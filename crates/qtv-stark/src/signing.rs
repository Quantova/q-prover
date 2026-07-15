//! The FIPS 204 signing derivation with a zero randomizer, arithmetized end to
//! end for one accepted iteration.
//!
//! Grinding resistance for the sortition draw does not come from checking that a
//! module lattice signature verifies. A hedged signature verifies just as well.
//! It comes from proving that the signature is the canonical one, the output of
//! the ML DSA 65 signing algorithm run with the per signature randomizer fixed at
//! zero. That is a proof over the signing computation, not the verification
//! relation, and it puts the secret key in the witness. This module arithmetizes
//! that signing computation for one accepted iteration of the rejection loop,
//! reusing the gadgets the prover already carries.
//!
//! The zero randomizer is load bearing and it is pinned here. The per message
//! seed of the signing loop is rho_pp = SHAKE256(K || rnd || mu), where K is the
//! secret signing seed, rnd is the per signature randomizer, and mu is the
//! message representative. The seed derivation is arithmetized on the sponge with
//! the rnd field of the absorbed block pinned to the thirty two zero bytes, so a
//! proof accepts only the derivation whose randomizer is zero. This is the one
//! constraint that separates option A from a bare verification proof.
//!
//! The computation an accepted iteration performs, all at the ML DSA 65 scale:
//!
//! - The masking expansion. From rho_pp and the loop counter kappa, ExpandMask
//!   squeezes SHAKE256 into the L mask polynomials. Reuses the sponge.
//! - The matrix product w = A y. The mask is transformed, multiplied pointwise by
//!   the expanded public matrix, and transformed back. Reuses the transform and
//!   the modular multiplication core, and the commitment high bits are recovered
//!   by the decomposition.
//! - The challenge. c_tilde = SHAKE256(mu || w1Encode(w1)) is absorbed over several
//!   blocks and SampleInBall turns it into the sparse challenge. Reuses the multi
//!   block absorb, the high bit packing, and the challenge ball sampler.
//! - The response z = y + c s1. The challenge is transformed, multiplied pointwise
//!   by the transformed secret, transformed back, and added to the mask. Reuses
//!   the transform and the modular multiplication core.
//! - The norm checks. The response infinity norm and the low bits r0 = LowBits(w -
//!   c s2) with its magnitude bound. Reuses the norm gadget and the decomposition.
//!
//! Each piece is arithmetized on its own description and proved on its own, the
//! same piece by piece method the batch verify relation is measured with. The
//! signing bench sizes each distinct piece to the work one iteration produces,
//! measures it once on the host, and composes the per iteration and per draw cost
//! from the exact structural multiplicities recorded here.

use crate::air::{Air, TraceTable};
use crate::lattice::{Q, RING_DEGREE};
use crate::{challenge_ball, decompose, encode, lattice, norm, ntt, sponge};

use qtv_crypto::sha3::shake256;

/// The ring degree of the signature, two hundred fifty six.
pub const N: usize = RING_DEGREE;

/// The public matrix rows for ML DSA 65.
pub const MATRIX_K: usize = lattice::MATRIX_ROWS;

/// The public matrix columns for ML DSA 65.
pub const MATRIX_L: usize = lattice::MATRIX_COLS;

/// The secret signing seed length in bytes.
pub const KEY_BYTES: usize = 32;

/// The per signature randomizer length in bytes. Fixed to zero for the
/// derandomized signing this proof binds.
pub const RANDOMIZER_BYTES: usize = 32;

/// The message representative length in bytes, the digest H(tr || m).
pub const MU_BYTES: usize = 64;

/// The number of transforms one accepted iteration runs at the ML DSA 65 scale.
/// The forward transform of the L mask polynomials and the one challenge
/// polynomial, and the inverse transform of the K matrix product rows, the L
/// response products, and the K low bit products.
pub const TRANSFORMS_PER_ITERATION: usize = MATRIX_L + 1 + MATRIX_K + MATRIX_L + MATRIX_K;

/// The number of pointwise modular products one accepted iteration runs. The
/// matrix product A y is K L N, the response product c s1 is L N, and the low bit
/// product c s2 is K N.
pub const POINTWISE_PER_ITERATION: usize = MATRIX_K * MATRIX_L * N + MATRIX_L * N + MATRIX_K * N;

/// The response coefficient count of one iteration, the L response polynomials.
pub const RESPONSE_COEFFS: usize = MATRIX_L * N;

/// The commitment coefficient count of one iteration, the K matrix product rows.
pub const COMMITMENT_COEFFS: usize = MATRIX_K * N;

/// The average number of signing loop iterations for the ML DSA 65 parameter set,
/// scaled by one thousand. The rejection loop repeats until the response and the
/// low bits pass their bounds; the expected repeat count for this parameter set is
/// about 5.1, so about 4.1 iterations are rejected before the accepted one.
pub const AVG_ITERATIONS_MILLI: u64 = 5100;

/// One arithmetized piece of the signing derivation, ready to prove and verify,
/// with the multiplicities that place it inside the signing loop.
pub struct Job {
    /// A short name for the piece.
    pub name: &'static str,
    /// The description the prover fills.
    pub prover: Air,
    /// The filled base trace.
    pub trace: TraceTable,
    /// The description the verifier rebuilds from the public inputs.
    pub verifier: Air,
    /// The low degree extension blow up the piece needs.
    pub blowup: usize,
    /// The number of query openings.
    pub queries: usize,
    /// How many times the piece runs inside one signing iteration.
    pub per_iteration: usize,
    /// How many times the piece runs once per draw, outside the loop.
    pub per_draw: usize,
    /// The trace row count.
    pub rows: usize,
    /// The base column count.
    pub columns: usize,
}

// A representative secret signing seed. The exact bytes do not change the shape
// or the cost of the derivation; only the trace size does.
fn key_seed() -> [u8; KEY_BYTES] {
    let mut key = [0u8; KEY_BYTES];
    for (i, b) in key.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(101).wrapping_add(7);
    }
    key
}

// A representative message representative mu.
fn message_representative() -> [u8; MU_BYTES] {
    let mut mu = [0u8; MU_BYTES];
    for (i, b) in mu.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(59).wrapping_add(3);
    }
    mu
}

/// The single block seed the loop derives, K joined with the zero randomizer and
/// the message representative. The randomizer field is the thirty two zero bytes
/// that make this the derandomized derivation.
pub fn seed_derivation_input() -> Vec<u8> {
    let key = key_seed();
    let mu = message_representative();
    let mut input = Vec::with_capacity(KEY_BYTES + RANDOMIZER_BYTES + MU_BYTES);
    input.extend_from_slice(&key);
    input.extend_from_slice(&[0u8; RANDOMIZER_BYTES]);
    input.extend_from_slice(&mu);
    input
}

/// The per message seed rho_pp = SHAKE256(K || 0 || mu, 64), the derived seed the
/// mask expansion runs on.
pub fn rho_pp() -> Vec<u8> {
    let mut out = vec![0u8; 64];
    shake256(&seed_derivation_input(), &mut out);
    out
}

// A deterministic reduced value sequence for the arithmetic bands, standing in
// for the reduced transform outputs and coefficients the real derivation carries.
fn reduced_sequence(count: usize, seed: u64) -> Vec<u64> {
    let mut state = seed | 1;
    (0..count)
        .map(|_| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state % Q
        })
        .collect()
}

fn reduced_pairs(count: usize, seed: u64) -> Vec<(u64, u64)> {
    let mut state = seed | 1;
    let mut draw = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state % Q
    };
    (0..count).map(|_| (draw(), draw())).collect()
}

/// The seed derivation piece. The sponge absorbs K, the zero randomizer, and mu,
/// and squeezes rho_pp, with the randomizer field pinned to zero by the input
/// block boundary. This is the piece that binds the zero randomizer.
pub fn seed_derivation_job() -> Job {
    let input = seed_derivation_input();
    // One permutation squeezes a full rate block, which covers the sixty four
    // byte seed the reference reads.
    let instance = sponge::shake_trace(sponge::SHAKE256_RATE, 1, &input);
    let verifier = sponge::shake_air(sponge::SHAKE256_RATE, 1, &input, &instance.output);
    let rows = instance.trace.length();
    let columns = instance.trace.width();
    Job {
        name: "seed derivation rho_pp, zero randomizer pinned",
        prover: instance.air,
        trace: instance.trace,
        verifier,
        blowup: 32,
        queries: 32,
        per_iteration: 0,
        per_draw: 1,
        rows,
        columns,
    }
}

/// The mask expansion piece for one mask polynomial. ExpandMask squeezes SHAKE256
/// over rho_pp joined with the two byte index into the mask coefficients; this is
/// the squeeze stream that feeds the unpacking.
pub fn mask_expansion_job() -> Job {
    let mut seed = rho_pp();
    // The two byte index of the first mask polynomial appended to rho_pp, as
    // ExpandMask forms it.
    seed.push(0);
    seed.push(0);
    // The mask coefficients are twenty bits each, so one polynomial reads six
    // hundred forty bytes, five SHAKE256 blocks, rounded to a power of two segment
    // count for the trace.
    let blocks = (N * 20 / 8).div_ceil(sponge::SHAKE256_RATE);
    let perms = blocks.next_power_of_two();
    let instance = sponge::shake_trace(sponge::SHAKE256_RATE, perms, &seed);
    let verifier = sponge::shake_air(sponge::SHAKE256_RATE, perms, &seed, &instance.output);
    let rows = instance.trace.length();
    let columns = instance.trace.width();
    Job {
        name: "mask expansion ExpandMask stream",
        prover: instance.air,
        trace: instance.trace,
        verifier,
        blowup: 32,
        queries: 32,
        per_iteration: MATRIX_L,
        per_draw: 0,
        rows,
        columns,
    }
}

/// One number theoretic transform of degree two hundred fifty six, the transform
/// the mask, the challenge, the matrix product, and the response all run on.
pub fn transform_job() -> Job {
    let coeffs = reduced_sequence(N, 0x5157_11a5);
    let instance = ntt::ntt_trace(&ntt::to_layer_zero(&coeffs));
    let verifier = ntt::ntt_air(N, &instance.input, &instance.output);
    let rows = instance.trace.length();
    let columns = instance.trace.width();
    Job {
        name: "number theoretic transform, degree 256",
        prover: instance.air,
        trace: instance.trace,
        verifier,
        blowup: 8,
        queries: 32,
        per_iteration: TRANSFORMS_PER_ITERATION,
        per_draw: 0,
        rows,
        columns,
    }
}

/// The transform domain pointwise products of one iteration in one batch, the
/// matrix product A y, the response product c s1, and the low bit product c s2,
/// each a coordinatewise modular multiplication over the signature modulus.
pub fn pointwise_products_job() -> Job {
    let inputs = reduced_pairs(POINTWISE_PER_ITERATION, 0x9e37_79b9);
    let batch = lattice::modmul_batch(&inputs);
    let length = batch.trace.length();
    let verifier = lattice::modmul_air(length);
    let columns = batch.trace.width();
    Job {
        name: "transform domain pointwise products, A y and c s1 and c s2",
        prover: batch.air,
        trace: batch.trace,
        verifier,
        blowup: 8,
        queries: 32,
        per_iteration: 1,
        per_draw: 0,
        rows: length,
        columns,
    }
}

/// The commitment high bits w1 = HighBits(w), one decomposition per matrix product
/// coefficient, the high part the challenge hash reads.
pub fn high_bits_job() -> Job {
    let coeffs = reduced_sequence(COMMITMENT_COEFFS, 0x00c0_ffee);
    let batch = decompose::decompose_batch(&coeffs);
    let length = batch.trace.length();
    let verifier = decompose::decompose_air(length);
    let columns = batch.trace.width();
    Job {
        name: "commitment high bits w1 = HighBits(w)",
        prover: batch.air,
        trace: batch.trace,
        verifier,
        blowup: 8,
        queries: 32,
        per_iteration: 1,
        per_draw: 0,
        rows: length,
        columns,
    }
}

/// The challenge hash absorb, SHAKE256 over mu joined with the w1 encoding. The
/// input runs to several blocks, so it is the multi block absorb.
pub fn challenge_absorb_job() -> Job {
    let mu = message_representative();
    // The commitment high bits packed two to a byte, w1Encode of the K matrix
    // rows, the encoded commitment the challenge hash absorbs.
    let highs: Vec<u8> = (0..COMMITMENT_COEFFS)
        .map(|i| (i as u8).wrapping_mul(7) & 0x0f)
        .collect();
    let w1 = encode::w1_encode(&highs);
    let mut input = Vec::with_capacity(mu.len() + w1.len());
    input.extend_from_slice(&mu);
    input.extend_from_slice(&w1);
    let instance = sponge::absorb_trace(sponge::SHAKE256_RATE, &input);
    let verifier = sponge::absorb_air(sponge::SHAKE256_RATE, &input, &instance.output);
    let rows = instance.trace.length();
    let columns = instance.trace.width();
    Job {
        name: "challenge hash absorb, mu joined with w1 encode",
        prover: instance.air,
        trace: instance.trace,
        verifier,
        blowup: 32,
        queries: 32,
        per_iteration: 1,
        per_draw: 0,
        rows,
        columns,
    }
}

/// The commitment high bit packing, w1Encode, folding two four bit high parts into
/// each byte of the challenge hash input.
pub fn w1_encode_job() -> Job {
    let highs: Vec<u8> = (0..COMMITMENT_COEFFS)
        .map(|i| (i as u8).wrapping_mul(7) & 0x0f)
        .collect();
    let batch = encode::encode_batch(&highs);
    let length = batch.trace.length();
    let verifier = encode::encode_air(length);
    let columns = batch.trace.width();
    Job {
        name: "commitment high bit packing w1Encode",
        prover: batch.air,
        trace: batch.trace,
        verifier,
        blowup: 8,
        queries: 32,
        per_iteration: 1,
        per_draw: 0,
        rows: length,
        columns,
    }
}

/// The challenge ball sampling, SampleInBall, turning the challenge squeeze into
/// the sparse plus or minus one challenge.
pub fn sample_in_ball_job() -> Job {
    let mut c_tilde = [0u8; 48];
    for (i, b) in c_tilde.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(53).wrapping_add(11);
    }
    let mut stream = vec![0u8; challenge_ball::BALL_BUFFER_BYTES];
    shake256(&c_tilde, &mut stream);
    let batch = challenge_ball::ball_batch(&stream);
    let length = batch.trace.length();
    let verifier = challenge_ball::ball_air(length);
    let columns = batch.trace.width();
    Job {
        name: "challenge ball sampling SampleInBall",
        prover: batch.air,
        trace: batch.trace,
        verifier,
        blowup: 8,
        queries: 32,
        per_iteration: 1,
        per_draw: 0,
        rows: length,
        columns,
    }
}

/// The response infinity norm, the check that every coefficient of z = y + c s1
/// sits within the bound gamma1 minus beta of zero.
pub fn response_norm_job() -> Job {
    let coeffs: Vec<u64> = (0..RESPONSE_COEFFS as u64)
        .map(|i| {
            let m = i.wrapping_mul(37) % norm::NORM_BOUND;
            if i % 2 == 0 {
                m
            } else {
                Q - m
            }
        })
        .collect();
    let batch = norm::norm_batch(&coeffs);
    let length = batch.trace.length();
    let verifier = norm::norm_air(length);
    let columns = batch.trace.width();
    Job {
        name: "response infinity norm on z",
        prover: batch.air,
        trace: batch.trace,
        verifier,
        blowup: 8,
        queries: 32,
        per_iteration: 1,
        per_draw: 0,
        rows: length,
        columns,
    }
}

/// The low bits r0 = LowBits(w - c s2), one decomposition per commitment
/// coefficient that extracts the centered low part the bound is taken on.
pub fn low_bits_job() -> Job {
    let coeffs = reduced_sequence(COMMITMENT_COEFFS, 0x1234_5678);
    let batch = decompose::decompose_batch(&coeffs);
    let length = batch.trace.length();
    let verifier = decompose::decompose_air(length);
    let columns = batch.trace.width();
    Job {
        name: "low bits r0 = LowBits(w - c s2)",
        prover: batch.air,
        trace: batch.trace,
        verifier,
        blowup: 8,
        queries: 32,
        per_iteration: 1,
        per_draw: 0,
        rows: length,
        columns,
    }
}

/// The low bits magnitude bound, the check that the centered low part r0 sits
/// within its bound of zero. It reuses the norm gadget shape; the reference bound
/// is gamma2 minus beta rather than the response bound gamma1 minus beta, the same
/// two sided range on a tighter constant.
pub fn low_bits_norm_job() -> Job {
    let coeffs: Vec<u64> = (0..COMMITMENT_COEFFS as u64)
        .map(|i| {
            let m = i.wrapping_mul(29) % (decompose::GAMMA2 - norm::BETA);
            if i % 2 == 0 {
                m
            } else {
                Q - m
            }
        })
        .collect();
    let batch = norm::norm_batch(&coeffs);
    let length = batch.trace.length();
    let verifier = norm::norm_air(length);
    let columns = batch.trace.width();
    Job {
        name: "low bits magnitude bound on r0",
        prover: batch.air,
        trace: batch.trace,
        verifier,
        blowup: 8,
        queries: 32,
        per_iteration: 1,
        per_draw: 0,
        rows: length,
        columns,
    }
}

/// Every distinct arithmetized piece of the signing derivation, each carrying the
/// multiplicities that place it inside the signing loop. The bench measures each
/// once and composes the per iteration and per draw cost from the multiplicities.
pub fn signing_jobs() -> Vec<Job> {
    vec![
        seed_derivation_job(),
        mask_expansion_job(),
        transform_job(),
        pointwise_products_job(),
        high_bits_job(),
        challenge_absorb_job(),
        w1_encode_job(),
        sample_in_ball_job(),
        response_norm_job(),
        low_bits_job(),
        low_bits_norm_job(),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::Felt;
    use crate::stark::{prove, verify, StarkParams};

    #[test]
    fn the_seed_derivation_pins_the_zero_randomizer() {
        let input = seed_derivation_input();
        assert_eq!(input.len(), KEY_BYTES + RANDOMIZER_BYTES + MU_BYTES);
        // The randomizer field is the thirty two zero bytes between the key and
        // the message representative.
        assert!(input[KEY_BYTES..KEY_BYTES + RANDOMIZER_BYTES]
            .iter()
            .all(|b| *b == 0));
    }

    #[test]
    fn the_rho_pp_matches_the_crypto_shake256() {
        let ours = rho_pp();
        let mut expected = vec![0u8; 64];
        shake256(&seed_derivation_input(), &mut expected);
        assert_eq!(ours, expected);
    }

    #[test]
    fn the_multiplicities_match_the_parameter_set() {
        // Twenty three transforms and ten thousand four hundred ninety six
        // pointwise products per iteration.
        assert_eq!(TRANSFORMS_PER_ITERATION, 23);
        assert_eq!(POINTWISE_PER_ITERATION, 10496);
        assert_eq!(RESPONSE_COEFFS, 1280);
        assert_eq!(COMMITMENT_COEFFS, 1536);
    }

    #[test]
    fn every_job_arithmetic_holds() {
        // The permutation carrying pieces are checked under fixed challenges; the
        // rest hold on the base trace directly.
        let challenges = [Felt::new(0x1234_5678), Felt::new(0x9abc_def0)];
        for job in signing_jobs() {
            let ok = if job.prover.num_challenges() == 0 {
                job.prover.is_satisfied(&job.trace)
            } else {
                job.prover
                    .is_satisfied_with(&job.trace, &challenges[..job.prover.num_challenges()])
            };
            assert!(ok, "arithmetic failed for {}", job.name);
        }
    }

    #[test]
    fn the_job_set_covers_the_iteration_and_the_draw() {
        let jobs = signing_jobs();
        let per_draw: usize = jobs.iter().map(|j| j.per_draw).sum();
        // Exactly one piece runs once per draw outside the loop, the seed
        // derivation.
        assert_eq!(per_draw, 1);
        // The transform and the mask expansion carry the loop multiplicities.
        let transforms = jobs
            .iter()
            .find(|j| j.name.starts_with("number theoretic"))
            .unwrap();
        assert_eq!(transforms.per_iteration, 23);
        let mask = jobs
            .iter()
            .find(|j| j.name.starts_with("mask expansion"))
            .unwrap();
        assert_eq!(mask.per_iteration, MATRIX_L);
    }

    // A small proof over the cheapest piece confirms the job descriptions prove
    // and verify through the protocol, not only that the arithmetic holds.
    #[test]
    fn a_representative_job_proves_and_verifies() {
        let job = sample_in_ball_job();
        let params = StarkParams {
            lde_blowup: job.blowup,
            num_queries: job.queries,
        };
        let proof = prove(&job.prover, &job.trace, &params);
        assert!(verify(&job.verifier, &params, &proof));
    }
}
