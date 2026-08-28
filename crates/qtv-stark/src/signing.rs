// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::air::{Air, TraceTable};
use crate::lattice::{Q, RING_DEGREE};
use crate::{challenge_ball, decompose, encode, lattice, norm, ntt, sponge};

use qtv_crypto::sha3::shake256;

pub const N: usize = RING_DEGREE;

pub const MATRIX_K: usize = lattice::MATRIX_ROWS;

pub const MATRIX_L: usize = lattice::MATRIX_COLS;

pub const KEY_BYTES: usize = 32;

pub const RANDOMIZER_BYTES: usize = 32;

pub const MU_BYTES: usize = 64;

pub const TRANSFORMS_PER_ITERATION: usize = MATRIX_L + 1 + MATRIX_K + MATRIX_L + MATRIX_K;

pub const POINTWISE_PER_ITERATION: usize = MATRIX_K * MATRIX_L * N + MATRIX_L * N + MATRIX_K * N;

pub const RESPONSE_COEFFS: usize = MATRIX_L * N;

pub const COMMITMENT_COEFFS: usize = MATRIX_K * N;

pub const AVG_ITERATIONS_MILLI: u64 = 5100;

pub struct Job {
    pub name: &'static str,
    pub prover: Air,
    pub trace: TraceTable,
    pub verifier: Air,
    pub blowup: usize,
    pub queries: usize,
    pub per_iteration: usize,
    pub per_draw: usize,
    pub rows: usize,
    pub columns: usize,
}

fn key_seed() -> [u8; KEY_BYTES] {
    let mut key = [0u8; KEY_BYTES];
    for (i, b) in key.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(101).wrapping_add(7);
    }
    key
}

fn message_representative() -> [u8; MU_BYTES] {
    let mut mu = [0u8; MU_BYTES];
    for (i, b) in mu.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(59).wrapping_add(3);
    }
    mu
}

pub fn seed_derivation_input() -> Vec<u8> {
    let key = key_seed();
    let mu = message_representative();
    let mut input = Vec::with_capacity(KEY_BYTES + RANDOMIZER_BYTES + MU_BYTES);
    input.extend_from_slice(&key);
    input.extend_from_slice(&[0u8; RANDOMIZER_BYTES]);
    input.extend_from_slice(&mu);
    input
}

pub fn rho_pp() -> Vec<u8> {
    let mut out = vec![0u8; 64];
    shake256(&seed_derivation_input(), &mut out);
    out
}

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

pub fn seed_derivation_job() -> Job {
    let input = seed_derivation_input();
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

pub fn mask_expansion_job() -> Job {
    let mut seed = rho_pp();
    seed.push(0);
    seed.push(0);
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

pub fn transform_job() -> Job {
    let coeffs = reduced_sequence(N, 1364660645);
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

pub fn pointwise_products_job() -> Job {
    let inputs = reduced_pairs(POINTWISE_PER_ITERATION, 2654435769);
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

pub fn high_bits_job() -> Job {
    let coeffs = reduced_sequence(COMMITMENT_COEFFS, 12648430);
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

pub fn challenge_absorb_job() -> Job {
    let mu = message_representative();
    let highs: Vec<u8> = (0..COMMITMENT_COEFFS)
        .map(|i| (i as u8).wrapping_mul(7) & 15)
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

pub fn w1_encode_job() -> Job {
    let highs: Vec<u8> = (0..COMMITMENT_COEFFS)
        .map(|i| (i as u8).wrapping_mul(7) & 15)
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

pub fn low_bits_job() -> Job {
    let coeffs = reduced_sequence(COMMITMENT_COEFFS, 305419896);
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
    use crate::field_ext::Fp3;
    use crate::stark::{prove, verify, StarkParams};

    #[test]
    fn the_seed_derivation_pins_the_zero_randomizer() {
        let input = seed_derivation_input();
        assert_eq!(input.len(), KEY_BYTES + RANDOMIZER_BYTES + MU_BYTES);
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
        assert_eq!(TRANSFORMS_PER_ITERATION, 23);
        assert_eq!(POINTWISE_PER_ITERATION, 10496);
        assert_eq!(RESPONSE_COEFFS, 1280);
        assert_eq!(COMMITMENT_COEFFS, 1536);
    }

    #[test]
    fn every_job_arithmetic_holds() {
        let challenges = [Fp3::new(Felt::new(305419896), Felt::new(11), Felt::new(97)), Fp3::new(Felt::new(2596069104), Felt::new(23), Felt::new(131))];
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
        assert_eq!(per_draw, 1);
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
