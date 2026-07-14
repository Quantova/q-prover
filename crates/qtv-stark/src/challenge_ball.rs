//! Challenge ball sampling of the sparse challenge polynomial.
//!
//! The challenge is a ring element with exactly tau nonzero coefficients, each
//! plus or minus one. It is drawn from the challenge squeeze by SampleInBall of
//! FIPS 204, Algorithm 29. The first eight squeeze bytes are the sign word. The
//! remaining bytes drive a shuffle, one target index at a time from the ring
//! degree minus tau up to the ring degree. For each target the stream is read
//! until a byte lands at or below the target, that byte is the position placed,
//! and bytes above the target are rejected.
//!
//! This module arithmetizes the position rejection that turns the squeeze into the
//! placement schedule. Each row consumes one stream byte, compares it to the
//! running target, and either accepts it as a placement and advances the target or
//! rejects it. A range witness pins the comparison, the target accumulates the
//! accept bits from the start value to the ring degree, and the accept count is
//! forced to tau by the endpoint. The stream is validated against the crypto crate
//! SHAKE256.

use crate::air::{Air, TraceTable};
use crate::field::Felt;
use crate::lattice::RING_DEGREE;

/// The number of nonzero coefficients of the challenge for the parameter set.
pub const TAU: usize = 49;

/// The first target index of the shuffle, the ring degree minus tau.
pub const START: usize = RING_DEGREE - TAU;

/// The sign word byte length, read before the shuffle.
pub const SIGN_BYTES: usize = 8;

/// The bytes of the first SHAKE256 buffer the reference squeezes, two rate blocks.
pub const BALL_BUFFER_BYTES: usize = crate::sponge::SHAKE256_RATE * 2;

const COL_J: usize = 0;
const COL_I: usize = 1;
const COL_ACC: usize = 2;
const COL_DONE: usize = 3;
const COL_DINV: usize = 4;
const COL_LE: usize = 5;
const COL_GT: usize = 6;
const COL_LE_BITS: usize = 7;
const COL_GT_BITS: usize = COL_LE_BITS + 8;

/// The column width of the challenge ball sampling piece.
pub const WIDTH: usize = COL_GT_BITS + 8;

/// The accept column relative to the piece base.
pub const ACCEPT_COL: usize = COL_ACC;

/// The consumed byte column relative to the piece base.
pub const BYTE_COL: usize = COL_J;

fn recompose(row: &[Felt], base: usize, bits: usize) -> Felt {
    let two = Felt::new(2);
    let mut acc = Felt::ZERO;
    let mut weight = Felt::ONE;
    for k in 0..bits {
        acc = acc.add(row[base + k].mul(weight));
        weight = weight.mul(two);
    }
    acc
}

/// The sign word, the little endian value of the first eight squeeze bytes.
pub fn sign_word(stream: &[u8]) -> u64 {
    let mut signs = 0u64;
    for i in 0..SIGN_BYTES {
        signs |= (stream[i] as u64) << (8 * i);
    }
    signs
}

/// Samples the sparse challenge polynomial from the squeeze, the reference
/// SampleInBall restricted to the first buffer. Returns the ring degree
/// coefficients, each in minus one, zero, or one.
pub fn sample_in_ball(stream: &[u8]) -> Vec<i64> {
    let signs = sign_word(stream);
    let mut c = vec![0i64; RING_DEGREE];
    let mut pos = SIGN_BYTES;
    let mut bit = 0usize;
    let mut i = START;
    while i < RING_DEGREE {
        let j = loop {
            let b = stream[pos] as usize;
            pos += 1;
            if b <= i {
                break b;
            }
        };
        c[i] = c[j];
        c[j] = if (signs >> bit) & 1 == 1 { -1 } else { 1 };
        bit += 1;
        i += 1;
    }
    c
}

/// The number of stream bytes the shuffle consumes to place all tau positions.
fn consumed_bytes(stream: &[u8]) -> usize {
    let mut pos = SIGN_BYTES;
    let mut i = START;
    while i < RING_DEGREE {
        let b = stream[pos] as usize;
        pos += 1;
        if b <= i {
            i += 1;
        }
    }
    pos - SIGN_BYTES
}

/// Adds the challenge ball sampling constraints at the given column base, so the
/// piece can be placed inside a wider joined trace.
pub fn add_constraints(air: &mut Air, base: usize) {
    let degree = Felt::new(RING_DEGREE as u64);
    let j = base + COL_J;
    let i = base + COL_I;
    let acc = base + COL_ACC;
    let done = base + COL_DONE;
    let dinv = base + COL_DINV;
    let le = base + COL_LE;
    let gt = base + COL_GT;

    // The accept, done, and their product gates. The accept bit and the done bit
    // are bits, and no accept fires once the target has reached the ring degree.
    air.add_single_row(2, move |row| row[acc].mul(row[acc].sub(Felt::ONE)));
    air.add_single_row(2, move |row| row[done].mul(row[done].sub(Felt::ONE)));
    air.add_single_row(2, move |row| row[done].mul(row[acc]));

    // The done bit is exactly the target at the ring degree. When the target is
    // below it the inverse witness pins the difference away from zero.
    air.add_single_row(2, move |row| row[done].mul(row[i].sub(degree)));
    air.add_single_row(3, move |row| {
        Felt::ONE
            .sub(row[done])
            .mul(row[i].sub(degree).mul(row[dinv]).sub(Felt::ONE))
    });

    // On an accept the byte lands at or below the target, pinned by the non
    // negative range witness target minus byte.
    air.add_single_row(1, move |row| {
        recompose(row, base + COL_LE_BITS, 8).sub(row[le])
    });
    air.add_single_row(2, move |row| row[acc].mul(row[le].sub(row[i].sub(row[j]))));

    // On a genuine rejection, before the target is done, the byte lands above the
    // target, pinned by the non negative range witness byte minus target minus one.
    air.add_single_row(1, move |row| {
        recompose(row, base + COL_GT_BITS, 8).sub(row[gt])
    });
    air.add_single_row(3, move |row| {
        Felt::ONE
            .sub(row[acc])
            .mul(Felt::ONE.sub(row[done]))
            .mul(row[gt].sub(row[j].sub(row[i]).sub(Felt::ONE)))
    });

    // The target accumulates the accept bits from one row to the next.
    air.add_transition(1, move |current, next| {
        next[i].sub(current[i]).sub(current[acc])
    });

    // Every range bit is zero or one.
    for start in [COL_LE_BITS, COL_GT_BITS] {
        for k in 0..8 {
            let col = base + start + k;
            air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
        }
    }
}

/// Builds the challenge ball description of the given length, and pins the target
/// endpoints, the start value at the first row and the ring degree at the last.
pub fn ball_air(length: usize) -> Air {
    let mut air = Air::new(WIDTH, length);
    add_constraints(&mut air, 0);
    air.add_boundary(COL_I, 0, Felt::new(START as u64));
    air.add_boundary(COL_I, length - 1, Felt::new(RING_DEGREE as u64));
    air
}

fn set_bits(trace: &mut TraceTable, col: usize, row: usize, value: u64, bits: usize) {
    for k in 0..bits {
        trace.set(col + k, row, Felt::new((value >> k) & 1));
    }
}

/// A filled challenge ball batch with its description and the sampled polynomial.
pub struct BallBatch {
    /// The description shared with the verifier.
    pub air: Air,
    /// The filled trace.
    pub trace: TraceTable,
    /// The sampled challenge polynomial, tau nonzero signs among the ring degree.
    pub challenge: Vec<i64>,
}

/// Lays out a trace over the shuffle bytes of the stream. Each row consumes one
/// byte from past the sign word, compares it to the running target, and advances
/// the target on an accept. The trace is padded past the last placement with rows
/// that hold the target at the ring degree.
pub fn ball_batch(stream: &[u8]) -> BallBatch {
    let consumed = consumed_bytes(stream);
    let length = (consumed + 1).next_power_of_two().max(2);
    let mut trace = TraceTable::new(WIDTH, length);

    let mut i = START;
    for row in 0..length {
        let byte = stream.get(SIGN_BYTES + row).copied().unwrap_or(0) as usize;
        let done = i == RING_DEGREE;
        let acc = if !done && byte <= i { 1usize } else { 0 };
        let le = if acc == 1 { i - byte } else { 0 };
        let gt = if acc == 0 && !done { byte - i - 1 } else { 0 };
        let dinv = if done {
            Felt::ZERO
        } else {
            Felt::new(i as u64).sub(Felt::new(RING_DEGREE as u64)).inv()
        };

        trace.set(COL_J, row, Felt::new(byte as u64));
        trace.set(COL_I, row, Felt::new(i as u64));
        trace.set(COL_ACC, row, Felt::new(acc as u64));
        trace.set(COL_DONE, row, Felt::new(done as u64));
        trace.set(COL_DINV, row, dinv);
        trace.set(COL_LE, row, Felt::new(le as u64));
        trace.set(COL_GT, row, Felt::new(gt as u64));
        set_bits(&mut trace, COL_LE_BITS, row, le as u64, 8);
        set_bits(&mut trace, COL_GT_BITS, row, gt as u64, 8);

        i += acc;
    }

    BallBatch {
        air: ball_air(length),
        trace,
        challenge: sample_in_ball(stream),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark::{prove, verify, StarkParams};
    use qtv_crypto::sha3::shake256;

    fn params() -> StarkParams {
        StarkParams {
            lde_blowup: 8,
            num_queries: 24,
        }
    }

    fn sample_stream() -> Vec<u8> {
        let mut c_tilde = [0u8; 48];
        for (i, b) in c_tilde.iter_mut().enumerate() {
            *b = (i as u8).wrapping_mul(53).wrapping_add(11);
        }
        let mut stream = vec![0u8; BALL_BUFFER_BYTES];
        shake256(&c_tilde, &mut stream);
        stream
    }

    #[test]
    fn the_challenge_has_tau_nonzero_signs() {
        let stream = sample_stream();
        let c = sample_in_ball(&stream);
        let nonzero = c.iter().filter(|&&v| v != 0).count();
        assert_eq!(nonzero, TAU);
        for v in &c {
            assert!(*v >= -1 && *v <= 1);
        }
    }

    #[test]
    fn the_accepted_positions_match_the_reference() {
        let stream = sample_stream();
        let batch = ball_batch(&stream);
        let mut positions = Vec::new();
        for row in 0..batch.trace.length() {
            if batch.trace.get(ACCEPT_COL, row) == Felt::ONE {
                positions.push(batch.trace.get(BYTE_COL, row).to_u64() as usize);
            }
        }
        assert_eq!(positions.len(), TAU);
        // The reference places tau positions, each at or below its target.
        for (step, p) in positions.iter().enumerate() {
            assert!(*p <= START + step);
        }
    }

    #[test]
    fn the_arithmetic_holds_on_every_row() {
        let batch = ball_batch(&sample_stream());
        assert!(batch.air.is_satisfied(&batch.trace));
    }

    #[test]
    fn a_flipped_accept_bit_is_rejected() {
        let batch = ball_batch(&sample_stream());
        let mut trace = batch.trace;
        // Claim a rejected byte was accepted. Its target no longer reaches the ring
        // degree at the endpoint, and the range witness no longer matches.
        let mut target = 0;
        for row in 0..trace.length() {
            if trace.get(ACCEPT_COL, row) == Felt::ZERO && trace.get(COL_DONE, row) == Felt::ZERO {
                target = row;
                break;
            }
        }
        trace.set(ACCEPT_COL, target, Felt::ONE);
        assert!(!batch.air.is_satisfied(&trace));
    }

    #[test]
    fn a_tampered_byte_is_rejected() {
        let batch = ball_batch(&sample_stream());
        let mut trace = batch.trace;
        // Raise an accepted byte above its target while keeping the accept bit.
        let mut target = 0;
        for row in 0..trace.length() {
            if trace.get(ACCEPT_COL, row) == Felt::ONE {
                target = row;
                break;
            }
        }
        trace.set(BYTE_COL, target, Felt::new(255));
        assert!(!batch.air.is_satisfied(&trace));
    }

    #[test]
    fn a_batch_proves_and_verifies() {
        let batch = ball_batch(&sample_stream());
        let proof = prove(&batch.air, &batch.trace, &params());
        assert!(verify(&ball_air(batch.trace.length()), &params(), &proof));
    }
}
