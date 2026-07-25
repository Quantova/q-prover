// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT


use crate::air::{Air, TraceTable};
use crate::field::Felt;
use crate::lattice::RING_DEGREE;

pub const TAU: usize = 49;

pub const START: usize = RING_DEGREE - TAU;

pub const SIGN_BYTES: usize = 8;

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

pub const WIDTH: usize = COL_GT_BITS + 8;

pub const ACCEPT_COL: usize = COL_ACC;

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

pub fn sign_word(stream: &[u8]) -> u64 {
    let mut signs = 0u64;
    for i in 0..SIGN_BYTES {
        signs |= (stream[i] as u64) << (8 * i);
    }
    signs
}

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

pub fn add_constraints(air: &mut Air, base: usize) {
    let degree = Felt::new(RING_DEGREE as u64);
    let j = base + COL_J;
    let i = base + COL_I;
    let acc = base + COL_ACC;
    let done = base + COL_DONE;
    let dinv = base + COL_DINV;
    let le = base + COL_LE;
    let gt = base + COL_GT;

    air.add_single_row(2, move |row| row[acc].mul(row[acc].sub(Felt::ONE)));
    air.add_single_row(2, move |row| row[done].mul(row[done].sub(Felt::ONE)));
    air.add_single_row(2, move |row| row[done].mul(row[acc]));

    air.add_single_row(2, move |row| row[done].mul(row[i].sub(degree)));
    air.add_single_row(3, move |row| {
        Felt::ONE
            .sub(row[done])
            .mul(row[i].sub(degree).mul(row[dinv]).sub(Felt::ONE))
    });

    air.add_single_row(1, move |row| {
        recompose(row, base + COL_LE_BITS, 8).sub(row[le])
    });
    air.add_single_row(2, move |row| row[acc].mul(row[le].sub(row[i].sub(row[j]))));

    air.add_single_row(1, move |row| {
        recompose(row, base + COL_GT_BITS, 8).sub(row[gt])
    });
    air.add_single_row(3, move |row| {
        Felt::ONE
            .sub(row[acc])
            .mul(Felt::ONE.sub(row[done]))
            .mul(row[gt].sub(row[j].sub(row[i]).sub(Felt::ONE)))
    });

    air.add_transition(1, move |current, next| {
        next[i].sub(current[i]).sub(current[acc])
    });

    for start in [COL_LE_BITS, COL_GT_BITS] {
        for k in 0..8 {
            let col = base + start + k;
            air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
        }
    }
}

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

pub struct BallBatch {
    pub air: Air,
    pub trace: TraceTable,
    pub challenge: Vec<i64>,
}

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
