// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::air::{Air, TraceTable};
use crate::field::Felt;
use crate::lattice::{Q, RESIDUE_BITS, RING_DEGREE};

pub const CANDIDATE_BYTES: usize = 3;

pub const REJ_BUFFER_BYTES: usize = crate::sponge::SHAKE128_RATE * 6;

pub const CANDIDATES: usize = REJ_BUFFER_BYTES / CANDIDATE_BYTES;

const COL_B0: usize = 0;
const COL_B1: usize = 1;
const COL_B2: usize = 2;
const COL_B2M: usize = 3;
const COL_BIT7: usize = 4;
const COL_Z: usize = 5;
const COL_ACC: usize = 6;
const COL_SUB: usize = 7;
const COL_OVER: usize = 8;
const COL_B0_BITS: usize = 9;
const COL_B1_BITS: usize = COL_B0_BITS + 8;
const COL_B2M_BITS: usize = COL_B1_BITS + 8;
const COL_SUB_BITS: usize = COL_B2M_BITS + 7;
const COL_OVER_BITS: usize = COL_SUB_BITS + RESIDUE_BITS;

pub const WIDTH: usize = COL_OVER_BITS + RESIDUE_BITS;

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

pub fn candidate(b0: u8, b1: u8, b2: u8) -> u32 {
    (b0 as u32) | ((b1 as u32) << 8) | (((b2 & 127) as u32) << 16)
}

pub fn rej_sample(stream: &[u8]) -> Vec<u64> {
    let mut out = Vec::with_capacity(RING_DEGREE);
    let mut pos = 0usize;
    while out.len() < RING_DEGREE && pos + CANDIDATE_BYTES <= stream.len() {
        let z = candidate(stream[pos], stream[pos + 1], stream[pos + 2]);
        pos += CANDIDATE_BYTES;
        if (z as u64) < Q {
            out.push(z as u64);
        }
    }
    out
}

pub fn add_constraints(air: &mut Air, base: usize) {
    let modulus = Felt::new(Q);
    let modulus_minus_one = Felt::new(Q - 1);
    let byte_hi = Felt::new(256);
    let word_hi = Felt::new(1 << 16);
    let top = Felt::new(128);
    let b0 = base + COL_B0;
    let b1 = base + COL_B1;
    let b2 = base + COL_B2;
    let b2m = base + COL_B2M;
    let bit7 = base + COL_BIT7;
    let z = base + COL_Z;
    let acc = base + COL_ACC;
    let sub = base + COL_SUB;
    let over = base + COL_OVER;

    air.add_single_row(1, move |row| {
        recompose(row, base + COL_B0_BITS, 8).sub(row[b0])
    });
    air.add_single_row(1, move |row| {
        recompose(row, base + COL_B1_BITS, 8).sub(row[b1])
    });
    air.add_single_row(1, move |row| {
        recompose(row, base + COL_B2M_BITS, 7).sub(row[b2m])
    });

    air.add_single_row(2, move |row| row[bit7].mul(row[bit7].sub(Felt::ONE)));
    air.add_single_row(1, move |row| row[b2].sub(row[b2m]).sub(row[bit7].mul(top)));

    air.add_single_row(1, move |row| {
        row[z]
            .sub(row[b0])
            .sub(row[b1].mul(byte_hi))
            .sub(row[b2m].mul(word_hi))
    });

    air.add_single_row(2, move |row| row[acc].mul(row[acc].sub(Felt::ONE)));

    air.add_single_row(1, move |row| {
        recompose(row, base + COL_SUB_BITS, RESIDUE_BITS).sub(row[sub])
    });
    air.add_single_row(2, move |row| {
        row[acc].mul(row[sub].sub(modulus_minus_one.sub(row[z])))
    });

    air.add_single_row(1, move |row| {
        recompose(row, base + COL_OVER_BITS, RESIDUE_BITS).sub(row[over])
    });
    air.add_single_row(2, move |row| {
        Felt::ONE
            .sub(row[acc])
            .mul(row[over].sub(row[z].sub(modulus)))
    });

    for start in [COL_B0_BITS, COL_B1_BITS] {
        for k in 0..8 {
            let col = base + start + k;
            air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
        }
    }
    for k in 0..7 {
        let col = base + COL_B2M_BITS + k;
        air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
    }
    for start in [COL_SUB_BITS, COL_OVER_BITS] {
        for k in 0..RESIDUE_BITS {
            let col = base + start + k;
            air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
        }
    }
}

pub fn rej_air(length: usize) -> Air {
    let mut air = Air::new(WIDTH, length);
    add_constraints(&mut air, 0);
    air
}

fn set_bits(trace: &mut TraceTable, col: usize, row: usize, value: u64, bits: usize) {
    for k in 0..bits {
        trace.set(col + k, row, Felt::new((value >> k) & 1));
    }
}

pub fn fill_row(trace: &mut TraceTable, base: usize, row: usize, b0: u8, b1: u8, b2: u8) {
    let b2m = (b2 & 127) as u64;
    let bit7 = (b2 >> 7) as u64;
    let z = candidate(b0, b1, b2) as u64;
    let acc = if z < Q { 1u64 } else { 0 };
    let sub = if acc == 1 { Q - 1 - z } else { 0 };
    let over = if acc == 0 { z.wrapping_sub(Q) } else { 0 };

    trace.set(base + COL_B0, row, Felt::new(b0 as u64));
    trace.set(base + COL_B1, row, Felt::new(b1 as u64));
    trace.set(base + COL_B2, row, Felt::new(b2 as u64));
    trace.set(base + COL_B2M, row, Felt::new(b2m));
    trace.set(base + COL_BIT7, row, Felt::new(bit7));
    trace.set(base + COL_Z, row, Felt::new(z));
    trace.set(base + COL_ACC, row, Felt::new(acc));
    trace.set(base + COL_SUB, row, Felt::new(sub));
    trace.set(base + COL_OVER, row, Felt::new(over));
    set_bits(trace, base + COL_B0_BITS, row, b0 as u64, 8);
    set_bits(trace, base + COL_B1_BITS, row, b1 as u64, 8);
    set_bits(trace, base + COL_B2M_BITS, row, b2m, 7);
    set_bits(trace, base + COL_SUB_BITS, row, sub, RESIDUE_BITS);
    set_bits(trace, base + COL_OVER_BITS, row, over, RESIDUE_BITS);
}

pub struct RejBatch {
    pub air: Air,
    pub trace: TraceTable,
    pub coefficients: Vec<u64>,
}

pub const ACCEPT_COL: usize = COL_ACC;

pub const CANDIDATE_COL: usize = COL_Z;

pub fn rej_batch(stream: &[u8]) -> RejBatch {
    let candidates = (stream.len() / CANDIDATE_BYTES).min(CANDIDATES);
    let length = candidates.next_power_of_two().max(2);
    let mut trace = TraceTable::new(WIDTH, length);
    for row in 0..length {
        let (b0, b1, b2) = if row < candidates {
            let p = row * CANDIDATE_BYTES;
            (stream[p], stream[p + 1], stream[p + 2])
        } else {
            (0, 0, 0)
        };
        fill_row(&mut trace, 0, row, b0, b1, b2);
    }
    RejBatch {
        air: rej_air(length),
        trace,
        coefficients: rej_sample(stream),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hashing::matrix_entry_seed;
    use crate::stark::{prove, verify, StarkParams};
    use qtv_crypto::sha3::shake128;

    fn params() -> StarkParams {
        StarkParams {
            lde_blowup: 8,
            num_queries: 24,
        }
    }

    fn sample_stream() -> Vec<u8> {
        let mut rho = [0u8; 32];
        for (i, b) in rho.iter_mut().enumerate() {
            *b = (i as u8).wrapping_mul(37).wrapping_add(1);
        }
        let seed = matrix_entry_seed(&rho, 3, 2);
        let mut stream = vec![0u8; REJ_BUFFER_BYTES];
        shake128(&seed, &mut stream);
        stream
    }

    #[test]
    fn the_sample_produces_a_full_ring_below_the_modulus() {
        let stream = sample_stream();
        let coeffs = rej_sample(&stream);
        assert_eq!(coeffs.len(), RING_DEGREE);
        for c in &coeffs {
            assert!(*c < Q);
        }
    }

    #[test]
    fn the_accept_bits_match_the_candidate_comparison() {
        let stream = sample_stream();
        let batch = rej_batch(&stream);
        let candidates = (stream.len() / CANDIDATE_BYTES).min(CANDIDATES);
        for row in 0..candidates {
            let p = row * CANDIDATE_BYTES;
            let z = candidate(stream[p], stream[p + 1], stream[p + 2]) as u64;
            let acc = batch.trace.get(ACCEPT_COL, row).to_u64();
            assert_eq!(acc, u64::from(z < Q));
        }
    }

    #[test]
    fn the_arithmetic_holds_on_every_row() {
        let batch = rej_batch(&sample_stream());
        assert!(batch.air.is_satisfied(&batch.trace));
    }

    #[test]
    fn a_flipped_accept_bit_is_rejected() {
        let batch = rej_batch(&sample_stream());
        let mut trace = batch.trace;
        let mut target = 0;
        for row in 0..trace.length() {
            if trace.get(ACCEPT_COL, row) == Felt::ONE {
                target = row;
                break;
            }
        }
        trace.set(ACCEPT_COL, target, Felt::ZERO);
        assert!(!batch.air.is_satisfied(&trace));
    }

    #[test]
    fn a_tampered_candidate_byte_is_rejected() {
        let batch = rej_batch(&sample_stream());
        let mut trace = batch.trace;
        trace.set(COL_B0, 1, trace.get(COL_B0, 1).add(Felt::ONE));
        assert!(!batch.air.is_satisfied(&trace));
    }

    #[test]
    fn a_batch_proves_and_verifies() {
        let batch = rej_batch(&sample_stream());
        let proof = prove(&batch.air, &batch.trace, &params());
        assert!(verify(&rej_air(batch.trace.length()), &params(), &proof));
    }
}
