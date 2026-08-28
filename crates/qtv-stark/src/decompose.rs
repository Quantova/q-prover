// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::air::{Air, TraceTable};
use crate::field::Felt;
use crate::lattice::Q;

pub const GAMMA2: u64 = (Q - 1) / 32;

pub const ALPHA: u64 = 2 * GAMMA2;

pub const HIGH_COUNT: u64 = (Q - 1) / ALPHA;

pub const HIGH_BITS: usize = 4;

pub const LOW_BITS: usize = 20;

pub const COL_R: usize = 0;
const COL_R1: usize = 1;
const COL_R0S: usize = 2;
const COL_KC: usize = 3;
const COL_R0S_INV: usize = 4;
const COL_R1_BITS: usize = 5;
const COL_R0S_BITS: usize = COL_R1_BITS + HIGH_BITS;
const COL_R0S_SLACK: usize = COL_R0S_BITS + LOW_BITS;

pub const WIDTH: usize = COL_R0S_SLACK + LOW_BITS;

const LOW_SHIFT: u64 = GAMMA2;

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

pub fn add_constraints(air: &mut Air, base: usize) {
    let alpha = Felt::new(ALPHA);
    let modulus = Felt::new(Q);
    let low_shift = Felt::new(LOW_SHIFT);
    let low_bound = Felt::new(ALPHA);
    let r = base + COL_R;
    let r1 = base + COL_R1;
    let r0s = base + COL_R0S;
    let kc = base + COL_KC;
    let r0s_inv = base + COL_R0S_INV;

    air.add_single_row(1, move |row| {
        row[r]
            .sub(row[r1].mul(alpha))
            .sub(row[r0s].sub(low_shift))
            .sub(row[kc].mul(modulus))
    });

    air.add_single_row(2, move |row| row[kc].mul(row[kc].sub(Felt::ONE)));

    air.add_single_row(2, move |row| row[kc].mul(row[r1]));

    air.add_single_row(3, move |row| {
        Felt::ONE
            .sub(row[kc])
            .mul(row[r0s].mul(row[r0s_inv]).sub(Felt::ONE))
    });

    air.add_single_row(1, move |row| {
        recompose(row, base + COL_R1_BITS, HIGH_BITS).sub(row[r1])
    });

    air.add_single_row(1, move |row| {
        recompose(row, base + COL_R0S_BITS, LOW_BITS).sub(row[r0s])
    });
    air.add_single_row(1, move |row| {
        recompose(row, base + COL_R0S_SLACK, LOW_BITS).sub(low_bound.sub(row[r0s]))
    });

    for k in 0..HIGH_BITS {
        let col = base + COL_R1_BITS + k;
        air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
    }
    for start in [COL_R0S_BITS, COL_R0S_SLACK] {
        for k in 0..LOW_BITS {
            let col = base + start + k;
            air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
        }
    }
}

pub fn decompose_air(length: usize) -> Air {
    let mut air = Air::new(WIDTH, length);
    add_constraints(&mut air, 0);
    air
}

fn set_bits(trace: &mut TraceTable, col: usize, row: usize, value: u64, bits: usize) {
    for k in 0..bits {
        trace.set(col + k, row, Felt::new((value >> k) & 1));
    }
}

pub fn decompose(r: u64) -> (u64, i64, u64) {
    let r0_raw = r % ALPHA;
    let r0c = if r0_raw <= GAMMA2 {
        r0_raw as i64
    } else {
        r0_raw as i64 - ALPHA as i64
    };
    let quotient = (r as i64 - r0c) / ALPHA as i64;
    if quotient == HIGH_COUNT as i64 {
        (0, r0c - 1, 1)
    } else {
        (quotient as u64, r0c, 0)
    }
}

pub fn fill_row(trace: &mut TraceTable, base: usize, row: usize, r: u64) {
    let (r1, r0c, kc) = decompose(r);
    let r0s = (r0c + LOW_SHIFT as i64) as u64;
    trace.set(base + COL_R, row, Felt::new(r));
    trace.set(base + COL_R1, row, Felt::new(r1));
    trace.set(base + COL_R0S, row, Felt::new(r0s));
    trace.set(base + COL_KC, row, Felt::new(kc));
    let inverse = if kc == 0 {
        Felt::new(r0s).inv()
    } else {
        Felt::ZERO
    };
    trace.set(base + COL_R0S_INV, row, inverse);
    set_bits(trace, base + COL_R1_BITS, row, r1, HIGH_BITS);
    set_bits(trace, base + COL_R0S_BITS, row, r0s, LOW_BITS);
    let slack = ALPHA.wrapping_sub(r0s);
    set_bits(trace, base + COL_R0S_SLACK, row, slack, LOW_BITS);
}

pub struct DecomposeBatch {
    pub air: Air,
    pub trace: TraceTable,
    pub count: usize,
}

pub fn decompose_batch(coefficients: &[u64]) -> DecomposeBatch {
    let count = coefficients.len();
    let length = count.next_power_of_two().max(2);
    let mut trace = TraceTable::new(WIDTH, length);
    for row in 0..length {
        let r = if row < count {
            coefficients[row] % Q
        } else {
            0
        };
        fill_row(&mut trace, 0, row, r);
    }
    DecomposeBatch {
        air: decompose_air(length),
        trace,
        count,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark::{prove, verify, StarkParams};

    fn params() -> StarkParams {
        StarkParams {
            lde_blowup: 8,
            num_queries: 24,
        }
    }

    #[test]
    fn the_parameters_match_the_set() {
        assert_eq!(GAMMA2, 261888);
        assert_eq!(ALPHA, 523776);
        assert_eq!(HIGH_COUNT, 16);
    }

    #[test]
    fn the_split_reconstructs_every_coefficient() {
        for r in [0u64, 1, GAMMA2, ALPHA, ALPHA + 5, Q - 1, Q / 3, Q - GAMMA2] {
            let (r1, r0c, kc) = decompose(r);
            assert!(r1 < HIGH_COUNT);
            assert!(r0c >= -(GAMMA2 as i64) && r0c <= GAMMA2 as i64);
            let recon = (r1 as i64 * ALPHA as i64 + r0c + kc as i64 * Q as i64) as u64;
            assert_eq!(recon % Q, r);
        }
    }

    #[test]
    fn a_batch_holds_the_decomposition() {
        let coeffs: Vec<u64> = (0..40u64).map(|i| i.wrapping_mul(332261) % Q).collect();
        let batch = decompose_batch(&coeffs);
        assert!(batch.air.is_satisfied(&batch.trace));
    }

    #[test]
    fn a_wrong_high_part_is_rejected() {
        let batch = decompose_batch(&[ALPHA + 7, 3 * ALPHA + 2, Q - 1, 100]);
        let mut trace = batch.trace;
        trace.set(COL_R1, 1, trace.get(COL_R1, 1).add(Felt::ONE));
        assert!(!batch.air.is_satisfied(&trace));
    }

    #[test]
    fn a_batch_proves_and_verifies() {
        let coeffs: Vec<u64> = (0..60u64)
            .map(|i| i.wrapping_mul(2654435769) % Q)
            .collect();
        let batch = decompose_batch(&coeffs);
        let proof = prove(&batch.air, &batch.trace, &params());
        assert!(verify(
            &decompose_air(batch.trace.length()),
            &params(),
            &proof
        ));
    }

    #[test]
    fn the_non_canonical_boundary_representation_is_rejected() {
        let batch = decompose_batch(&[GAMMA2]);
        let mut trace = batch.trace;
        trace.set(COL_R1, 0, Felt::ONE);
        trace.set(COL_R0S, 0, Felt::ZERO);
        trace.set(COL_KC, 0, Felt::ZERO);
        set_bits(&mut trace, COL_R1_BITS, 0, 1, HIGH_BITS);
        set_bits(&mut trace, COL_R0S_BITS, 0, 0, LOW_BITS);
        set_bits(&mut trace, COL_R0S_SLACK, 0, ALPHA, LOW_BITS);
        assert!(!batch.air.is_satisfied(&trace));
    }

    #[test]
    fn an_out_of_range_low_part_is_rejected() {
        let batch = decompose_batch(&[5 * ALPHA + 9]);
        let mut trace = batch.trace;
        let r0s = trace.get(COL_R0S, 0);
        trace.set(COL_R0S, 0, r0s.add(Felt::new(ALPHA)));
        trace.set(COL_R1, 0, trace.get(COL_R1, 0).sub(Felt::new(2)));
        assert!(!batch.air.is_satisfied(&trace));
    }
}
