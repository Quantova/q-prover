// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT


use crate::air::{Air, TraceTable};
use crate::field::Felt;

pub const Q: u64 = 8_380_417;

pub const RING_DEGREE: usize = 256;

pub const RESIDUE_BITS: usize = 23;

pub const MATRIX_ROWS: usize = 6;

pub const MATRIX_COLS: usize = 5;

pub const PRODUCTS_PER_SIGNATURE: usize = MATRIX_ROWS * MATRIX_COLS * RING_DEGREE;

pub fn signature_batch_workload(signatures: usize, seed: u64) -> Vec<(u64, u64)> {
    let mut state = seed | 1;
    let mut draw = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state % Q
    };
    (0..signatures * PRODUCTS_PER_SIGNATURE)
        .map(|_| (draw(), draw()))
        .collect()
}

pub const COL_A: usize = 0;
pub const COL_B: usize = 1;

pub const COL_R: usize = 2;
const COL_QUO: usize = 3;
const COL_R_BITS: usize = 4;
const COL_S_BITS: usize = COL_R_BITS + RESIDUE_BITS;
const COL_QUO_BITS: usize = COL_S_BITS + RESIDUE_BITS;

pub const WIDTH: usize = COL_QUO_BITS + RESIDUE_BITS;

fn recompose(row: &[Felt], base: usize) -> Felt {
    let two = Felt::new(2);
    let mut acc = Felt::ZERO;
    let mut weight = Felt::ONE;
    for k in 0..RESIDUE_BITS {
        acc = acc.add(row[base + k].mul(weight));
        weight = weight.mul(two);
    }
    acc
}

pub fn add_constraints(air: &mut Air, base: usize) {
    let modulus = Felt::new(Q);
    let modulus_minus_one = Felt::new(Q - 1);
    let a = base + COL_A;
    let b = base + COL_B;
    let r = base + COL_R;
    let quo = base + COL_QUO;

    air.add_single_row(2, move |row| {
        row[a].mul(row[b]).sub(row[quo].mul(modulus)).sub(row[r])
    });

    air.add_single_row(1, move |row| recompose(row, base + COL_R_BITS).sub(row[r]));

    air.add_single_row(1, move |row| {
        recompose(row, base + COL_S_BITS).sub(modulus_minus_one.sub(row[r]))
    });

    air.add_single_row(1, move |row| recompose(row, base + COL_QUO_BITS).sub(row[quo]));

    for k in 0..RESIDUE_BITS {
        let col = base + COL_R_BITS + k;
        air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
    }
    for k in 0..RESIDUE_BITS {
        let col = base + COL_S_BITS + k;
        air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
    }
    for k in 0..RESIDUE_BITS {
        let col = base + COL_QUO_BITS + k;
        air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
    }
}

pub fn modmul_air(length: usize) -> Air {
    let mut air = Air::new(WIDTH, length);
    add_constraints(&mut air, 0);
    air
}

pub fn fill_row(trace: &mut TraceTable, base: usize, row: usize, a: u64, b: u64) {
    let product = (a as u128) * (b as u128);
    let quotient = (product / Q as u128) as u64;
    let residue = (product % Q as u128) as u64;
    let slack = Q - 1 - residue;

    trace.set(base + COL_A, row, Felt::new(a));
    trace.set(base + COL_B, row, Felt::new(b));
    trace.set(base + COL_R, row, Felt::new(residue));
    trace.set(base + COL_QUO, row, Felt::new(quotient));
    for k in 0..RESIDUE_BITS {
        trace.set(base + COL_R_BITS + k, row, Felt::new((residue >> k) & 1));
        trace.set(base + COL_S_BITS + k, row, Felt::new((slack >> k) & 1));
        trace.set(base + COL_QUO_BITS + k, row, Felt::new((quotient >> k) & 1));
    }
}

pub struct ModMulBatch {
    pub air: Air,
    pub trace: TraceTable,
    pub count: usize,
}

pub fn modmul_batch(inputs: &[(u64, u64)]) -> ModMulBatch {
    let count = inputs.len();
    let length = count.next_power_of_two().max(2);
    let mut trace = TraceTable::new(WIDTH, length);
    for row in 0..length {
        let (a, b) = if row < count { inputs[row] } else { (0, 0) };
        fill_row(&mut trace, 0, row, a % Q, b % Q);
    }
    ModMulBatch {
        air: modmul_air(length),
        trace,
        count,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark::{prove, verify, StarkParams};

    fn sample_inputs(count: usize) -> Vec<(u64, u64)> {
        (0..count as u64)
            .map(|i| {
                let a = i.wrapping_mul(2654435769) % Q;
                let b = (i.wrapping_mul(2235703115) + 7) % Q;
                (a, b)
            })
            .collect()
    }

    #[test]
    fn each_row_holds_a_modular_product() {
        let batch = modmul_batch(&sample_inputs(20));
        for row in 0..20 {
            let a = batch.trace.get(COL_A, row).to_u64();
            let b = batch.trace.get(COL_B, row).to_u64();
            let r = batch.trace.get(COL_R, row).to_u64();
            assert_eq!(r, ((a as u128 * b as u128) % Q as u128) as u64);
            assert!(r < Q);
        }
        assert!(batch.air.is_satisfied(&batch.trace));
    }

    #[test]
    fn the_signature_workload_has_the_expected_shape() {
        let workload = signature_batch_workload(2, 4660);
        assert_eq!(workload.len(), 2 * PRODUCTS_PER_SIGNATURE);
        assert_eq!(PRODUCTS_PER_SIGNATURE, 7680);
        for (a, b) in &workload {
            assert!(*a < Q && *b < Q);
        }
    }

    #[test]
    fn a_batch_proves_and_verifies() {
        let batch = modmul_batch(&sample_inputs(100));
        let params = StarkParams {
            lde_blowup: 8,
            num_queries: 24,
        };
        let proof = prove(&batch.air, &batch.trace, &params);
        assert!(verify(&modmul_air(batch.trace.length()), &params, &proof));
    }

    #[test]
    fn a_wrong_residue_is_rejected() {
        let batch = modmul_batch(&sample_inputs(64));
        let mut trace = batch.trace;
        trace.set(COL_R, 5, trace.get(COL_R, 5).add(Felt::ONE));
        assert!(!batch.air.is_satisfied(&trace));
        let params = StarkParams {
            lde_blowup: 8,
            num_queries: 24,
        };
        let proof = prove(&batch.air, &trace, &params);
        assert!(!verify(&modmul_air(trace.length()), &params, &proof));
    }

    #[test]
    fn a_forged_residue_with_a_compensating_quotient_is_rejected() {
        let a = 3u64;
        let b = 5u64;
        let honest = (a * b) % Q;
        let forged = honest + 1;
        assert!(forged < Q);
        let quotient = Felt::new(a)
            .mul(Felt::new(b))
            .sub(Felt::new(forged))
            .mul(Felt::new(Q).inv());
        let length = 2;
        let mut trace = TraceTable::new(WIDTH, length);
        fill_row(&mut trace, 0, 1, 0, 0);
        trace.set(COL_A, 0, Felt::new(a));
        trace.set(COL_B, 0, Felt::new(b));
        trace.set(COL_R, 0, Felt::new(forged));
        trace.set(COL_QUO, 0, quotient);
        for k in 0..RESIDUE_BITS {
            trace.set(COL_R_BITS + k, 0, Felt::new((forged >> k) & 1));
            trace.set(COL_S_BITS + k, 0, Felt::new(((Q - 1 - forged) >> k) & 1));
        }
        let air = modmul_air(length);
        assert!(!air.is_satisfied(&trace));
        let params = StarkParams {
            lde_blowup: 8,
            num_queries: 24,
        };
        let proof = prove(&air, &trace, &params);
        assert!(!verify(&modmul_air(length), &params, &proof));
    }

    #[test]
    fn a_non_canonical_residue_is_rejected() {
        let a = 3u64;
        let b = 5u64;
        let length = 2;
        let mut trace = TraceTable::new(WIDTH, length);
        for row in 0..length {
            fill_row(&mut trace, 0, row, a, b);
        }
        let shifted = 15 + Q;
        trace.set(COL_R, 0, Felt::new(shifted));
        trace.set(COL_QUO, 0, trace.get(COL_QUO, 0).sub(Felt::ONE));
        for k in 0..RESIDUE_BITS {
            trace.set(COL_R_BITS + k, 0, Felt::new((shifted >> k) & 1));
            let slack = Q.wrapping_sub(1).wrapping_sub(shifted);
            trace.set(COL_S_BITS + k, 0, Felt::new((slack >> k) & 1));
        }
        let air = modmul_air(length);
        assert!(!air.is_satisfied(&trace));
    }
}
