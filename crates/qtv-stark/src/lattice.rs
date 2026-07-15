//! Batch verification core for the module lattice signature.

use crate::air::{Air, TraceTable};
use crate::field::Felt;

/// The signature modulus, two to the twenty three minus two to the thirteen plus
pub const Q: u64 = 8_380_417;

/// The ring degree of the signature.
pub const RING_DEGREE: usize = 256;

/// The bit width of a residue below the modulus.
pub const RESIDUE_BITS: usize = 23;

/// The row count of the public matrix in the verification relation.
pub const MATRIX_ROWS: usize = 6;

/// The column count of the public matrix in the verification relation.
pub const MATRIX_COLS: usize = 5;

/// The count of coordinatewise modular multiplications in the transform domain
pub const PRODUCTS_PER_SIGNATURE: usize = MATRIX_ROWS * MATRIX_COLS * RING_DEGREE;

/// Produces the modular multiplication workload for a batch of signatures. Each
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

/// The first factor column, relative to the piece base. In the transform domain
pub const COL_A: usize = 0;
/// The second factor column, relative to the piece base. In the matrix vector
pub const COL_B: usize = 1;

/// The product residue column, relative to the piece base.
pub const COL_R: usize = 2;
const COL_QUO: usize = 3;
const COL_R_BITS: usize = 4;
const COL_S_BITS: usize = COL_R_BITS + RESIDUE_BITS;

/// The column width of the modular multiplication piece.
pub const WIDTH: usize = COL_S_BITS + RESIDUE_BITS;

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

/// Adds the modular multiplication constraints at the given column base, so the
pub fn add_constraints(air: &mut Air, base: usize) {
    let modulus = Felt::new(Q);
    let modulus_minus_one = Felt::new(Q - 1);
    let a = base + COL_A;
    let b = base + COL_B;
    let r = base + COL_R;
    let quo = base + COL_QUO;

    // r equals a times b minus the quotient times the modulus.
    air.add_single_row(2, move |row| {
        row[a].mul(row[b]).sub(row[quo].mul(modulus)).sub(row[r])
    });

    // The bit expansion of r recomposes to r.
    air.add_single_row(1, move |row| recompose(row, base + COL_R_BITS).sub(row[r]));

    // The bit expansion of q minus one minus r recomposes to that value, which
    // together with the previous expansion forces r into zero to q minus one.
    air.add_single_row(1, move |row| {
        recompose(row, base + COL_S_BITS).sub(modulus_minus_one.sub(row[r]))
    });

    // Every bit is zero or one.
    for k in 0..RESIDUE_BITS {
        let col = base + COL_R_BITS + k;
        air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
    }
    for k in 0..RESIDUE_BITS {
        let col = base + COL_S_BITS + k;
        air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
    }
}

/// Builds the description for a batch of modular multiplications of the given
pub fn modmul_air(length: usize) -> Air {
    let mut air = Air::new(WIDTH, length);
    add_constraints(&mut air, 0);
    air
}

/// Fills one modular multiplication row at the given column base.
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
    }
}

/// A filled batch trace with its description.
pub struct ModMulBatch {
    /// The description shared with the verifier.
    pub air: Air,
    /// The filled trace.
    pub trace: TraceTable,
    /// The number of real multiplications, before padding.
    pub count: usize,
}

/// Lays out a trace that checks the batch of modular multiplications. Inputs are
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
                let a = i.wrapping_mul(0x9e37_79b9) % Q;
                let b = (i.wrapping_mul(0x8542_1f4b) + 7) % Q;
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
        let workload = signature_batch_workload(2, 0x1234);
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
        // Break the residue on one row without fixing its bit expansion.
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
    fn a_non_canonical_residue_is_rejected() {
        // A residue shifted by the modulus keeps the product identity but must
        // fail the canonical range expansion.
        let a = 3u64;
        let b = 5u64;
        let length = 2;
        let mut trace = TraceTable::new(WIDTH, length);
        for row in 0..length {
            fill_row(&mut trace, 0, row, a, b);
        }
        // Row zero true residue is 15. Replace it with 15 plus q and drop the
        // quotient by one, which keeps a times b but leaves the range.
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
