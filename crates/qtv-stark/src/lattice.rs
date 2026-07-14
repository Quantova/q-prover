//! Batch verification core for the machine lattice signature.
//!
//! The machine lattice signature verifies through the number theoretic
//! transform and modular arithmetic over the signature modulus. The atomic step
//! of both the transform twiddle products and the pointwise products in the
//! matrix vector product is a modular multiplication over that modulus. This
//! module arithmetizes that step and lays out a trace that checks a batch of
//! such multiplications.
//!
//! Each row proves one relation r equals a times b modulo q, where q is the
//! signature modulus. The row carries the quotient and the bit expansions that
//! force r into the canonical range zero to q minus one. The inputs a and b are
//! assumed already reduced, as they are when they come out of the transform.

use crate::air::{Air, TraceTable};
use crate::field::Felt;

/// The signature modulus, two to the twenty three minus two to the thirteen plus
/// one.
pub const Q: u64 = 8_380_417;

/// The ring degree of the signature.
pub const RING_DEGREE: usize = 256;

/// The bit width of a residue below the modulus.
pub const RESIDUE_BITS: usize = 23;

const COL_A: usize = 0;
const COL_B: usize = 1;
const COL_R: usize = 2;
const COL_QUO: usize = 3;
const COL_R_BITS: usize = 4;
const COL_S_BITS: usize = COL_R_BITS + RESIDUE_BITS;
const WIDTH: usize = COL_S_BITS + RESIDUE_BITS;

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

/// Builds the description for a batch of modular multiplications of the given
/// length. The length must be a power of two.
pub fn modmul_air(length: usize) -> Air {
    let mut air = Air::new(WIDTH, length);
    let modulus = Felt::new(Q);
    let modulus_minus_one = Felt::new(Q - 1);

    // r equals a times b minus the quotient times the modulus.
    air.add_single_row(2, move |row| {
        row[COL_A]
            .mul(row[COL_B])
            .sub(row[COL_QUO].mul(modulus))
            .sub(row[COL_R])
    });

    // The bit expansion of r recomposes to r.
    air.add_single_row(1, |row| recompose(row, COL_R_BITS).sub(row[COL_R]));

    // The bit expansion of q minus one minus r recomposes to that value, which
    // together with the previous expansion forces r into zero to q minus one.
    air.add_single_row(1, move |row| {
        recompose(row, COL_S_BITS).sub(modulus_minus_one.sub(row[COL_R]))
    });

    // Every bit is zero or one.
    for k in 0..RESIDUE_BITS {
        let col = COL_R_BITS + k;
        air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
    }
    for k in 0..RESIDUE_BITS {
        let col = COL_S_BITS + k;
        air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
    }

    air
}

fn fill_row(trace: &mut TraceTable, row: usize, a: u64, b: u64) {
    let product = (a as u128) * (b as u128);
    let quotient = (product / Q as u128) as u64;
    let residue = (product % Q as u128) as u64;
    let slack = Q - 1 - residue;

    trace.set(COL_A, row, Felt::new(a));
    trace.set(COL_B, row, Felt::new(b));
    trace.set(COL_R, row, Felt::new(residue));
    trace.set(COL_QUO, row, Felt::new(quotient));
    for k in 0..RESIDUE_BITS {
        trace.set(COL_R_BITS + k, row, Felt::new((residue >> k) & 1));
        trace.set(COL_S_BITS + k, row, Felt::new((slack >> k) & 1));
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
/// taken as pairs a and b already reduced below the modulus. The trace is padded
/// with zero multiplications up to a power of two length.
pub fn modmul_batch(inputs: &[(u64, u64)]) -> ModMulBatch {
    let count = inputs.len();
    let length = count.next_power_of_two().max(2);
    let mut trace = TraceTable::new(WIDTH, length);
    for row in 0..length {
        let (a, b) = if row < count { inputs[row] } else { (0, 0) };
        fill_row(&mut trace, row, a % Q, b % Q);
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
            fill_row(&mut trace, row, a, b);
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
