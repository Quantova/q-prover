//! Infinity norm range check for the signature response.
//!
//! The verify relation rejects a signature whose response vector z leaves the
//! band around zero. Each coefficient sits in zero to the modulus minus one and
//! stands for a centered value, small when it is below the modulus over two and
//! negative when it is above. The check proves the centered magnitude of every
//! coefficient is below the bound gamma1 minus beta, so a coefficient in the
//! middle band is rejected.

use crate::air::{Air, TraceTable};
use crate::field::Felt;
use crate::lattice::Q;

/// The response range parameter gamma1 for the ML DSA 65 parameter set, two to
/// the nineteen.
pub const GAMMA1: u64 = 1 << 19;

/// The rejection margin beta for the ML DSA 65 parameter set, the challenge
/// weight times the secret bound.
pub const BETA: u64 = 196;

/// The exclusive infinity norm bound the response must respect.
pub const NORM_BOUND: u64 = GAMMA1 - BETA;

/// The bit width that covers the bound.
pub const NORM_BITS: usize = 20;

/// The input response coefficient column, relative to the piece base.
pub const COL_Z: usize = 0;
const COL_SIGN: usize = 1;
const COL_MAG: usize = 2;
const COL_MAG_BITS: usize = 3;
const COL_MAG_SLACK: usize = COL_MAG_BITS + NORM_BITS;

/// The column width of the norm check piece.
pub const WIDTH: usize = COL_MAG_SLACK + NORM_BITS;

fn recompose(row: &[Felt], base: usize) -> Felt {
    let two = Felt::new(2);
    let mut acc = Felt::ZERO;
    let mut weight = Felt::ONE;
    for k in 0..NORM_BITS {
        acc = acc.add(row[base + k].mul(weight));
        weight = weight.mul(two);
    }
    acc
}

/// Adds the infinity norm constraints at the given column base, so the piece can
/// be placed inside a wider joined trace.
pub fn add_constraints(air: &mut Air, base: usize) {
    let modulus = Felt::new(Q);
    let bound_minus_one = Felt::new(NORM_BOUND - 1);
    let z = base + COL_Z;
    let sign = base + COL_SIGN;
    let mag = base + COL_MAG;

    // The centered magnitude is the coefficient when the sign bit is zero and
    // the modulus minus the coefficient when the sign bit is one.
    air.add_single_row(2, move |row| {
        let mirror = modulus.sub(row[z].add(row[z]));
        row[mag].sub(row[z]).sub(row[sign].mul(mirror))
    });

    // The sign is a bit.
    air.add_single_row(2, move |row| row[sign].mul(row[sign].sub(Felt::ONE)));

    // The magnitude bit expansion recomposes to the magnitude, and the slack
    // expansion recomposes to the bound minus one minus the magnitude, which
    // together force the magnitude below the bound.
    air.add_single_row(1, move |row| {
        recompose(row, base + COL_MAG_BITS).sub(row[mag])
    });
    air.add_single_row(1, move |row| {
        recompose(row, base + COL_MAG_SLACK).sub(bound_minus_one.sub(row[mag]))
    });

    for start in [COL_MAG_BITS, COL_MAG_SLACK] {
        for k in 0..NORM_BITS {
            let col = base + start + k;
            air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
        }
    }
}

/// Builds the description for a batch of infinity norm checks of the given
/// length. The length must be a power of two.
pub fn norm_air(length: usize) -> Air {
    let mut air = Air::new(WIDTH, length);
    add_constraints(&mut air, 0);
    air
}

/// Fills one infinity norm check row at the given column base.
pub fn fill_row(trace: &mut TraceTable, base: usize, row: usize, z: u64) {
    let (sign, magnitude) = if z <= Q / 2 { (0u64, z) } else { (1u64, Q - z) };
    trace.set(base + COL_Z, row, Felt::new(z));
    trace.set(base + COL_SIGN, row, Felt::new(sign));
    trace.set(base + COL_MAG, row, Felt::new(magnitude));
    // A coefficient outside the bound has no honest witness. The wrapping keeps
    // the fill total so the range constraints reject it rather than panicking.
    let slack = (NORM_BOUND - 1).wrapping_sub(magnitude);
    for k in 0..NORM_BITS {
        trace.set(
            base + COL_MAG_BITS + k,
            row,
            Felt::new((magnitude >> k) & 1),
        );
        trace.set(base + COL_MAG_SLACK + k, row, Felt::new((slack >> k) & 1));
    }
}

/// A filled norm batch with its description.
pub struct NormBatch {
    /// The description shared with the verifier.
    pub air: Air,
    /// The filled trace.
    pub trace: TraceTable,
    /// The number of real coefficients before padding.
    pub count: usize,
}

/// Lays out a trace that checks the infinity norm of a batch of coefficients.
/// The trace is padded with zero coefficients up to a power of two length.
pub fn norm_batch(coefficients: &[u64]) -> NormBatch {
    let count = coefficients.len();
    let length = count.next_power_of_two().max(2);
    let mut trace = TraceTable::new(WIDTH, length);
    for row in 0..length {
        let z = if row < count {
            coefficients[row] % Q
        } else {
            0
        };
        fill_row(&mut trace, 0, row, z);
    }
    NormBatch {
        air: norm_air(length),
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
    fn small_and_negative_coefficients_pass() {
        let coeffs = [0u64, 1, 5, NORM_BOUND - 1, Q - 1, Q - (NORM_BOUND - 1)];
        let batch = norm_batch(&coeffs);
        assert!(batch.air.is_satisfied(&batch.trace));
    }

    #[test]
    fn a_coefficient_on_the_bound_is_rejected() {
        let batch = norm_batch(&[NORM_BOUND]);
        assert!(!batch.air.is_satisfied(&batch.trace));
    }

    #[test]
    fn a_middle_band_coefficient_is_rejected() {
        // A coefficient at the modulus over two is as far from zero as possible.
        let batch = norm_batch(&[Q / 2]);
        assert!(!batch.air.is_satisfied(&batch.trace));
    }

    #[test]
    fn a_batch_proves_and_verifies() {
        let coeffs: Vec<u64> = (0..50u64)
            .map(|i| {
                let m = i.wrapping_mul(37) % NORM_BOUND;
                if i % 2 == 0 {
                    m
                } else {
                    Q - m
                }
            })
            .collect();
        let batch = norm_batch(&coeffs);
        let proof = prove(&batch.air, &batch.trace, &params());
        assert!(verify(&norm_air(batch.trace.length()), &params(), &proof));
    }

    #[test]
    fn a_tampered_coefficient_is_rejected() {
        let batch = norm_batch(&[1, 2, 3, 4]);
        let mut trace = batch.trace;
        trace.set(COL_Z, 2, Felt::new(Q / 2));
        assert!(!batch.air.is_satisfied(&trace));
        let proof = prove(&batch.air, &trace, &params());
        assert!(!verify(&norm_air(trace.length()), &params(), &proof));
    }
}
