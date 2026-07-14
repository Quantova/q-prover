//! High and low bit decomposition for the verify relation.

use crate::air::{Air, TraceTable};
use crate::field::Felt;
use crate::lattice::Q;

/// The low bit parameter gamma2 for the ML DSA 65 parameter set, the modulus
pub const GAMMA2: u64 = (Q - 1) / 32;

/// The decomposition step alpha, twice gamma2.
pub const ALPHA: u64 = 2 * GAMMA2;

/// The number of high parts, the modulus minus one over alpha.
pub const HIGH_COUNT: u64 = (Q - 1) / ALPHA;

/// The bit width of a high part.
pub const HIGH_BITS: usize = 4;

/// The bit width that covers the shifted low part.
pub const LOW_BITS: usize = 20;

/// The input coefficient column, relative to the piece base.
pub const COL_R: usize = 0;
const COL_R1: usize = 1;
const COL_R0S: usize = 2;
const COL_KC: usize = 3;
const COL_R0S_INV: usize = 4;
const COL_R1_BITS: usize = 5;
const COL_R0S_BITS: usize = COL_R1_BITS + HIGH_BITS;
const COL_R0S_SLACK: usize = COL_R0S_BITS + LOW_BITS;

/// The column width of the decomposition piece.
pub const WIDTH: usize = COL_R0S_SLACK + LOW_BITS;

// The shift that carries the centered low part into the non negative range
// zero to alpha.
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

/// Adds the decomposition constraints at the given column base, so the piece can
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

    // r equals r1 times alpha plus the centered low part plus the wrap term. The
    // centered low part is the shifted low column minus gamma2.
    air.add_single_row(1, move |row| {
        row[r]
            .sub(row[r1].mul(alpha))
            .sub(row[r0s].sub(low_shift))
            .sub(row[kc].mul(modulus))
    });

    // The wrap term is a bit.
    air.add_single_row(2, move |row| row[kc].mul(row[kc].sub(Felt::ONE)));

    // The wrap only fires for the top segment, where the high part is zero.
    air.add_single_row(2, move |row| row[kc].mul(row[r1]));

    // Off the wrap the centered low part stays above minus gamma2, so the
    // shifted low part is non zero. The inverse witness pins that, which removes
    // the boundary ambiguity between the two representations at plus or minus
    // gamma2.
    air.add_single_row(3, move |row| {
        Felt::ONE
            .sub(row[kc])
            .mul(row[r0s].mul(row[r0s_inv]).sub(Felt::ONE))
    });

    // The high part recomposes from four bits, which forces it below sixteen.
    air.add_single_row(1, move |row| {
        recompose(row, base + COL_R1_BITS, HIGH_BITS).sub(row[r1])
    });

    // The shifted low part recomposes, and its slack recomposes to alpha minus
    // it, which together force it within zero to alpha.
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

/// Builds the decomposition description of the given length. The length must be a
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

/// The decomposition of one coefficient into a high part, a centered low part,
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

/// Fills one decomposition row at the given column base.
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

/// A filled decomposition batch with its description.
pub struct DecomposeBatch {
    /// The description shared with the verifier.
    pub air: Air,
    /// The filled trace.
    pub trace: TraceTable,
    /// The number of real coefficients before padding.
    pub count: usize,
}

/// Lays out a trace that decomposes a batch of coefficients. The trace is padded
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
        let coeffs: Vec<u64> = (0..40u64).map(|i| i.wrapping_mul(0x51_1e5) % Q).collect();
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
            .map(|i| i.wrapping_mul(0x9e37_79b9) % Q)
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
        // The coefficient gamma2 splits canonically as high part zero and low
        // part gamma2. The alternative high part one with low part minus gamma2
        // satisfies the modular relation but sets the shifted low part to zero
        // off the wrap, which the inverse gate rejects.
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
        // Move the whole low part above alpha while keeping the field relation by
        // dropping the high part, which the range check must catch.
        let batch = decompose_batch(&[5 * ALPHA + 9]);
        let mut trace = batch.trace;
        let r0s = trace.get(COL_R0S, 0);
        trace.set(COL_R0S, 0, r0s.add(Felt::new(ALPHA)));
        trace.set(COL_R1, 0, trace.get(COL_R1, 0).sub(Felt::new(2)));
        assert!(!batch.air.is_satisfied(&trace));
    }
}
