//! Hint application for the verify relation.
//!
//! After the commitment coefficients are decomposed, the signature carries one
//! hint bit per coefficient. The verifier applies the hint to recover the high
//! bits it hashes. When the hint is set the high part moves up by one if the
//! centered low part is positive and down by one otherwise, wrapping around the
//! sixteen high values. This module arithmetizes that recovery on top of the
//! decomposition, so the used high part is bound to the coefficient and the hint.
//!
//! The coefficient r is assumed already reduced below the modulus, as it is when
//! it comes out of the transform.

use crate::air::{Air, TraceTable};
use crate::decompose::{decompose, ALPHA, GAMMA2, HIGH_COUNT};
use crate::field::Felt;
use crate::lattice::Q;

const HIGH_BITS: usize = 4;
const LOW_BITS: usize = 20;
const POS_BITS: usize = 18;

const COL_R: usize = 0;
const COL_H: usize = 1;
const COL_R1: usize = 2;
const COL_R0S: usize = 3;
const COL_KC: usize = 4;
const COL_R0S_INV: usize = 5;
const COL_POS: usize = 6;
const COL_DPOS: usize = 7;
const COL_R1U: usize = 8;
const COL_HI: usize = 9;
const COL_LO: usize = 10;
const COL_R1_BITS: usize = 11;
const COL_R0S_BITS: usize = COL_R1_BITS + HIGH_BITS;
const COL_R0S_SLACK: usize = COL_R0S_BITS + LOW_BITS;
const COL_DPOS_BITS: usize = COL_R0S_SLACK + LOW_BITS;
const COL_DPOS_SLACK: usize = COL_DPOS_BITS + POS_BITS;
const COL_R1U_BITS: usize = COL_DPOS_SLACK + POS_BITS;
const WIDTH: usize = COL_R1U_BITS + HIGH_BITS;

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

/// The high bits the verifier recovers by applying the hint bit to the
/// coefficient.
pub fn use_hint(h: u64, r: u64) -> u64 {
    let (r1, r0c, _) = decompose(r);
    if h == 0 {
        return r1;
    }
    let delta: i64 = if r0c > 0 { 1 } else { -1 };
    (r1 as i64 + delta).rem_euclid(HIGH_COUNT as i64) as u64
}

/// Builds the hint recovery description of the given length. The length must be
/// a power of two.
pub fn hint_air(length: usize) -> Air {
    let mut air = Air::new(WIDTH, length);
    let alpha = Felt::new(ALPHA);
    let modulus = Felt::new(Q);
    let gamma2 = Felt::new(GAMMA2);
    let gamma2_plus_one = Felt::new(GAMMA2 + 1);
    let high = Felt::new(HIGH_COUNT);
    let low_bound = Felt::new(ALPHA);

    // The decomposition relation and its canonical gates, as in the decompose
    // module.
    air.add_single_row(1, move |row| {
        row[COL_R]
            .sub(row[COL_R1].mul(alpha))
            .sub(row[COL_R0S].sub(gamma2))
            .sub(row[COL_KC].mul(modulus))
    });
    air.add_single_row(2, |row| row[COL_KC].mul(row[COL_KC].sub(Felt::ONE)));
    air.add_single_row(2, |row| row[COL_KC].mul(row[COL_R1]));
    air.add_single_row(3, |row| {
        Felt::ONE
            .sub(row[COL_KC])
            .mul(row[COL_R0S].mul(row[COL_R0S_INV]).sub(Felt::ONE))
    });
    air.add_single_row(1, |row| {
        recompose(row, COL_R1_BITS, HIGH_BITS).sub(row[COL_R1])
    });
    air.add_single_row(1, |row| {
        recompose(row, COL_R0S_BITS, LOW_BITS).sub(row[COL_R0S])
    });
    air.add_single_row(1, move |row| {
        recompose(row, COL_R0S_SLACK, LOW_BITS).sub(low_bound.sub(row[COL_R0S]))
    });

    // The sign of the centered low part. The positive flag is one exactly when
    // the shifted low part is above gamma2, which the shifted remainder pins.
    air.add_single_row(2, |row| row[COL_POS].mul(row[COL_POS].sub(Felt::ONE)));
    air.add_single_row(1, move |row| {
        row[COL_DPOS]
            .sub(row[COL_R0S])
            .add(row[COL_POS].mul(gamma2_plus_one))
    });
    air.add_single_row(1, |row| {
        recompose(row, COL_DPOS_BITS, POS_BITS).sub(row[COL_DPOS])
    });
    air.add_single_row(1, move |row| {
        recompose(row, COL_DPOS_SLACK, POS_BITS).sub(gamma2.sub(row[COL_DPOS]))
    });

    // The hint bit and the wrap bits.
    air.add_single_row(2, |row| row[COL_H].mul(row[COL_H].sub(Felt::ONE)));
    air.add_single_row(2, |row| row[COL_HI].mul(row[COL_HI].sub(Felt::ONE)));
    air.add_single_row(2, |row| row[COL_LO].mul(row[COL_LO].sub(Felt::ONE)));

    // The used high part is the high part shifted by the hint direction, modulo
    // the high count. The direction is plus one when the sign flag is set and
    // minus one otherwise, taken only when the hint is set.
    air.add_single_row(2, move |row| {
        let direction = row[COL_POS].add(row[COL_POS]).sub(Felt::ONE);
        row[COL_R1U]
            .sub(row[COL_R1])
            .sub(row[COL_H].mul(direction))
            .add(high.mul(row[COL_HI]))
            .sub(high.mul(row[COL_LO]))
    });
    air.add_single_row(1, |row| {
        recompose(row, COL_R1U_BITS, HIGH_BITS).sub(row[COL_R1U])
    });

    // The high part range.
    for k in 0..HIGH_BITS {
        let col = COL_R1_BITS + k;
        air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
        let col = COL_R1U_BITS + k;
        air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
    }
    for base in [COL_R0S_BITS, COL_R0S_SLACK] {
        for k in 0..LOW_BITS {
            let col = base + k;
            air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
        }
    }
    for base in [COL_DPOS_BITS, COL_DPOS_SLACK] {
        for k in 0..POS_BITS {
            let col = base + k;
            air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
        }
    }

    air
}

fn set_bits(trace: &mut TraceTable, base: usize, row: usize, value: u64, bits: usize) {
    for k in 0..bits {
        trace.set(base + k, row, Felt::new((value >> k) & 1));
    }
}

fn fill_row(trace: &mut TraceTable, row: usize, r: u64, h: u64) {
    let (r1, r0c, kc) = decompose(r);
    let r0s = (r0c + GAMMA2 as i64) as u64;
    let pos = if r0c > 0 { 1u64 } else { 0 };
    let dpos = r0s - pos * (GAMMA2 + 1);
    let delta: i64 = if h == 1 {
        if pos == 1 {
            1
        } else {
            -1
        }
    } else {
        0
    };
    let raw = r1 as i64 + delta;
    let hi = if raw == HIGH_COUNT as i64 { 1u64 } else { 0 };
    let lo = if raw == -1 { 1u64 } else { 0 };
    let r1u = (raw - HIGH_COUNT as i64 * hi as i64 + HIGH_COUNT as i64 * lo as i64) as u64;

    trace.set(COL_R, row, Felt::new(r));
    trace.set(COL_H, row, Felt::new(h));
    trace.set(COL_R1, row, Felt::new(r1));
    trace.set(COL_R0S, row, Felt::new(r0s));
    trace.set(COL_KC, row, Felt::new(kc));
    let inverse = if kc == 0 {
        Felt::new(r0s).inv()
    } else {
        Felt::ZERO
    };
    trace.set(COL_R0S_INV, row, inverse);
    trace.set(COL_POS, row, Felt::new(pos));
    trace.set(COL_DPOS, row, Felt::new(dpos));
    trace.set(COL_R1U, row, Felt::new(r1u));
    trace.set(COL_HI, row, Felt::new(hi));
    trace.set(COL_LO, row, Felt::new(lo));
    set_bits(trace, COL_R1_BITS, row, r1, HIGH_BITS);
    set_bits(trace, COL_R0S_BITS, row, r0s, LOW_BITS);
    set_bits(trace, COL_R0S_SLACK, row, ALPHA.wrapping_sub(r0s), LOW_BITS);
    set_bits(trace, COL_DPOS_BITS, row, dpos, POS_BITS);
    set_bits(
        trace,
        COL_DPOS_SLACK,
        row,
        GAMMA2.wrapping_sub(dpos),
        POS_BITS,
    );
    set_bits(trace, COL_R1U_BITS, row, r1u, HIGH_BITS);
}

/// A filled hint recovery batch with its description.
pub struct HintBatch {
    /// The description shared with the verifier.
    pub air: Air,
    /// The filled trace.
    pub trace: TraceTable,
    /// The number of real coefficients before padding.
    pub count: usize,
}

/// Lays out a trace that recovers the used high bits for a batch of coefficient
/// and hint pairs. The trace is padded with zero pairs up to a power of two
/// length.
pub fn hint_batch(pairs: &[(u64, u64)]) -> HintBatch {
    let count = pairs.len();
    let length = count.next_power_of_two().max(2);
    let mut trace = TraceTable::new(WIDTH, length);
    for row in 0..length {
        let (r, h) = if row < count {
            (pairs[row].0 % Q, pairs[row].1 & 1)
        } else {
            (0, 0)
        };
        fill_row(&mut trace, row, r, h);
    }
    HintBatch {
        air: hint_air(length),
        trace,
        count,
    }
}

/// Reads the recovered high part of a row from a filled trace.
pub fn recovered_high(trace: &TraceTable, row: usize) -> u64 {
    trace.get(COL_R1U, row).to_u64()
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
    fn the_recovered_high_matches_the_reference() {
        let batch = hint_batch(&[
            (0, 0),
            (ALPHA + 9, 1),
            (Q - 1, 1),
            (5 * ALPHA + 3, 1),
            (77, 0),
        ]);
        for row in 0..5 {
            let r = batch.trace.get(COL_R, row).to_u64();
            let h = batch.trace.get(COL_H, row).to_u64();
            assert_eq!(recovered_high(&batch.trace, row), use_hint(h, r));
        }
        assert!(batch.air.is_satisfied(&batch.trace));
    }

    #[test]
    fn a_set_hint_moves_the_high_part() {
        // A coefficient with a positive low part moves up by one under the hint.
        let r = ALPHA + 100;
        let (r1, r0c, _) = decompose(r);
        assert!(r0c > 0);
        assert_eq!(use_hint(1, r), (r1 + 1) % HIGH_COUNT);
        let batch = hint_batch(&[(r, 1)]);
        assert!(batch.air.is_satisfied(&batch.trace));
    }

    #[test]
    fn a_forged_used_high_is_rejected() {
        let batch = hint_batch(&[(ALPHA + 100, 1)]);
        let mut trace = batch.trace;
        trace.set(COL_R1U, 0, trace.get(COL_R1U, 0).add(Felt::ONE));
        assert!(!batch.air.is_satisfied(&trace));
    }

    #[test]
    fn a_forged_sign_flag_is_rejected() {
        // A coefficient with a negative low part cannot claim a positive sign.
        let r = ALPHA - 100;
        let (_, r0c, _) = decompose(r);
        assert!(r0c < 0);
        let batch = hint_batch(&[(r, 1)]);
        let mut trace = batch.trace;
        trace.set(COL_POS, 0, Felt::ONE);
        assert!(!batch.air.is_satisfied(&trace));
    }

    #[test]
    fn a_batch_proves_and_verifies() {
        let pairs: Vec<(u64, u64)> = (0..48u64)
            .map(|i| (i.wrapping_mul(0x9e37_79b9) % Q, i & 1))
            .collect();
        let batch = hint_batch(&pairs);
        let proof = prove(&batch.air, &batch.trace, &params());
        assert!(verify(&hint_air(batch.trace.length()), &params(), &proof));
    }
}
