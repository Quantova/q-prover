//! Hint application for the verify relation.

use crate::air::{Air, TraceTable};
use crate::decompose::{decompose, ALPHA, GAMMA2, HIGH_COUNT};
use crate::field::Felt;
use crate::lattice::Q;

const HIGH_BITS: usize = 4;
const LOW_BITS: usize = 20;
const POS_BITS: usize = 18;

/// The input coefficient column, relative to the piece base.
pub const COL_R: usize = 0;
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

/// The column width of the hint recovery piece.
pub const WIDTH: usize = COL_R1U_BITS + HIGH_BITS;

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
pub fn use_hint(h: u64, r: u64) -> u64 {
    let (r1, r0c, _) = decompose(r);
    if h == 0 {
        return r1;
    }
    let delta: i64 = if r0c > 0 { 1 } else { -1 };
    (r1 as i64 + delta).rem_euclid(HIGH_COUNT as i64) as u64
}

/// Adds the hint recovery constraints at the given column base, so the piece can
pub fn add_constraints(air: &mut Air, base: usize) {
    let alpha = Felt::new(ALPHA);
    let modulus = Felt::new(Q);
    let gamma2 = Felt::new(GAMMA2);
    let gamma2_plus_one = Felt::new(GAMMA2 + 1);
    let high = Felt::new(HIGH_COUNT);
    let low_bound = Felt::new(ALPHA);
    let r = base + COL_R;
    let h = base + COL_H;
    let r1 = base + COL_R1;
    let r0s = base + COL_R0S;
    let kc = base + COL_KC;
    let r0s_inv = base + COL_R0S_INV;
    let pos = base + COL_POS;
    let dpos = base + COL_DPOS;
    let r1u = base + COL_R1U;
    let hi = base + COL_HI;
    let lo = base + COL_LO;

    // The decomposition relation and its canonical gates, as in the decompose
    // module.
    air.add_single_row(1, move |row| {
        row[r]
            .sub(row[r1].mul(alpha))
            .sub(row[r0s].sub(gamma2))
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

    // The sign of the centered low part. The positive flag is one exactly when
    // the shifted low part is above gamma2, which the shifted remainder pins.
    air.add_single_row(2, move |row| row[pos].mul(row[pos].sub(Felt::ONE)));
    air.add_single_row(1, move |row| {
        row[dpos].sub(row[r0s]).add(row[pos].mul(gamma2_plus_one))
    });
    air.add_single_row(1, move |row| {
        recompose(row, base + COL_DPOS_BITS, POS_BITS).sub(row[dpos])
    });
    air.add_single_row(1, move |row| {
        recompose(row, base + COL_DPOS_SLACK, POS_BITS).sub(gamma2.sub(row[dpos]))
    });

    // The hint bit and the wrap bits.
    air.add_single_row(2, move |row| row[h].mul(row[h].sub(Felt::ONE)));
    air.add_single_row(2, move |row| row[hi].mul(row[hi].sub(Felt::ONE)));
    air.add_single_row(2, move |row| row[lo].mul(row[lo].sub(Felt::ONE)));

    // The used high part is the high part shifted by the hint direction, modulo
    // the high count. The direction is plus one when the sign flag is set and
    // minus one otherwise, taken only when the hint is set.
    air.add_single_row(2, move |row| {
        let direction = row[pos].add(row[pos]).sub(Felt::ONE);
        row[r1u]
            .sub(row[r1])
            .sub(row[h].mul(direction))
            .add(high.mul(row[hi]))
            .sub(high.mul(row[lo]))
    });
    air.add_single_row(1, move |row| {
        recompose(row, base + COL_R1U_BITS, HIGH_BITS).sub(row[r1u])
    });

    // The high part range.
    for k in 0..HIGH_BITS {
        let col = base + COL_R1_BITS + k;
        air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
        let col = base + COL_R1U_BITS + k;
        air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
    }
    for start in [COL_R0S_BITS, COL_R0S_SLACK] {
        for k in 0..LOW_BITS {
            let col = base + start + k;
            air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
        }
    }
    for start in [COL_DPOS_BITS, COL_DPOS_SLACK] {
        for k in 0..POS_BITS {
            let col = base + start + k;
            air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
        }
    }
}

/// Builds the hint recovery description of the given length. The length must be
pub fn hint_air(length: usize) -> Air {
    let mut air = Air::new(WIDTH, length);
    add_constraints(&mut air, 0);
    air
}

fn set_bits(trace: &mut TraceTable, col: usize, row: usize, value: u64, bits: usize) {
    for k in 0..bits {
        trace.set(col + k, row, Felt::new((value >> k) & 1));
    }
}

/// Fills one hint recovery row at the given column base.
pub fn fill_row(trace: &mut TraceTable, base: usize, row: usize, r: u64, h: u64) {
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

    trace.set(base + COL_R, row, Felt::new(r));
    trace.set(base + COL_H, row, Felt::new(h));
    trace.set(base + COL_R1, row, Felt::new(r1));
    trace.set(base + COL_R0S, row, Felt::new(r0s));
    trace.set(base + COL_KC, row, Felt::new(kc));
    let inverse = if kc == 0 {
        Felt::new(r0s).inv()
    } else {
        Felt::ZERO
    };
    trace.set(base + COL_R0S_INV, row, inverse);
    trace.set(base + COL_POS, row, Felt::new(pos));
    trace.set(base + COL_DPOS, row, Felt::new(dpos));
    trace.set(base + COL_R1U, row, Felt::new(r1u));
    trace.set(base + COL_HI, row, Felt::new(hi));
    trace.set(base + COL_LO, row, Felt::new(lo));
    set_bits(trace, base + COL_R1_BITS, row, r1, HIGH_BITS);
    set_bits(trace, base + COL_R0S_BITS, row, r0s, LOW_BITS);
    set_bits(
        trace,
        base + COL_R0S_SLACK,
        row,
        ALPHA.wrapping_sub(r0s),
        LOW_BITS,
    );
    set_bits(trace, base + COL_DPOS_BITS, row, dpos, POS_BITS);
    set_bits(
        trace,
        base + COL_DPOS_SLACK,
        row,
        GAMMA2.wrapping_sub(dpos),
        POS_BITS,
    );
    set_bits(trace, base + COL_R1U_BITS, row, r1u, HIGH_BITS);
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
        fill_row(&mut trace, 0, row, r, h);
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
