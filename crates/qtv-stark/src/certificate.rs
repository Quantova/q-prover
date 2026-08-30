// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::air::{Air, TraceTable};
use crate::field::Felt;
use crate::lattice::{Q, RESIDUE_BITS};
use crate::sponge::{lane_low_col, squeeze_row, SHAKE256_RATE, SPONGE_WIDTH};
use crate::{decompose, hint, lattice, norm, sponge};

const QUO_BITS: usize = 10;

const SQ_COL: usize = SPONGE_WIDTH;
const REDUCE_BASE: usize = SQ_COL + 1;
const R_V: usize = REDUCE_BASE;
const R_R: usize = REDUCE_BASE + 1;
const R_QUO: usize = REDUCE_BASE + 2;
const R_QUO_BITS: usize = REDUCE_BASE + 3;
const R_R_BITS: usize = R_QUO_BITS + QUO_BITS;
const R_SLACK_BITS: usize = R_R_BITS + RESIDUE_BITS;
const REDUCE_WIDTH: usize = 3 + QUO_BITS + 2 * RESIDUE_BITS;

pub const DECOMPOSE_BASE: usize = REDUCE_BASE + REDUCE_WIDTH;
pub const HINT_BASE: usize = DECOMPOSE_BASE + decompose::WIDTH;
pub const MODMUL_BASE: usize = HINT_BASE + hint::WIDTH;
pub const NORM_BASE: usize = MODMUL_BASE + lattice::WIDTH;
pub const CERT_WIDTH: usize = NORM_BASE + norm::WIDTH;

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

pub fn certificate_air(perms: usize, message: &[u8], output: &[u8]) -> Air {
    let rows = perms * sponge::SEGMENT_ROWS;
    let mut air = Air::new(CERT_WIDTH, rows);

    sponge::add_sponge_constraints(&mut air, SHAKE256_RATE, perms, message, output);

    let hot_rows: std::collections::HashSet<usize> = (0..perms).map(squeeze_row).collect();
    for global in 0..rows {
        let value = if hot_rows.contains(&global) {
            Felt::ONE
        } else {
            Felt::ZERO
        };
        air.add_boundary(SQ_COL, global, value);
    }

    let squeeze_col = lane_low_col(0);
    air.add_single_row(2, move |row| {
        row[SQ_COL].mul(row[R_V].sub(row[squeeze_col]))
    });
    air.add_single_row(2, move |row| Felt::ONE.sub(row[SQ_COL]).mul(row[R_V]));

    let modulus = Felt::new(Q);
    let modulus_minus_one = Felt::new(Q - 1);
    air.add_single_row(1, move |row| {
        row[R_V].sub(row[R_QUO].mul(modulus)).sub(row[R_R])
    });
    air.add_single_row(1, move |row| {
        recompose(row, R_QUO_BITS, QUO_BITS).sub(row[R_QUO])
    });
    air.add_single_row(1, move |row| {
        recompose(row, R_R_BITS, RESIDUE_BITS).sub(row[R_R])
    });
    air.add_single_row(1, move |row| {
        recompose(row, R_SLACK_BITS, RESIDUE_BITS).sub(modulus_minus_one.sub(row[R_R]))
    });
    for k in 0..QUO_BITS {
        let col = R_QUO_BITS + k;
        air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
    }
    for start in [R_R_BITS, R_SLACK_BITS] {
        for k in 0..RESIDUE_BITS {
            let col = start + k;
            air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
        }
    }

    decompose::add_constraints(&mut air, DECOMPOSE_BASE);
    hint::add_constraints(&mut air, HINT_BASE);
    lattice::add_constraints(&mut air, MODMUL_BASE);
    norm::add_constraints(&mut air, NORM_BASE);

    let gamma = air.add_challenge();
    let dec_r = DECOMPOSE_BASE + decompose::COL_R;
    let hint_r = HINT_BASE + hint::COL_R;
    let mm_a = MODMUL_BASE + lattice::COL_A;
    let mm_b = MODMUL_BASE + lattice::COL_B;
    let norm_z = NORM_BASE + norm::COL_Z;

    air.add_permutation(
        1,
        move |row, ch| ch[gamma].sub_base(row[R_R]),
        move |row, ch| ch[gamma].sub_base(row[dec_r]),
    );
    air.add_permutation(
        1,
        move |row, ch| ch[gamma].sub_base(row[R_R]),
        move |row, ch| ch[gamma].sub_base(row[hint_r]),
    );
    air.add_permutation(
        1,
        move |row, ch| ch[gamma].sub_base(row[R_R]),
        move |row, ch| ch[gamma].sub_base(row[mm_a]),
    );

    air.add_permutation(
        1,
        move |row, ch| ch[gamma].sub_base(row[mm_b]),
        move |row, ch| ch[gamma].sub_base(row[norm_z]),
    );

    air
}

pub struct Certificate {
    pub air: Air,
    pub trace: TraceTable,
    pub length: usize,
    pub output: Vec<u8>,
    pub coefficients: Vec<u64>,
}

fn set_bits(trace: &mut TraceTable, col: usize, row: usize, value: u64, bits: usize) {
    for k in 0..bits {
        trace.set(col + k, row, Felt::new((value >> k) & 1));
    }
}

pub fn certificate_trace(
    perms: usize,
    message: &[u8],
    hints: &[u64],
    responses: &[u64],
) -> Certificate {
    let rows = perms * sponge::SEGMENT_ROWS;
    let mut trace = TraceTable::new(CERT_WIDTH, rows);
    sponge::fill_sponge_columns(&mut trace, SHAKE256_RATE, perms, message);

    let mut coefficients = Vec::with_capacity(perms);
    for row in 0..rows {
        let (v, sq) = if let Some(j) = (0..perms).find(|&j| squeeze_row(j) == row) {
            (trace.get(lane_low_col(0), row).to_u64(), j)
        } else {
            (0, usize::MAX)
        };
        let r = v % Q;
        let quo = v / Q;
        trace.set(R_V, row, Felt::new(v));
        trace.set(R_R, row, Felt::new(r));
        trace.set(R_QUO, row, Felt::new(quo));
        set_bits(&mut trace, R_QUO_BITS, row, quo, QUO_BITS);
        set_bits(&mut trace, R_R_BITS, row, r, RESIDUE_BITS);
        set_bits(&mut trace, R_SLACK_BITS, row, Q - 1 - r, RESIDUE_BITS);
        if sq != usize::MAX {
            trace.set(SQ_COL, row, Felt::ONE);
            coefficients.push(r);
        }
        let h = if sq != usize::MAX {
            hints.get(sq).copied().unwrap_or(0) & 1
        } else {
            0
        };
        let z = if sq != usize::MAX {
            responses.get(sq).copied().unwrap_or(0) % Q
        } else {
            0
        };
        decompose::fill_row(&mut trace, DECOMPOSE_BASE, row, r);
        hint::fill_row(&mut trace, HINT_BASE, row, r, h);
        lattice::fill_row(&mut trace, MODMUL_BASE, row, r, z);
        norm::fill_row(&mut trace, NORM_BASE, row, z);
    }

    let output = sponge::shake_output(SHAKE256_RATE, perms, message);
    let air = certificate_air(perms, message, &output);
    Certificate {
        air,
        trace,
        length: rows,
        output,
        coefficients,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field_ext::Fp3;
    use crate::stark::{prove, verify, StarkParams};

    fn params() -> StarkParams {
        StarkParams {
            lde_blowup: 32,
            num_queries: 24,
        }
    }

    fn challenges() -> [Fp3; 1] {
        [Fp3::new(
            Felt::new(20015998343868),
            Felt::new(77),
            Felt::new(4242),
        )]
    }

    fn responses() -> Vec<u64> {
        vec![12_345, Q - 6_789]
    }

    fn sample() -> Certificate {
        let hints: Vec<u64> = (0..8u64).map(|i| i & 1).collect();
        certificate_trace(2, b"module lattice fused certificate", &hints, &responses())
    }

    #[test]
    fn the_coefficients_are_the_reduced_squeeze_words() {
        let cert = sample();
        assert_eq!(cert.coefficients.len(), 2);
        for (j, c) in cert.coefficients.iter().enumerate() {
            let word = cert.trace.get(lane_low_col(0), squeeze_row(j)).to_u64();
            assert_eq!(*c, word % Q);
            assert!(*c < Q);
        }
    }

    #[test]
    fn the_fused_arithmetic_holds() {
        let cert = sample();
        assert!(cert.air.is_satisfied_with(&cert.trace, &challenges()));
    }

    #[test]
    fn the_certificate_proves_and_verifies() {
        let cert = sample();
        let proof = prove(&cert.air, &cert.trace, &params());
        let air = certificate_air(2, b"module lattice fused certificate", &cert.output);
        assert!(verify(&air, &params(), &proof));
    }

    #[test]
    fn a_tampered_certificate_trace_is_rejected() {
        let cert = sample();
        let mut trace = cert.trace;
        let row = squeeze_row(0);
        trace.set(R_R, row, trace.get(R_R, row).add(Felt::ONE));
        let proof = prove(&cert.air, &trace, &params());
        let air = certificate_air(2, b"module lattice fused certificate", &cert.output);
        assert!(!verify(&air, &params(), &proof));
    }

    #[test]
    fn a_split_coefficient_breaks_the_binding() {
        let cert = sample();
        let mut trace = cert.trace;
        let dec_r = DECOMPOSE_BASE + decompose::COL_R;
        let row = squeeze_row(0);
        trace.set(dec_r, row, trace.get(dec_r, row).add(Felt::new(7)));
        assert!(!cert.air.is_satisfied_with(&trace, &challenges()));
    }

    #[test]
    fn a_tampered_reduction_is_rejected() {
        let cert = sample();
        let mut trace = cert.trace;
        let row = squeeze_row(1);
        trace.set(R_R, row, trace.get(R_R, row).add(Felt::ONE));
        assert!(!cert.air.is_satisfied_with(&trace, &challenges()));
    }

    #[test]
    fn a_proof_against_a_wrong_squeeze_is_rejected() {
        let cert = sample();
        let proof = prove(&cert.air, &cert.trace, &params());
        let mut wrong = cert.output.clone();
        wrong[0] ^= 1;
        let air = certificate_air(2, b"module lattice fused certificate", &wrong);
        assert!(!verify(&air, &params(), &proof));
    }

    #[test]
    fn the_product_multiplies_the_hash_coefficient_by_the_response() {
        let cert = sample();
        for j in 0..cert.coefficients.len() {
            let row = squeeze_row(j);
            let a = cert.trace.get(MODMUL_BASE + lattice::COL_A, row).to_u64();
            let r = cert.trace.get(R_R, row).to_u64();
            let b = cert.trace.get(MODMUL_BASE + lattice::COL_B, row).to_u64();
            let product = cert.trace.get(MODMUL_BASE + lattice::COL_R, row).to_u64();
            assert_eq!(a, r);
            assert_eq!(product, ((a as u128 * b as u128) % Q as u128) as u64);
        }
    }

    #[test]
    fn an_out_of_bound_response_has_no_satisfying_trace() {
        let hints: Vec<u64> = (0..8u64).map(|i| i & 1).collect();
        let cert = certificate_trace(2, b"module lattice fused certificate", &hints, &[Q / 2, 3]);
        assert!(!cert.air.is_satisfied_with(&cert.trace, &challenges()));
    }

    #[test]
    fn a_split_response_breaks_the_binding() {
        let cert = sample();
        let mut trace = cert.trace;
        let mm_b = MODMUL_BASE + lattice::COL_B;
        let row = squeeze_row(0);
        trace.set(mm_b, row, trace.get(mm_b, row).add(Felt::new(7)));
        assert!(!cert.air.is_satisfied_with(&trace, &challenges()));
    }
}
