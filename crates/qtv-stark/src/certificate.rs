//! The fused certificate over the hashing and the per member signature verify

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

/// The column base of the commitment decomposition band.
pub const DECOMPOSE_BASE: usize = REDUCE_BASE + REDUCE_WIDTH;
/// The column base of the hint recovery band.
pub const HINT_BASE: usize = DECOMPOSE_BASE + decompose::WIDTH;
/// The column base of the transform domain matrix vector product band.
pub const MODMUL_BASE: usize = HINT_BASE + hint::WIDTH;
/// The column base of the response infinity norm band.
pub const NORM_BASE: usize = MODMUL_BASE + lattice::WIDTH;
/// The full base column width of the fused certificate.
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

/// Builds the fused description over a public message hashed for the given number
pub fn certificate_air(perms: usize, message: &[u8], output: &[u8]) -> Air {
    let rows = perms * sponge::SEGMENT_ROWS;
    let mut air = Air::new(CERT_WIDTH, rows);

    // The hashing band, the SHAKE256 squeeze.
    sponge::add_sponge_constraints(&mut air, SHAKE256_RATE, perms, message, output);

    // The squeeze selector, one on each squeeze row and zero elsewhere.
    for global in 0..rows {
        let hot = (0..perms).any(|j| squeeze_row(j) == global);
        let value = if hot { Felt::ONE } else { Felt::ZERO };
        air.add_boundary(SQ_COL, global, value);
    }

    // The reduction input equals the squeeze word on a squeeze row and is zero
    // elsewhere, so the coefficient is bound to the hash output.
    let squeeze_col = lane_low_col(0);
    air.add_single_row(2, move |row| {
        row[SQ_COL].mul(row[R_V].sub(row[squeeze_col]))
    });
    air.add_single_row(2, move |row| Felt::ONE.sub(row[SQ_COL]).mul(row[R_V]));

    // The reduction, the squeeze word is the quotient times the modulus plus the
    // coefficient, with the quotient below its bound and the coefficient below the
    // modulus.
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

    // The per coefficient signature verify pieces over the reduced coefficient:
    // the commitment decomposition, the hint recovery, the transform domain matrix
    // vector product, and the response infinity norm.
    decompose::add_constraints(&mut air, DECOMPOSE_BASE);
    hint::add_constraints(&mut air, HINT_BASE);
    lattice::add_constraints(&mut air, MODMUL_BASE);
    norm::add_constraints(&mut air, NORM_BASE);

    // One transcript challenge drives every binding permutation. Each binds one
    // multiset of trace cells to another so a value written in one band is the
    // value consumed in another.
    let gamma = air.add_challenge();
    let dec_r = DECOMPOSE_BASE + decompose::COL_R;
    let hint_r = HINT_BASE + hint::COL_R;
    let mm_a = MODMUL_BASE + lattice::COL_A;
    let mm_b = MODMUL_BASE + lattice::COL_B;
    let norm_z = NORM_BASE + norm::COL_Z;

    // The reduced coefficient is the decomposition input, the hint recovery input,
    // and the matrix coefficient the product multiplies, so all three pieces act on
    // the hash derived value.
    air.add_permutation(
        1,
        move |row, ch| ch[gamma].sub(row[R_R]),
        move |row, ch| ch[gamma].sub(row[dec_r]),
    );
    air.add_permutation(
        1,
        move |row, ch| ch[gamma].sub(row[R_R]),
        move |row, ch| ch[gamma].sub(row[hint_r]),
    );
    air.add_permutation(
        1,
        move |row, ch| ch[gamma].sub(row[R_R]),
        move |row, ch| ch[gamma].sub(row[mm_a]),
    );

    // The second factor of the product is the response the norm band bounds, so the
    // response the product multiplies is exactly the one proved small.
    air.add_permutation(
        1,
        move |row, ch| ch[gamma].sub(row[mm_b]),
        move |row, ch| ch[gamma].sub(row[norm_z]),
    );

    air
}

/// A filled fused certificate with its description and the squeeze output.
pub struct Certificate {
    /// The joined description shared with the verifier.
    pub air: Air,
    /// The filled base trace.
    pub trace: TraceTable,
    /// The power of two row count.
    pub length: usize,
    /// The squeeze output bytes.
    pub output: Vec<u8>,
    /// The hash derived coefficients the arithmetic consumes, one per segment.
    pub coefficients: Vec<u64>,
}

fn set_bits(trace: &mut TraceTable, col: usize, row: usize, value: u64, bits: usize) {
    for k in 0..bits {
        trace.set(col + k, row, Felt::new((value >> k) & 1));
    }
}

/// Lays out the fused trace. The sponge squeezes the message for the given number
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
        // The response coefficient this segment carries, zero off a squeeze row so
        // the product and the norm are the trivial zero relation there.
        let z = if sq != usize::MAX {
            responses.get(sq).copied().unwrap_or(0) % Q
        } else {
            0
        };
        decompose::fill_row(&mut trace, DECOMPOSE_BASE, row, r);
        hint::fill_row(&mut trace, HINT_BASE, row, r, h);
        // The matrix vector product of the hash derived coefficient with the
        // response, and the response norm over the same response.
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
    use crate::stark::{prove, verify, StarkParams};

    fn params() -> StarkParams {
        StarkParams {
            lde_blowup: 32,
            num_queries: 24,
        }
    }

    fn challenges() -> [Felt; 1] {
        [Felt::new(0x1234_5678_9abc)]
    }

    // Two responses inside the ML DSA 65 response bound, one small positive and one
    // the negative representative below the modulus, so the norm band holds.
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
    fn a_split_coefficient_breaks_the_binding() {
        // Feed the decomposition a coefficient other than the reduced squeeze word.
        // The permutation binding the reduced coefficient to the decomposition input
        // can no longer close.
        let cert = sample();
        let mut trace = cert.trace;
        let dec_r = DECOMPOSE_BASE + decompose::COL_R;
        let row = squeeze_row(0);
        trace.set(dec_r, row, trace.get(dec_r, row).add(Felt::new(7)));
        assert!(!cert.air.is_satisfied_with(&trace, &challenges()));
    }

    #[test]
    fn a_tampered_reduction_is_rejected() {
        // Claim a different coefficient for a squeeze word without changing the
        // squeeze. The reduction relation no longer holds.
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
        // On each squeeze row the product's first factor is the hash derived
        // coefficient and its residue is that coefficient times the response.
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
        // A response at the modulus over two is as far from zero as a coefficient
        // reaches, well outside the response bound, so the norm band cannot hold and
        // the fused trace has no satisfying assignment.
        let hints: Vec<u64> = (0..8u64).map(|i| i & 1).collect();
        let cert = certificate_trace(2, b"module lattice fused certificate", &hints, &[Q / 2, 3]);
        assert!(!cert.air.is_satisfied_with(&cert.trace, &challenges()));
    }

    #[test]
    fn a_split_response_breaks_the_binding() {
        // Feed the product a second factor other than the response the norm bounds.
        // The permutation binding the product factor to the norm input can no longer
        // close.
        let cert = sample();
        let mut trace = cert.trace;
        let mm_b = MODMUL_BASE + lattice::COL_B;
        let row = squeeze_row(0);
        trace.set(mm_b, row, trace.get(mm_b, row).add(Felt::new(7)));
        assert!(!cert.air.is_satisfied_with(&trace, &challenges()));
    }
}
