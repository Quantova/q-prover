//! The joined batch certificate over the module lattice verify relation.
//!
//! The arithmetized pieces are placed side by side in one trace, the transform
//! domain modular multiplication, the response infinity norm, the commitment
//! decomposition, and the hint recovery, each in its own column band. A single
//! proof over the joined trace is one certificate for the whole batch.
//!
//! The permutation argument that is already in place joins two of the pieces. The
//! decomposition and the hint recovery both act on the commitment coefficients,
//! so the argument binds the multiset of coefficients the decomposition consumes
//! to the multiset the hint recovery consumes. A prover that fed different
//! coefficients to the two pieces could not close the running product.
//!
//! What is joined here is the per coefficient field arithmetic of the relation.
//! What remains proved separately, and why, is stated honestly in the batch
//! benchmark: the full radix two transform keeps its own butterfly network layout
//! and its own permutation wiring, so it does not share this per row band; and the
//! two hashing steps keep the sponge layout of row chained permutations, which is
//! a different trace shape and length, and their rejection sampling and multi
//! block absorb are not yet arithmetized.

use crate::air::{Air, TraceTable};
use crate::lattice::Q;
use crate::{decompose, hint, lattice, norm};

/// The column base of the modular multiplication band.
pub const MODMUL_BASE: usize = 0;
/// The column base of the response norm band.
pub const NORM_BASE: usize = MODMUL_BASE + lattice::WIDTH;
/// The column base of the decomposition band.
pub const DECOMPOSE_BASE: usize = NORM_BASE + norm::WIDTH;
/// The column base of the hint recovery band.
pub const HINT_BASE: usize = DECOMPOSE_BASE + decompose::WIDTH;
/// The joined base column width, before the permutation auxiliary column.
pub const BATCH_WIDTH: usize = HINT_BASE + hint::WIDTH;

/// Builds the joined description of the given length. The length must be a power
/// of two. The four pieces are laid in their bands and the permutation argument
/// binds the decomposition coefficient to the hint recovery coefficient.
pub fn batch_air(length: usize) -> Air {
    let mut air = Air::new(BATCH_WIDTH, length);
    lattice::add_constraints(&mut air, MODMUL_BASE);
    norm::add_constraints(&mut air, NORM_BASE);
    decompose::add_constraints(&mut air, DECOMPOSE_BASE);
    hint::add_constraints(&mut air, HINT_BASE);

    let gamma = air.add_challenge();
    let dec_r = DECOMPOSE_BASE + decompose::COL_R;
    let hint_r = HINT_BASE + hint::COL_R;
    air.add_permutation(
        1,
        move |row, ch| ch[gamma].sub(row[dec_r]),
        move |row, ch| ch[gamma].sub(row[hint_r]),
    );

    air
}

/// A joined batch certificate trace with its description.
pub struct BatchCertificate {
    /// The joined description shared with the verifier.
    pub air: Air,
    /// The filled base trace.
    pub trace: TraceTable,
    /// The power of two row count.
    pub length: usize,
}

/// Lays out the joined trace over the batch workloads. The modular products, the
/// response coefficients, the commitment coefficients, and the hint bits are each
/// padded with zeros to a common power of two length. The commitment coefficients
/// feed both the decomposition and the hint recovery, which is what the
/// permutation argument binds.
pub fn batch_trace(
    products: &[(u64, u64)],
    response: &[u64],
    commitment: &[u64],
    hints: &[u64],
) -> BatchCertificate {
    let count = products
        .len()
        .max(response.len())
        .max(commitment.len())
        .max(1);
    let length = count.next_power_of_two().max(2);
    let mut trace = TraceTable::new(BATCH_WIDTH, length);

    for row in 0..length {
        let (a, b) = if row < products.len() {
            products[row]
        } else {
            (0, 0)
        };
        lattice::fill_row(&mut trace, MODMUL_BASE, row, a % Q, b % Q);

        let z = if row < response.len() {
            response[row] % Q
        } else {
            0
        };
        norm::fill_row(&mut trace, NORM_BASE, row, z);

        let r = if row < commitment.len() {
            commitment[row] % Q
        } else {
            0
        };
        decompose::fill_row(&mut trace, DECOMPOSE_BASE, row, r);

        let h = if row < hints.len() { hints[row] & 1 } else { 0 };
        hint::fill_row(&mut trace, HINT_BASE, row, r, h);
    }

    BatchCertificate {
        air: batch_air(length),
        trace,
        length,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::Felt;
    use crate::stark::{prove, verify, StarkParams};

    fn params() -> StarkParams {
        StarkParams {
            lde_blowup: 8,
            num_queries: 24,
        }
    }

    fn sample_batch() -> BatchCertificate {
        let products: Vec<(u64, u64)> = (0..20u64)
            .map(|i| (i.wrapping_mul(0x9e37_79b9) % Q, (i * 7 + 3) % Q))
            .collect();
        let response: Vec<u64> = (0..12u64)
            .map(|i| {
                let m = i.wrapping_mul(37) % norm::NORM_BOUND;
                if i % 2 == 0 {
                    m
                } else {
                    Q - m
                }
            })
            .collect();
        let commitment: Vec<u64> = (0..15u64).map(|i| i.wrapping_mul(0x0051_1e5) % Q).collect();
        let hints: Vec<u64> = (0..15u64).map(|i| i & 1).collect();
        batch_trace(&products, &response, &commitment, &hints)
    }

    #[test]
    fn the_joined_arithmetic_holds() {
        let cert = sample_batch();
        assert!(cert.air.is_satisfied(&cert.trace));
    }

    #[test]
    fn the_permutation_binds_the_shared_coefficients() {
        let cert = sample_batch();
        let challenges = [Felt::new(0x1234_5678_9abc)];
        assert!(cert.air.is_satisfied_with(&cert.trace, &challenges));
    }

    #[test]
    fn a_mismatched_hint_coefficient_breaks_the_join() {
        let cert = sample_batch();
        let mut trace = cert.trace;
        // Change the hint recovery coefficient on one row so the decomposition and
        // the hint act on different multisets. The running product cannot close.
        let hint_r = HINT_BASE + hint::COL_R;
        trace.set(hint_r, 3, trace.get(hint_r, 3).add(Felt::new(5)));
        let challenges = [Felt::new(0x1234_5678_9abc)];
        assert!(!cert.air.is_satisfied_with(&trace, &challenges));
    }

    #[test]
    fn the_certificate_proves_and_verifies() {
        let cert = sample_batch();
        let proof = prove(&cert.air, &cert.trace, &params());
        assert!(verify(&batch_air(cert.length), &params(), &proof));
    }

    #[test]
    fn a_tampered_certificate_is_rejected() {
        let cert = sample_batch();
        let mut trace = cert.trace;
        // Break a norm magnitude so the response band no longer holds.
        trace.set(NORM_BASE + norm::COL_Z, 2, Felt::new(Q / 2));
        let proof = prove(&cert.air, &trace, &params());
        assert!(!verify(&batch_air(cert.length), &params(), &proof));
    }
}
