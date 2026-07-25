// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT


use crate::air::{Air, TraceTable};
use crate::lattice::Q;
use crate::{decompose, hint, lattice, norm};

pub const MODMUL_BASE: usize = 0;
pub const NORM_BASE: usize = MODMUL_BASE + lattice::WIDTH;
pub const DECOMPOSE_BASE: usize = NORM_BASE + norm::WIDTH;
pub const HINT_BASE: usize = DECOMPOSE_BASE + decompose::WIDTH;
pub const BATCH_WIDTH: usize = HINT_BASE + hint::WIDTH;

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

pub struct BatchCertificate {
    pub air: Air,
    pub trace: TraceTable,
    pub length: usize,
}

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
            .map(|i| (i.wrapping_mul(2654435769) % Q, (i * 7 + 3) % Q))
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
        let commitment: Vec<u64> = (0..15u64).map(|i| i.wrapping_mul(332261) % Q).collect();
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
        let challenges = [Felt::new(20015998343868)];
        assert!(cert.air.is_satisfied_with(&cert.trace, &challenges));
    }

    #[test]
    fn a_mismatched_hint_coefficient_breaks_the_join() {
        let cert = sample_batch();
        let mut trace = cert.trace;
        let hint_r = HINT_BASE + hint::COL_R;
        trace.set(hint_r, 3, trace.get(hint_r, 3).add(Felt::new(5)));
        let challenges = [Felt::new(20015998343868)];
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
        trace.set(NORM_BASE + norm::COL_Z, 2, Felt::new(Q / 2));
        let proof = prove(&cert.air, &trace, &params());
        assert!(!verify(&batch_air(cert.length), &params(), &proof));
    }
}
