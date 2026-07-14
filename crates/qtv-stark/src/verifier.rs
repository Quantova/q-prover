//! The verification interface for the hash based STARK backend.

use crate::fri::verify as fri_verify;
use crate::prover::{Proof, PublicInputs};

/// The verifier checks a proof against the public inputs without the witness.
pub trait Verifier {
    /// Returns true when the proof is accepted for the given statement.
    fn verify(&self, public: &PublicInputs, proof: &Proof) -> bool;
}

/// The FRI backed low degree verifier.
pub struct LowDegreeVerifier;

impl Verifier for LowDegreeVerifier {
    fn verify(&self, public: &PublicInputs, proof: &Proof) -> bool {
        fri_verify(&public.params, proof)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{root_of_unity, Felt};
    use crate::fri::FriParams;
    use crate::prover::{LowDegreeProver, Prover, Witness};

    fn eval_domain(coeffs: &[Felt], log_n: u32) -> Vec<Felt> {
        let n = 1usize << log_n;
        let omega = root_of_unity(log_n);
        let mut point = Felt::ONE;
        let mut out = Vec::with_capacity(n);
        for _ in 0..n {
            let mut acc = Felt::ZERO;
            for coeff in coeffs.iter().rev() {
                acc = acc.mul(point).add(*coeff);
            }
            out.push(acc);
            point = point.mul(omega);
        }
        out
    }

    #[test]
    fn a_low_degree_witness_round_trips_through_the_interfaces() {
        let params = FriParams {
            log_domain_size: 10,
            num_queries: 16,
            blowup: 4,
        };
        let coeffs: Vec<Felt> = (0..params.degree_bound() as u64).map(Felt::new).collect();
        let public = PublicInputs {
            params: params.clone(),
        };
        let witness = Witness {
            trace: eval_domain(&coeffs, params.log_domain_size),
        };
        let proof = LowDegreeProver.prove(&public, &witness);
        assert!(LowDegreeVerifier.verify(&public, &proof));
    }

    #[test]
    fn a_high_degree_witness_fails_the_interfaces() {
        let params = FriParams {
            log_domain_size: 10,
            num_queries: 16,
            blowup: 4,
        };
        let coeffs: Vec<Felt> = (0..params.domain_size() as u64).map(Felt::new).collect();
        let public = PublicInputs {
            params: params.clone(),
        };
        let witness = Witness {
            trace: eval_domain(&coeffs, params.log_domain_size),
        };
        let proof = LowDegreeProver.prove(&public, &witness);
        assert!(!LowDegreeVerifier.verify(&public, &proof));
    }
}
