//! The proving interface for the hash based STARK backend.

use crate::field::Felt;
use crate::fri::{prove as fri_prove, FriParams};

/// A proof that a committed evaluation vector is close to a low degree
pub use crate::fri::FriProof as Proof;

/// The public part of the low degree statement.
pub struct PublicInputs {
    /// The FRI schedule the proof commits to.
    pub params: FriParams,
}

/// A witness holding the evaluation vector under test.
pub struct Witness {
    /// The evaluations over the initial domain.
    pub trace: Vec<Felt>,
}

/// The prover binds a witness to public inputs and emits a proof.
pub trait Prover {
    /// Produces a proof for the given statement and witness.
    fn prove(&self, public: &PublicInputs, witness: &Witness) -> Proof;
}

/// The FRI backed low degree prover.
pub struct LowDegreeProver;

impl Prover for LowDegreeProver {
    fn prove(&self, public: &PublicInputs, witness: &Witness) -> Proof {
        fri_prove(&witness.trace, &public.params)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_prover_emits_a_proof_over_the_full_domain() {
        let params = FriParams {
            log_domain_size: 8,
            num_queries: 8,
            blowup: 4,
        };
        let trace = vec![Felt::new(3); params.domain_size()];
        let public = PublicInputs {
            params: params.clone(),
        };
        let witness = Witness { trace };
        let proof = LowDegreeProver.prove(&public, &witness);
        assert_eq!(proof.layer_roots.len(), params.rounds());
        assert_eq!(proof.queries.len(), params.num_queries);
    }
}
