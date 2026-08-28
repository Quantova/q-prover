// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::field::Felt;
use crate::fri::{prove as fri_prove, FriParams};

pub type Proof = crate::fri::FriProof<Felt>;

pub struct PublicInputs {
    pub params: FriParams,
}

pub struct Witness {
    pub trace: Vec<Felt>,
}

pub trait Prover {
    fn prove(&self, public: &PublicInputs, witness: &Witness) -> Proof;
}

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
