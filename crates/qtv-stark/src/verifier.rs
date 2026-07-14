//! The verification interface for the hash based STARK backend.

use crate::prover::{Proof, PublicInputs};

/// The verifier checks a proof against the public inputs without the witness.
pub trait Verifier {
    /// Returns true when the proof is accepted for the given statement.
    fn verify(&self, public: &PublicInputs, proof: &Proof) -> bool;
}
