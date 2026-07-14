//! The proving interface for the hash based STARK backend.

use crate::field::Felt;
use crate::merkle::Digest;

/// A statement to be proven, given by its public inputs.
pub struct PublicInputs {
    /// The public field elements that fix the statement.
    pub values: Vec<Felt>,
}

/// A witness holding the private execution trace.
pub struct Witness {
    /// The private trace that satisfies the statement.
    pub trace: Vec<Felt>,
}

/// A proof carrying the commitments and the query openings.
pub struct Proof {
    /// The commitment root over the execution trace.
    pub trace_root: Digest,
    /// The commitment roots produced by each FRI round.
    pub fri_roots: Vec<Digest>,
    /// The field elements revealed at the sampled query positions.
    pub openings: Vec<Felt>,
}

/// The prover binds a witness to public inputs and emits a proof.
pub trait Prover {
    /// Produces a proof for the given statement and witness.
    fn prove(&self, public: &PublicInputs, witness: &Witness) -> Proof;
}
