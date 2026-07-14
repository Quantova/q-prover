//! Benchmark harness skeleton for the qtv-stark backend.
//!
//! It measures proving time and verification time. This data must exist before
//! the consensus design is frozen, so the harness is stood up now over a trivial
//! backend and grows as the real prover lands.

use std::time::Instant;

use qtv_stark::field::Felt;
use qtv_stark::merkle::Digest;
use qtv_stark::prover::{Proof, Prover, PublicInputs, Witness};
use qtv_stark::verifier::Verifier;

/// A trivial backend that exercises the interfaces so the harness compiles and
/// reports timings.
struct Backend;

impl Prover for Backend {
    fn prove(&self, public: &PublicInputs, witness: &Witness) -> Proof {
        let mut acc = Felt::ZERO;
        for value in &witness.trace {
            acc = acc.add(*value);
        }
        for value in &public.values {
            acc = acc.add(*value);
        }
        let mut trace_root: Digest = [0u8; 32];
        trace_root[..8].copy_from_slice(&acc.to_u64().to_le_bytes());
        Proof {
            trace_root,
            fri_roots: Vec::new(),
            openings: vec![acc],
        }
    }
}

impl Verifier for Backend {
    fn verify(&self, _public: &PublicInputs, proof: &Proof) -> bool {
        !proof.openings.is_empty()
    }
}

fn main() {
    let public = PublicInputs {
        values: (0..16).map(Felt::new).collect(),
    };
    let witness = Witness {
        trace: (0..1024).map(Felt::new).collect(),
    };
    let backend = Backend;
    let rounds: u32 = 1000;

    let start = Instant::now();
    let mut proof = backend.prove(&public, &witness);
    for _ in 1..rounds {
        proof = backend.prove(&public, &witness);
    }
    let prove_time = start.elapsed() / rounds;

    let start = Instant::now();
    let mut accepted = backend.verify(&public, &proof);
    for _ in 1..rounds {
        accepted = backend.verify(&public, &proof);
    }
    let verify_time = start.elapsed() / rounds;

    println!("proving time per proof {:?}", prove_time);
    println!("verification time per proof {:?}", verify_time);
    println!("accepted {}", accepted);
}
