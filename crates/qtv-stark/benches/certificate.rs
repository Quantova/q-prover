//! Benchmark for the fused certificate over the hashing and the per coefficient
//! arithmetic.
//!
//! It builds one flat trace that hashes a message with SHAKE256 and, on each
//! squeeze segment, reduces the squeeze word into a coefficient below the modulus
//! and runs the commitment decomposition and the hint recovery over it. A single
//! proof covers the hashing and the arithmetic together, bound so the coefficient
//! the arithmetic consumes is the word the hash produced. The benchmark reports the
//! definitive proving time, verification time, and proof size of that one
//! certificate, together with an honest statement of what still stands apart.

use std::time::Instant;

use qtv_stark::certificate::{certificate_air, certificate_trace, CERT_WIDTH};
use qtv_stark::merkle::MerkleProof;
use qtv_stark::sponge::SEGMENT_ROWS;
use qtv_stark::stark::{prove, verify, StarkParams, StarkProof};

fn merkle_bytes(proof: &MerkleProof) -> usize {
    8 + proof.siblings.len() * 32
}

fn proof_bytes(proof: &StarkProof) -> usize {
    let mut total = 64;
    total += proof.fri.layer_roots.len() * 32;
    total += proof.fri.final_layer.len() * 8;
    for query in &proof.fri.queries {
        total += 8;
        for layer in &query.layers {
            total += 16;
            total += merkle_bytes(&layer.eval_path) + merkle_bytes(&layer.sibling_path);
        }
    }
    for opening in &proof.openings {
        for row in &opening.rows {
            total += 8;
            total += row.values.len() * 8;
            total += merkle_bytes(&row.path) + merkle_bytes(&row.aux_path);
        }
    }
    total
}

fn main() {
    let perms = 16;
    let params = StarkParams {
        lde_blowup: 32,
        num_queries: 32,
    };
    let message = b"quantova fused certificate batch";
    let hints: Vec<u64> = (0..perms as u64).map(|i| i & 1).collect();

    let cert = certificate_trace(perms, message, &hints);

    let prove_iters = 3;
    let start = Instant::now();
    let mut proof = prove(&cert.air, &cert.trace, &params);
    for _ in 1..prove_iters {
        proof = prove(&cert.air, &cert.trace, &params);
    }
    let prove_time = start.elapsed() / prove_iters;

    let air = certificate_air(perms, message, &cert.output);
    let verify_iters = 20;
    let start = Instant::now();
    let mut accepted = verify(&air, &params, &proof);
    for _ in 1..verify_iters {
        accepted = verify(&air, &params, &proof);
    }
    let verify_time = start.elapsed() / verify_iters;

    println!("fused certificate over hashing and per coefficient arithmetic");
    println!(
        "segments {}, coefficients {}",
        perms,
        cert.coefficients.len()
    );
    println!(
        "trace rows {}, base columns {}",
        perms * SEGMENT_ROWS,
        CERT_WIDTH
    );
    println!(
        "queries {}, blow up {}",
        params.num_queries, params.lde_blowup
    );
    println!("proof bytes {}", proof_bytes(&proof));
    println!("proving time {:?}", prove_time);
    println!("verification time {:?}", verify_time);
    println!("accepted {}", accepted);
    println!();
    println!("one certificate covers the SHAKE256 hashing band and the arithmetic band");
    println!("bound on each squeeze row, the reduction input equals the squeeze word, and the");
    println!("permutation binds the reduced coefficient to the decomposition and the hint");
    println!("recovery, so the hash output the arithmetic consumes cannot be split from it");
    println!();
    println!("still outside this certificate:");
    println!("  the batch is sixteen hash derived coefficients, one squeeze word per segment;");
    println!("  scaling to the full per signature coefficient count widens the arithmetic band");
    println!("  but keeps the shape");
    println!("  the modular multiplication and the response norm bands consume the transform");
    println!("  outputs and the response, which are not products of this hash, so they join the");
    println!("  arithmetic certificate without a hash binding");
    println!("  the squeeze word reduces modulo the modulus here; the faithful rejection");
    println!("  sampling of the matrix expansion is arithmetized in the sample module and binds");
    println!("  the same way");
}
