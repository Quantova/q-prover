//! Benchmark for the general proof over the worked example.
//!
//! It arithmetizes a squaring chain, proves it, and reports proving time,
//! verification time, and proof size at a representative trace length.

use std::time::Instant;

use qtv_stark::examples::squaring_chain;
use qtv_stark::field::Felt;
use qtv_stark::stark::{prove, verify, StarkParams, StarkProof};

fn merkle_bytes(proof: &qtv_stark::merkle::MerkleProof) -> usize {
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
    let log_length = 12;
    let params = StarkParams {
        lde_blowup: 8,
        num_queries: 32,
    };
    let chain = squaring_chain(log_length, Felt::new(3));

    let prove_iters = 20;
    let start = Instant::now();
    let mut proof = prove(&chain.air, &chain.trace, &params);
    for _ in 1..prove_iters {
        proof = prove(&chain.air, &chain.trace, &params);
    }
    let prove_time = start.elapsed() / prove_iters;

    let verify_iters = 200;
    let start = Instant::now();
    let mut accepted = verify(&chain.air, &params, &proof);
    for _ in 1..verify_iters {
        accepted = verify(&chain.air, &params, &proof);
    }
    let verify_time = start.elapsed() / verify_iters;

    println!("trace length {}", 1usize << log_length);
    println!("trace columns {}", chain.trace.width());
    println!("queries {}", params.num_queries);
    println!("proof bytes {}", proof_bytes(&proof));
    println!("proving time per proof {:?}", prove_time);
    println!("verification time per proof {:?}", verify_time);
    println!("accepted {}", accepted);
}
