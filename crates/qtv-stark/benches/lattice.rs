// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Benchmark for the batch module lattice verification core.

use std::time::Instant;

use qtv_stark::lattice::{
    modmul_air, modmul_batch, signature_batch_workload, PRODUCTS_PER_SIGNATURE,
};
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
    let signatures = 1;
    let workload = signature_batch_workload(signatures, 24301);
    let batch = modmul_batch(&workload);
    let length = batch.trace.length();
    let air = modmul_air(length);
    let params = StarkParams {
        lde_blowup: 8,
        num_queries: 32,
    };

    let prove_iters = 5;
    let start = Instant::now();
    let mut proof = prove(&batch.air, &batch.trace, &params);
    for _ in 1..prove_iters {
        proof = prove(&batch.air, &batch.trace, &params);
    }
    let prove_time = start.elapsed() / prove_iters;

    let verify_iters = 50;
    let start = Instant::now();
    let mut accepted = verify(&air, &params, &proof);
    for _ in 1..verify_iters {
        accepted = verify(&air, &params, &proof);
    }
    let verify_time = start.elapsed() / verify_iters;

    println!("signatures {}", signatures);
    println!("products per signature {}", PRODUCTS_PER_SIGNATURE);
    println!("modular multiplications {}", batch.count);
    println!("trace length {}", length);
    println!("trace columns {}", batch.trace.width());
    println!("queries {}", params.num_queries);
    println!("proof bytes {}", proof_bytes(&proof));
    println!("proving time per proof {:?}", prove_time);
    println!("verification time per proof {:?}", verify_time);
    println!("accepted {}", accepted);
}
