// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::time::Instant;

use qtv_stark::sponge::{shake_air, shake_trace, SHAKE256_RATE};
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
    let message = b"quantova sponge benchmark seed";
    let perms = 4;
    let rate = SHAKE256_RATE;
    let instance = shake_trace(rate, perms, message);
    let params = StarkParams {
        lde_blowup: 32,
        num_queries: 32,
    };

    let prove_iters = 3;
    let start = Instant::now();
    let mut proof = prove(&instance.air, &instance.trace, &params);
    for _ in 1..prove_iters {
        proof = prove(&instance.air, &instance.trace, &params);
    }
    let prove_time = start.elapsed() / prove_iters;

    let air = shake_air(rate, perms, message, &instance.output);
    let verify_iters = 20;
    let start = Instant::now();
    let mut accepted = verify(&air, &params, &proof);
    for _ in 1..verify_iters {
        accepted = verify(&air, &params, &proof);
    }
    let verify_time = start.elapsed() / verify_iters;

    println!("shake256 squeeze");
    println!("rate bytes {}", rate);
    println!("permutations {}", perms);
    println!("squeeze bytes {}", instance.output.len());
    println!("trace rows {}", instance.trace.length());
    println!("base columns {}", instance.trace.width());
    println!("queries {}", params.num_queries);
    println!("blow up {}", params.lde_blowup);
    println!("proof bytes {}", proof_bytes(&proof));
    println!("proving time per proof {:?}", prove_time);
    println!("verification time per proof {:?}", verify_time);
    println!("accepted {}", accepted);
}
