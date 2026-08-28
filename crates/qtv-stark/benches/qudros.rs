// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::time::Instant;

use qtv_stark::qudros::{qudros_air, qudros_trace, LANES};
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
    let mut input = [0u64; LANES];
    for (i, lane) in input.iter_mut().enumerate() {
        *lane = (i as u64)
            .wrapping_mul(81985529216486895)
            .wrapping_add(3735928559);
    }
    let instance = qudros_trace(&input);
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

    let verify_iters = 20;
    let air = qudros_air(&input, &instance.output);
    let start = Instant::now();
    let mut accepted = verify(&air, &params, &proof);
    for _ in 1..verify_iters {
        accepted = verify(&air, &params, &proof);
    }
    let verify_time = start.elapsed() / verify_iters;

    println!("qudros f permutation");
    println!("rounds proved 24 in trace rows {}", instance.trace.length());
    println!("base columns {}", instance.trace.width());
    println!("queries {}", params.num_queries);
    println!("blow up {}", params.lde_blowup);
    println!("proof bytes {}", proof_bytes(&proof));
    println!("proving time per proof {:?}", prove_time);
    println!("verification time per proof {:?}", verify_time);
    println!("accepted {}", accepted);
}
