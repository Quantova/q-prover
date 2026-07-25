// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Benchmark for one full number theoretic transform over the signature modulus.

use std::time::Instant;

use qtv_stark::lattice::Q;
use qtv_stark::ntt::{ntt_trace, to_layer_zero};
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
    let n: usize = 256;
    let coeffs: Vec<u64> = (0..n as u64)
        .map(|i| i.wrapping_mul(2654435769).wrapping_add(7) % Q)
        .collect();
    let instance = ntt_trace(&to_layer_zero(&coeffs));
    let params = StarkParams {
        lde_blowup: 8,
        num_queries: 32,
    };

    let prove_iters = 5;
    let start = Instant::now();
    let mut proof = prove(&instance.air, &instance.trace, &params);
    for _ in 1..prove_iters {
        proof = prove(&instance.air, &instance.trace, &params);
    }
    let prove_time = start.elapsed() / prove_iters;

    let verify_iters = 50;
    let start = Instant::now();
    let mut accepted = verify(&instance.air, &params, &proof);
    for _ in 1..verify_iters {
        accepted = verify(&instance.air, &params, &proof);
    }
    let verify_time = start.elapsed() / verify_iters;

    println!("ring degree {}", n);
    println!("layers {}", n.trailing_zeros());
    println!("butterflies {}", (n / 2) * n.trailing_zeros() as usize);
    println!("trace length {}", instance.trace.length());
    println!("base columns {}", instance.trace.width());
    println!("queries {}", params.num_queries);
    println!("proof bytes {}", proof_bytes(&proof));
    println!("proving time per proof {:?}", prove_time);
    println!("verification time per proof {:?}", verify_time);
    println!("accepted {}", accepted);
}
