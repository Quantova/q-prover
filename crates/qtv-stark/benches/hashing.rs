// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::time::Instant;

use qtv_stark::hashing::{
    challenge_hash, matrix_entries, matrix_entry_hash, matrix_entry_perms, MU_BYTES,
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

struct Report {
    name: &'static str,
    rows: usize,
    columns: usize,
    prove: std::time::Duration,
    verify: std::time::Duration,
    bytes: usize,
    accepted: bool,
}

fn measure<F>(name: &'static str, build: F, params: &StarkParams) -> Report
where
    F: Fn() -> qtv_stark::sponge::SpongeInstance,
{
    let instance = build();
    let prove_iters = 3;
    let start = Instant::now();
    let mut proof = prove(&instance.air, &instance.trace, params);
    for _ in 1..prove_iters {
        proof = prove(&instance.air, &instance.trace, params);
    }
    let prove = start.elapsed() / prove_iters;

    let verify_iters = 20;
    let start = Instant::now();
    let mut accepted = verify(&instance.air, params, &proof);
    for _ in 1..verify_iters {
        accepted = verify(&instance.air, params, &proof);
    }
    let verify = start.elapsed() / verify_iters;

    Report {
        name,
        rows: instance.trace.length(),
        columns: instance.trace.width(),
        prove,
        verify,
        bytes: proof_bytes(&proof),
        accepted,
    }
}

fn main() {
    let params = StarkParams {
        lde_blowup: 32,
        num_queries: 32,
    };

    let mut rho = [0u8; 32];
    for (i, b) in rho.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(37).wrapping_add(1);
    }
    let mut digest = vec![0u8; MU_BYTES];
    for (i, b) in digest.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(29).wrapping_add(7);
    }

    let reports = [
        measure(
            "matrix entry expansion",
            || matrix_entry_hash(&rho, 2, 3),
            &params,
        ),
        measure("challenge squeeze", || challenge_hash(&digest), &params),
    ];

    println!("matrix entries in the expansion {}", matrix_entries());
    println!("matrix entry squeeze permutations {}", matrix_entry_perms());
    println!();
    for r in &reports {
        println!(
            "{:<24} rows {:>4} columns {:>4} prove {:>12?} verify {:>10?} bytes {:>8} accepted {}",
            r.name, r.rows, r.columns, r.prove, r.verify, r.bytes, r.accepted,
        );
    }
}
