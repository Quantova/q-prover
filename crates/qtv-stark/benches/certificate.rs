// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Benchmark for the fused certificate over the hashing and the per coefficient

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
    // In bound member responses, one per segment, standing in for the response
    // coefficients decoded from the member signatures.
    let responses: Vec<u64> = (0..perms as u64)
        .map(|i| (i * 40_009 + 1) % 500_000)
        .collect();

    let cert = certificate_trace(perms, message, &hints, &responses);

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
    println!("one certificate covers the SHAKE256 hashing band and the signature arithmetic band");
    println!("bound on each squeeze row, the reduction input equals the squeeze word, and the");
    println!("permutation binds the reduced coefficient to the decomposition, the hint recovery,");
    println!(
        "and the first factor of the matrix vector product, while a further permutation binds"
    );
    println!(
        "the product's second factor to the coefficient the response norm bounds, so the hash"
    );
    println!("to matrix coefficient to product to response to norm chain cannot be split");
    println!();
    println!("now inside the fused certificate, over the hash derived coefficients:");
    println!("  the transform domain matrix vector product of the coefficient with the response");
    println!("  the response infinity norm over the response the product multiplies");
    println!("  the canonical reduction, the commitment decomposition, and the hint recovery");
    println!();
    println!("still outside this certificate:");
    println!("  the batch is sixteen hash derived coefficients, one squeeze word per segment;");
    println!("  scaling to the full per signature coefficient count widens the arithmetic band");
    println!("  but keeps the shape");
    println!("  the hash derived coefficient is not reconstructed to the member matrix expansion,");
    println!(
        "  the decoded response, and the public key t1; the full verify equation closure, the"
    );
    println!(
        "  ExpandA rejection sampling to transform chain, the SampleInBall challenge, and the"
    );
    println!(
        "  multi block transcript absorb stay arithmetized in the sample, ntt, challenge ball,"
    );
    println!("  and sponge modules but are not fused here");
}
