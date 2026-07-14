//! Benchmark for the joined batch certificate of the module lattice verify
//! relation.
//!
//! It builds one joined trace over a batch of signatures, the transform domain
//! modular multiplication, the response norm, the commitment decomposition, and
//! the hint recovery, and proves it once. It reports the definitive proving time,
//! verification time, and proof size of the single certificate, together with an
//! honest statement of the pieces still proved separately.

use std::time::Instant;

use qtv_stark::batch::{batch_air, batch_trace, BATCH_WIDTH};
use qtv_stark::lattice::{
    signature_batch_workload, MATRIX_COLS, MATRIX_ROWS, PRODUCTS_PER_SIGNATURE, Q, RING_DEGREE,
};
use qtv_stark::norm::NORM_BOUND;
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

fn draw(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state % Q
}

fn main() {
    let signatures = 2;
    let params = StarkParams {
        lde_blowup: 8,
        num_queries: 32,
    };

    let products = signature_batch_workload(signatures, 0x5eed);

    let mut state = 0xa1b2u64 | 1;
    let response: Vec<u64> = (0..signatures * MATRIX_COLS * RING_DEGREE)
        .map(|_| {
            let m = draw(&mut state) % NORM_BOUND;
            if m & 1 == 0 {
                m
            } else {
                Q - m
            }
        })
        .collect();
    let commitment: Vec<u64> = (0..signatures * MATRIX_ROWS * RING_DEGREE)
        .map(|_| draw(&mut state))
        .collect();
    let hints: Vec<u64> = commitment.iter().map(|_| draw(&mut state) & 1).collect();

    let cert = batch_trace(&products, &response, &commitment, &hints);

    let prove_iters = 3;
    let start = Instant::now();
    let mut proof = prove(&cert.air, &cert.trace, &params);
    for _ in 1..prove_iters {
        proof = prove(&cert.air, &cert.trace, &params);
    }
    let prove_time = start.elapsed() / prove_iters;

    let verify_iters = 20;
    let start = Instant::now();
    let mut accepted = verify(&batch_air(cert.length), &params, &proof);
    for _ in 1..verify_iters {
        accepted = verify(&batch_air(cert.length), &params, &proof);
    }
    let verify_time = start.elapsed() / verify_iters;

    println!("joined batch certificate");
    println!("signatures {}", signatures);
    println!(
        "matrix {} rows {} columns, ring degree {}",
        MATRIX_ROWS, MATRIX_COLS, RING_DEGREE
    );
    println!(
        "products per signature {}, joined trace rows {}",
        PRODUCTS_PER_SIGNATURE, cert.length
    );
    println!("base columns {}", BATCH_WIDTH);
    println!("queries {}", params.num_queries);
    println!("blow up {}", params.lde_blowup);
    println!("proof bytes {}", proof_bytes(&proof));
    println!("proving time {:?}", prove_time);
    println!("verification time {:?}", verify_time);
    println!("accepted {}", accepted);
    println!();
    println!("joined pieces: modular multiplication, response norm, decomposition, hint recovery");
    println!("permutation join: the decomposition and the hint recovery share the commitment");
    println!("coefficient multiset, bound by the running product argument");
    println!();
    println!("the hashing joins the arithmetic under one proof in the fused certificate bench,");
    println!("which binds a SHAKE256 squeeze word to the coefficient the arithmetic consumes;");
    println!("the matrix rejection sampling, the challenge ball sampling, the multi block");
    println!("absorb, and the commitment and index encodings are arithmetized in their modules");
    println!();
    println!("proved separately, not in this per row band:");
    println!("  the full radix two transform keeps its butterfly network layout and its own");
    println!("  permutation wiring, so it does not share the per row band; its modular");
    println!("  multiplication core is the band joined here");
}
