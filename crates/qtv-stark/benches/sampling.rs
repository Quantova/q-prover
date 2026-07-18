//! Benchmark for the arithmetized sampling steps of the batch verify relation.

use std::time::Instant;

use qtv_crypto::sha3::{shake128, shake256};
use qtv_stark::challenge_ball::{ball_air, ball_batch, BALL_BUFFER_BYTES};
use qtv_stark::encode::{encode_air, encode_batch};
use qtv_stark::sample::{rej_air, rej_batch, REJ_BUFFER_BYTES};
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

fn report(
    name: &str,
    air: &qtv_stark::air::Air,
    trace: &qtv_stark::air::TraceTable,
    verifier: qtv_stark::air::Air,
    params: &StarkParams,
) {
    let prove_iters = 5;
    let start = Instant::now();
    let mut proof = prove(air, trace, params);
    for _ in 1..prove_iters {
        proof = prove(air, trace, params);
    }
    let prove_time = start.elapsed() / prove_iters;

    let verify_iters = 50;
    let start = Instant::now();
    let mut accepted = verify(&verifier, params, &proof);
    for _ in 1..verify_iters {
        accepted = verify(&verifier, params, &proof);
    }
    let verify_time = start.elapsed() / verify_iters;

    println!("{}", name);
    println!("  rows {} columns {}", air.length(), air.base_width());
    println!("  proof bytes {}", proof_bytes(&proof));
    println!("  proving time {:?}", prove_time);
    println!("  verification time {:?}", verify_time);
    println!("  accepted {}", accepted);
}

fn main() {
    let params = StarkParams {
        lde_blowup: 8,
        num_queries: 32,
    };

    let mut rho = [0u8; 32];
    for (i, b) in rho.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(37).wrapping_add(1);
    }
    let mut seed = Vec::with_capacity(34);
    seed.extend_from_slice(&rho);
    seed.push(2);
    seed.push(3);
    let mut rej_stream = vec![0u8; REJ_BUFFER_BYTES];
    shake128(&seed, &mut rej_stream);
    let rej = rej_batch(&rej_stream);
    report(
        "matrix rejection sampling",
        &rej.air,
        &rej.trace,
        rej_air(rej.trace.length()),
        &params,
    );
    println!();

    let mut c_tilde = [0u8; 48];
    for (i, b) in c_tilde.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(53).wrapping_add(11);
    }
    let mut ball_stream = vec![0u8; BALL_BUFFER_BYTES];
    shake256(&c_tilde, &mut ball_stream);
    let ball = ball_batch(&ball_stream);
    report(
        "challenge ball position sampling",
        &ball.air,
        &ball.trace,
        ball_air(ball.trace.length()),
        &params,
    );
    println!();

    let highs: Vec<u8> = (0..256u16)
        .map(|i| (i.wrapping_mul(7) & 15) as u8)
        .collect();
    let enc = encode_batch(&highs);
    report(
        "commitment high bit packing",
        &enc.air,
        &enc.trace,
        encode_air(enc.trace.length()),
        &params,
    );
}
