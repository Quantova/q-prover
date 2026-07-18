//! Benchmark for the arithmetized part of the batch verify relation.

use std::time::Instant;

use qtv_stark::decompose::decompose_batch;
use qtv_stark::hint::hint_batch;
use qtv_stark::lattice::{
    modmul_batch, signature_batch_workload, MATRIX_COLS, MATRIX_ROWS, Q, RING_DEGREE,
};
use qtv_stark::norm::norm_batch;
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

struct Piece {
    name: &'static str,
    rows: usize,
    columns: usize,
    prove: std::time::Duration,
    verify: std::time::Duration,
    bytes: usize,
    accepted: bool,
}

fn measure<A>(
    name: &'static str,
    air: &qtv_stark::air::Air,
    trace: &qtv_stark::air::TraceTable,
    fresh_air: A,
    params: &StarkParams,
) -> Piece
where
    A: Fn() -> qtv_stark::air::Air,
{
    let start = Instant::now();
    let proof = prove(air, trace, params);
    let prove = start.elapsed();

    let verify_iters = 20;
    let start = Instant::now();
    let mut accepted = true;
    for _ in 0..verify_iters {
        accepted = verify(&fresh_air(), params, &proof);
    }
    let verify = start.elapsed() / verify_iters;

    Piece {
        name,
        rows: trace.length(),
        columns: trace.width(),
        prove,
        verify,
        bytes: proof_bytes(&proof),
        accepted,
    }
}

fn main() {
    let signatures = 4;
    let params = StarkParams {
        lde_blowup: 8,
        num_queries: 32,
    };

    // The transform domain modular multiplications of the matrix vector product.
    let modmul_work = signature_batch_workload(signatures, 24301);
    let modmul = modmul_batch(&modmul_work);
    let modmul_len = modmul.trace.length();

    // The response coefficients for the infinity norm check, one ring per matrix
    // column and signature.
    let mut state = 41394u64 | 1;
    let norm_count = signatures * MATRIX_COLS * RING_DEGREE;
    let norm_work: Vec<u64> = (0..norm_count)
        .map(|_| {
            let m = draw(&mut state) % qtv_stark::norm::NORM_BOUND;
            if m & 1 == 0 {
                m
            } else {
                Q - m
            }
        })
        .collect();
    let norm = norm_batch(&norm_work);
    let norm_len = norm.trace.length();

    // The commitment coefficients for the decomposition and the hint recovery,
    // one ring per matrix row and signature.
    let hint_count = signatures * MATRIX_ROWS * RING_DEGREE;
    let dec_work: Vec<u64> = (0..hint_count).map(|_| draw(&mut state)).collect();
    let decompose = decompose_batch(&dec_work);
    let dec_len = decompose.trace.length();
    let hint_work: Vec<(u64, u64)> = dec_work
        .iter()
        .map(|r| (*r, draw(&mut state) & 1))
        .collect();
    let hint = hint_batch(&hint_work);
    let hint_len = hint.trace.length();

    let pieces = [
        measure(
            "modular multiplication",
            &modmul.air,
            &modmul.trace,
            || qtv_stark::lattice::modmul_air(modmul_len),
            &params,
        ),
        measure(
            "response norm",
            &norm.air,
            &norm.trace,
            || qtv_stark::norm::norm_air(norm_len),
            &params,
        ),
        measure(
            "decomposition",
            &decompose.air,
            &decompose.trace,
            || qtv_stark::decompose::decompose_air(dec_len),
            &params,
        ),
        measure(
            "hint recovery",
            &hint.air,
            &hint.trace,
            || qtv_stark::hint::hint_air(hint_len),
            &params,
        ),
    ];

    println!("signatures {}", signatures);
    println!("matrix {} rows {} columns", MATRIX_ROWS, MATRIX_COLS);
    println!("ring degree {}", RING_DEGREE);
    println!();

    let mut total_prove = std::time::Duration::ZERO;
    let mut total_verify = std::time::Duration::ZERO;
    let mut total_bytes = 0usize;
    for piece in &pieces {
        println!(
            "{:<24} rows {:>6} columns {:>3} prove {:>10?} verify {:>10?} bytes {:>8} accepted {}",
            piece.name,
            piece.rows,
            piece.columns,
            piece.prove,
            piece.verify,
            piece.bytes,
            piece.accepted,
        );
        total_prove += piece.prove;
        total_verify += piece.verify;
        total_bytes += piece.bytes;
    }
    println!();
    println!("total proving time {:?}", total_prove);
    println!("total verification time {:?}", total_verify);
    println!("total proof bytes {}", total_bytes);
}
