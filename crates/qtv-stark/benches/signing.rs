//! Benchmark for the FIPS 204 signing derivation with a zero randomizer.

use std::time::Instant;

use qtv_stark::merkle::MerkleProof;
use qtv_stark::signing::{signing_jobs, Job, AVG_ITERATIONS_MILLI};
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

// One measured piece, its cost and the multiplicities that place it in the loop.
struct Measured {
    name: &'static str,
    rows: usize,
    columns: usize,
    per_iteration: usize,
    per_draw: usize,
    prove_secs: f64,
    verify_secs: f64,
    bytes: usize,
}

fn measure(job: &Job) -> Measured {
    let params = StarkParams {
        lde_blowup: job.blowup,
        num_queries: job.queries,
    };

    // The hashing pieces carry the degree eleven qudros transition and are the
    // heaviest, so they are proved once; the lighter arithmetic pieces are averaged
    // over a few runs.
    let heavy = job.blowup >= 32 || job.rows >= 8192;
    let prove_iters = if heavy { 1 } else { 3 };
    let verify_iters = if heavy { 5 } else { 20 };

    let start = Instant::now();
    let mut proof = prove(&job.prover, &job.trace, &params);
    for _ in 1..prove_iters {
        proof = prove(&job.prover, &job.trace, &params);
    }
    let prove_secs = start.elapsed().as_secs_f64() / prove_iters as f64;

    let start = Instant::now();
    let mut accepted = verify(&job.verifier, &params, &proof);
    for _ in 1..verify_iters {
        accepted = verify(&job.verifier, &params, &proof);
    }
    let verify_secs = start.elapsed().as_secs_f64() / verify_iters as f64;
    assert!(accepted, "the piece {} did not verify", job.name);

    Measured {
        name: job.name,
        rows: job.rows,
        columns: job.columns,
        per_iteration: job.per_iteration,
        per_draw: job.per_draw,
        prove_secs,
        verify_secs,
        bytes: proof_bytes(&proof),
    }
}

fn main() {
    let jobs = signing_jobs();
    println!("FIPS 204 signing derivation with a zero randomizer, ML DSA 65");
    println!("measured on this host in release, each distinct piece once");
    println!();
    println!("per piece cost and its multiplicity in one signing iteration:");
    println!(
        "  {:<48} {:>6} {:>5} {:>6} {:>6} {:>11} {:>11} {:>10}",
        "piece", "rows", "cols", "x/iter", "x/draw", "prove", "verify", "bytes"
    );

    let mut measured = Vec::new();
    for job in &jobs {
        let m = measure(job);
        println!(
            "  {:<48} {:>6} {:>5} {:>6} {:>6} {:>9.3}s {:>9.2}ms {:>10}",
            m.name,
            m.rows,
            m.columns,
            m.per_iteration,
            m.per_draw,
            m.prove_secs,
            m.verify_secs * 1e3,
            m.bytes,
        );
        measured.push(m);
    }

    // The accepted iteration, the sum of each piece times its per iteration count.
    let iter_prove: f64 = measured
        .iter()
        .map(|m| m.prove_secs * m.per_iteration as f64)
        .sum();
    let iter_verify: f64 = measured
        .iter()
        .map(|m| m.verify_secs * m.per_iteration as f64)
        .sum();
    let iter_bytes: f64 = measured
        .iter()
        .map(|m| m.bytes as f64 * m.per_iteration as f64)
        .sum();

    // The per draw pieces run once outside the loop, the seed derivation.
    let draw_once_prove: f64 = measured
        .iter()
        .map(|m| m.prove_secs * m.per_draw as f64)
        .sum();
    let draw_once_verify: f64 = measured
        .iter()
        .map(|m| m.verify_secs * m.per_draw as f64)
        .sum();
    let draw_once_bytes: f64 = measured
        .iter()
        .map(|m| m.bytes as f64 * m.per_draw as f64)
        .sum();

    let avg_iterations = AVG_ITERATIONS_MILLI as f64 / 1000.0;
    let rejected = avg_iterations - 1.0;

    // The full derandomization proof for one draw, the seed derivation once plus
    // the average number of full iterations, since a rejected iteration performs
    // the same computation as the accepted one and its rejection must also be
    // proved.
    let draw_prove = draw_once_prove + iter_prove * avg_iterations;
    let draw_verify = draw_once_verify + iter_verify * avg_iterations;
    let draw_bytes = draw_once_bytes + iter_bytes * avg_iterations;

    let slot_secs = 0.150;
    let iter_slots = (iter_prove / slot_secs).ceil() as u64;
    let draw_slots = (draw_prove / slot_secs).ceil() as u64;

    println!();
    println!("one accepted iteration, the mask expansion, the matrix product, the");
    println!("challenge, the response, and the norm checks, arithmetized end to end:");
    println!("  prove  {:.3} s", iter_prove);
    println!("  verify {:.1} ms", iter_verify * 1e3);
    println!("  bytes  {:.0} ({:.2} MB)", iter_bytes, iter_bytes / 1.0e6);
    println!();
    println!("seed derivation rho_pp, once per draw, with the randomizer pinned to zero:");
    println!("  prove  {:.3} s", draw_once_prove);
    println!("  verify {:.1} ms", draw_once_verify * 1e3);
    println!("  bytes  {:.0}", draw_once_bytes);
    println!();
    println!(
        "average signing loop iterations for ML DSA 65: {:.1}",
        avg_iterations
    );
    println!(
        "so about {:.1} iterations are rejected before the accepted one",
        rejected
    );
    println!();
    println!("each rejected iteration performs the same measured computation as the");
    println!("accepted one and its rejection must be proved, so it adds one iteration cost:");
    println!(
        "  additional prove per rejected iteration  {:.3} s",
        iter_prove
    );
    println!(
        "  additional verify per rejected iteration {:.1} ms",
        iter_verify * 1e3
    );
    println!(
        "  rejected iterations add about {:.3} s prove and {:.1} ms verify in total",
        iter_prove * rejected,
        iter_verify * rejected * 1e3
    );
    println!();
    println!(
        "full derandomization proof for one draw, seed once plus {:.1} iterations:",
        avg_iterations
    );
    println!("  prove  {:.3} s", draw_prove);
    println!("  verify {:.1} ms", draw_verify * 1e3);
    println!("  bytes  {:.0} ({:.2} MB)", draw_bytes, draw_bytes / 1.0e6);
    println!();
    println!("lookahead depth the prove time forces, at a 150 ms slot:");
    println!(
        "  one accepted iteration forces {} slots of lead time",
        iter_slots
    );
    println!(
        "  the full per draw proof forces {} slots of lead time",
        draw_slots
    );
    println!();
    println!("is the verify affordable on the 150 ms critical path?");
    let iter_ok = iter_verify < slot_secs;
    let draw_ok = draw_verify < slot_secs;
    println!(
        "  one accepted iteration verify {:.1} ms: {}",
        iter_verify * 1e3,
        if iter_ok {
            "under 150 ms, affordable"
        } else {
            "over 150 ms, NOT affordable"
        }
    );
    println!(
        "  full per draw verify {:.1} ms: {}",
        draw_verify * 1e3,
        if draw_ok {
            "under 150 ms, affordable"
        } else {
            "over 150 ms, NOT affordable"
        }
    );
    println!();
    println!("these are separate proofs whose costs sum; folding them into one succinct");
    println!("proof by the recursion layer is the step that would put a single small verify");
    println!("on the critical path, and that recursion is not measured here.");
}
