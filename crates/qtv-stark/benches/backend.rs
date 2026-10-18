// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::time::Instant;

use qtv_stark::field::{root_of_unity, Felt};
use qtv_stark::field_ext::Fp3;
use qtv_stark::fri::{prove, verify, FriParams};

fn eval_poly(coeffs: &[Felt], point: Felt) -> Felt {
    let mut acc = Felt::ZERO;
    for coeff in coeffs.iter().rev() {
        acc = acc.mul(point).add(*coeff);
    }
    acc
}

fn eval_domain(coeffs: &[Felt], log_n: u32) -> Vec<Felt> {
    let n = 1usize << log_n;
    let omega = root_of_unity(log_n);
    let mut point = Felt::ONE;
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        out.push(eval_poly(coeffs, point));
        point = point.mul(omega);
    }
    out
}

fn proof_bytes(proof: &qtv_stark::fri::FriProof<Fp3>) -> usize {
    let mut total = proof.layer_roots.len() * 32;
    total += proof.final_layer.len() * 24;
    for query in &proof.queries {
        total += 8;
        for layer in &query.layers {
            total += 48;
            total += (layer.eval_path.siblings.len() + layer.sibling_path.siblings.len()) * 32;
        }
    }
    total
}

fn main() {
    let params = FriParams {
        log_domain_size: 16,
        num_queries: 160,
        blowup: 8,
    };

    let degree = 256;
    let coeffs: Vec<Felt> = (0..degree)
        .map(|i| Felt::new((i as u64).wrapping_mul(11400714819323198485) ^ 305419896))
        .collect();
    let evals: Vec<Fp3> = eval_domain(&coeffs, params.log_domain_size)
        .into_iter()
        .map(Fp3::from_base)
        .collect();

    let prove_iters = 20;
    let start = Instant::now();
    let mut proof = prove(&evals, &params);
    for _ in 1..prove_iters {
        proof = prove(&evals, &params);
    }
    let prove_time = start.elapsed() / prove_iters;

    let verify_iters = 200;
    let start = Instant::now();
    let mut accepted = verify(&params, &proof);
    assert!(
        accepted,
        "the benchmark proof must verify under the soundness floor"
    );
    for _ in 1..verify_iters {
        accepted = verify(&params, &proof);
    }
    let verify_time = start.elapsed() / verify_iters;

    println!("domain size {}", params.domain_size());
    println!("degree bound {}", params.degree_bound());
    println!("folding rounds {}", params.rounds());
    println!("queries {}", params.num_queries);
    println!("proof bytes {}", proof_bytes(&proof));
    println!("proving time per proof {:?}", prove_time);
    println!("verification time per proof {:?}", verify_time);
    println!("accepted {}", accepted);
}
