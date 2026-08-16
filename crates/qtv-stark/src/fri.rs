// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT


use crate::field::{root_of_unity, Felt, MODULUS};
use crate::field_ext::Fp3;
use crate::merkle::{Digest, MerkleProof, MerkleTree};
use qtv_crypto::sha3::sha3_256;

// A field the FRI layers can live in. Folding, the codeword values and the
// folding challenges are drawn from this field; the evaluation-domain points
// and query positions stay in the base field.
pub trait FriField: Copy + PartialEq + core::fmt::Debug {
    const LIMBS: usize;

    fn zero() -> Self;
    fn add(self, other: Self) -> Self;
    fn sub(self, other: Self) -> Self;
    fn mul(self, other: Self) -> Self;
    // Multiply by a base-field scalar (domain points live in the base field).
    fn scale(self, scalar: Felt) -> Self;
    fn from_base(value: Felt) -> Self;

    fn sample(transcript: &mut Transcript) -> Self;
    fn absorb(self, transcript: &mut Transcript);
    fn hash_leaf(self) -> Digest;
    fn to_limbs(self) -> Vec<u64>;
    fn from_limbs(limbs: &[u64]) -> Self;
}

impl FriField for Felt {
    const LIMBS: usize = 1;

    fn zero() -> Self {
        Felt::ZERO
    }
    fn add(self, other: Self) -> Self {
        Felt::add(self, other)
    }
    fn sub(self, other: Self) -> Self {
        Felt::sub(self, other)
    }
    fn mul(self, other: Self) -> Self {
        Felt::mul(self, other)
    }
    fn scale(self, scalar: Felt) -> Self {
        Felt::mul(self, scalar)
    }
    fn from_base(value: Felt) -> Self {
        value
    }
    fn sample(transcript: &mut Transcript) -> Self {
        transcript.challenge_felt()
    }
    fn absorb(self, transcript: &mut Transcript) {
        transcript.absorb_felt(self);
    }
    fn hash_leaf(self) -> Digest {
        crate::merkle::hash_leaf(self)
    }
    fn to_limbs(self) -> Vec<u64> {
        vec![self.to_u64()]
    }
    fn from_limbs(limbs: &[u64]) -> Self {
        Felt::new(limbs[0])
    }
}

#[derive(Clone, Debug)]
pub struct FriParams {
    pub log_domain_size: u32,
    pub num_queries: usize,
    pub blowup: usize,
}

impl FriParams {
    pub fn domain_size(&self) -> usize {
        1usize << self.log_domain_size
    }

    pub fn rounds(&self) -> usize {
        (self.log_domain_size - self.blowup.trailing_zeros()) as usize
    }

    pub fn degree_bound(&self) -> usize {
        self.domain_size() / self.blowup
    }
}

pub fn fold_pair<F: FriField>(low: F, high: F, challenge: F, x_inv: Felt) -> F {
    let inv_two = Felt::new(2).inv();
    let sum = low.add(high);
    let diff = low.sub(high);
    sum.add(challenge.mul(diff).scale(x_inv)).scale(inv_two)
}

pub fn fold_layer<F: FriField>(evaluations: &[F], challenge: F, generator_inv: Felt) -> Vec<F> {
    let half = evaluations.len() / 2;
    let mut folded = Vec::with_capacity(half);
    let mut x_inv = Felt::ONE;
    for i in 0..half {
        let low = evaluations[i];
        let high = evaluations[i + half];
        folded.push(fold_pair(low, high, challenge, x_inv));
        x_inv = x_inv.mul(generator_inv);
    }
    folded
}

pub const PROTOCOL_TAG: &[u8] = b"QTV-STARK/v2";

pub struct Transcript {
    state: Digest,
}

impl Transcript {
    pub fn new() -> Self {
        Transcript { state: [0u8; 32] }
    }

    pub fn with_domain(context: &[u8]) -> Self {
        let mut transcript = Transcript::new();
        transcript.absorb(PROTOCOL_TAG);
        transcript.absorb(&(context.len() as u64).to_le_bytes());
        transcript.absorb(context);
        transcript
    }

    pub fn absorb(&mut self, bytes: &[u8]) {
        let mut preimage = Vec::with_capacity(32 + bytes.len());
        preimage.extend_from_slice(&self.state);
        preimage.extend_from_slice(bytes);
        self.state = sha3_256(&preimage);
    }

    pub fn absorb_digest(&mut self, digest: &Digest) {
        self.absorb(digest);
    }

    pub fn absorb_felt(&mut self, value: Felt) {
        self.absorb(&value.to_u64().to_le_bytes());
    }

    pub fn absorb_ext(&mut self, value: Fp3) {
        let mut bytes = [0u8; 24];
        for (i, limb) in value.to_u64s().iter().enumerate() {
            bytes[i * 8..i * 8 + 8].copy_from_slice(&limb.to_le_bytes());
        }
        self.absorb(&bytes);
    }

    fn squeeze(&mut self, domain: u8) -> Digest {
        let mut preimage = [0u8; 33];
        preimage[..32].copy_from_slice(&self.state);
        preimage[32] = domain;
        let out = sha3_256(&preimage);
        self.state = out;
        out
    }

    pub fn challenge_felt(&mut self) -> Felt {
        let out = self.squeeze(1);
        let mut wide: u128 = 0;
        for byte in &out[..16] {
            wide = (wide << 8) | (*byte as u128);
        }
        Felt::new((wide % (MODULUS as u128)) as u64)
    }

    // Sample a uniform element of the cubic extension by drawing three
    // independent base-field limbs from the transcript.
    pub fn challenge_ext(&mut self) -> Fp3 {
        let a0 = self.challenge_felt();
        let a1 = self.challenge_felt();
        let a2 = self.challenge_felt();
        Fp3::new(a0, a1, a2)
    }

    pub fn challenge_index(&mut self, bound: usize) -> usize {
        let out = self.squeeze(2);
        let mut wide: u64 = 0;
        for byte in &out[..8] {
            wide = (wide << 8) | (*byte as u64);
        }
        (wide % bound as u64) as usize
    }
}

impl Default for Transcript {
    fn default() -> Self {
        Transcript::new()
    }
}

pub struct QueryLayer<F: FriField> {
    pub eval: F,
    pub sibling: F,
    pub eval_path: MerkleProof,
    pub sibling_path: MerkleProof,
}

pub struct QueryProof<F: FriField> {
    pub position: usize,
    pub layers: Vec<QueryLayer<F>>,
}

pub struct FriProof<F: FriField> {
    pub layer_roots: Vec<Digest>,
    pub final_layer: Vec<F>,
    pub queries: Vec<QueryProof<F>>,
}

fn commit_layer<F: FriField>(values: &[F]) -> MerkleTree {
    let leaves: Vec<Digest> = values.iter().map(|v| v.hash_leaf()).collect();
    MerkleTree::commit(&leaves)
}

pub fn prove<F: FriField>(evaluations: &[F], params: &FriParams) -> FriProof<F> {
    let mut transcript = Transcript::with_domain(&[]);
    prove_with_domain(evaluations, params, &mut transcript)
}

pub fn prove_with_domain<F: FriField>(
    evaluations: &[F],
    params: &FriParams,
    transcript: &mut Transcript,
) -> FriProof<F> {
    let n = params.domain_size();
    assert_eq!(
        evaluations.len(),
        n,
        "evaluation vector must fill the domain"
    );
    assert!(
        params.blowup.is_power_of_two(),
        "blow up must be a power of two"
    );
    let rounds = params.rounds();
    assert!(rounds >= 1, "the schedule needs at least one fold");

    let mut layers: Vec<Vec<F>> = vec![evaluations.to_vec()];
    let mut trees: Vec<MerkleTree> = Vec::with_capacity(rounds);
    let mut layer_roots: Vec<Digest> = Vec::with_capacity(rounds);

    let first_tree = commit_layer(&layers[0]);
    transcript.absorb_digest(&first_tree.root());
    layer_roots.push(first_tree.root());
    trees.push(first_tree);

    let mut generator_inv = root_of_unity(params.log_domain_size).inv();
    let mut final_layer: Vec<F> = Vec::new();

    for round in 0..rounds {
        let challenge = F::sample(&mut *transcript);
        let folded = fold_layer(&layers[round], challenge, generator_inv);
        if round < rounds - 1 {
            let tree = commit_layer(&folded);
            transcript.absorb_digest(&tree.root());
            layer_roots.push(tree.root());
            trees.push(tree);
            layers.push(folded);
            generator_inv = generator_inv.mul(generator_inv);
        } else {
            for value in &folded {
                value.absorb(&mut *transcript);
            }
            final_layer = folded;
        }
    }

    let half_domain = n / 2;
    let mut queries = Vec::with_capacity(params.num_queries);
    for _ in 0..params.num_queries {
        let position = transcript.challenge_index(half_domain);
        let mut opened = Vec::with_capacity(rounds);
        for round in 0..rounds {
            let half = half_domain >> round;
            let index = position % half;
            let layer = &layers[round];
            opened.push(QueryLayer {
                eval: layer[index],
                sibling: layer[index + half],
                eval_path: trees[round].open(index),
                sibling_path: trees[round].open(index + half),
            });
        }
        queries.push(QueryProof {
            position,
            layers: opened,
        });
    }

    FriProof {
        layer_roots,
        final_layer,
        queries,
    }
}

pub fn verify<F: FriField>(params: &FriParams, proof: &FriProof<F>) -> bool {
    let mut transcript = Transcript::with_domain(&[]);
    verify_with_domain(params, proof, &mut transcript)
}

pub fn verify_with_domain<F: FriField>(
    params: &FriParams,
    proof: &FriProof<F>,
    transcript: &mut Transcript,
) -> bool {
    let n = params.domain_size();
    if !params.blowup.is_power_of_two() {
        return false;
    }
    let rounds = params.rounds();
    if rounds == 0
        || proof.layer_roots.len() != rounds
        || proof.final_layer.len() != params.blowup
        || proof.queries.len() != params.num_queries
    {
        return false;
    }

    let constant = proof.final_layer[0];
    if proof.final_layer.iter().any(|v| *v != constant) {
        return false;
    }

    transcript.absorb_digest(&proof.layer_roots[0]);
    let mut challenges = Vec::with_capacity(rounds);
    for round in 0..rounds {
        challenges.push(F::sample(&mut *transcript));
        if round < rounds - 1 {
            transcript.absorb_digest(&proof.layer_roots[round + 1]);
        } else {
            for value in &proof.final_layer {
                value.absorb(&mut *transcript);
            }
        }
    }

    let half_domain = n / 2;
    let mut positions = Vec::with_capacity(params.num_queries);
    for _ in 0..params.num_queries {
        positions.push(transcript.challenge_index(half_domain));
    }

    let mut generator_inv = Vec::with_capacity(rounds);
    let mut current = root_of_unity(params.log_domain_size).inv();
    for _ in 0..rounds {
        generator_inv.push(current);
        current = current.mul(current);
    }

    for (query, expected_position) in proof.queries.iter().zip(positions.iter()) {
        if query.position != *expected_position || query.layers.len() != rounds {
            return false;
        }
        for round in 0..rounds {
            let half = half_domain >> round;
            let index = query.position % half;
            let layer = &query.layers[round];

            if layer.eval_path.leaf_index != index || layer.sibling_path.leaf_index != index + half
            {
                return false;
            }
            if !crate::merkle::verify(
                &proof.layer_roots[round],
                &layer.eval.hash_leaf(),
                &layer.eval_path,
            ) {
                return false;
            }
            if !crate::merkle::verify(
                &proof.layer_roots[round],
                &layer.sibling.hash_leaf(),
                &layer.sibling_path,
            ) {
                return false;
            }

            let x_inv = generator_inv[round].pow(index as u64);
            let folded = fold_pair(layer.eval, layer.sibling, challenges[round], x_inv);

            if round < rounds - 1 {
                let next = &query.layers[round + 1];
                let half_next = half >> 1;
                let expected = if index < half_next {
                    next.eval
                } else {
                    next.sibling
                };
                if folded != expected {
                    return false;
                }
            } else if folded != proof.final_layer[index] {
                return false;
            }
        }
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::root_of_unity;

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

    // Extension-field low-degree extension of a polynomial with Fp3 coefficients.
    fn eval_poly_ext(coeffs: &[Fp3], point: Felt) -> Fp3 {
        let mut acc = Fp3::ZERO;
        for coeff in coeffs.iter().rev() {
            acc = acc.scale(point).add(*coeff);
        }
        acc
    }

    fn eval_domain_ext(coeffs: &[Fp3], log_n: u32) -> Vec<Fp3> {
        let n = 1usize << log_n;
        let omega = root_of_unity(log_n);
        let mut point = Felt::ONE;
        let mut out = Vec::with_capacity(n);
        for _ in 0..n {
            out.push(eval_poly_ext(coeffs, point));
            point = point.mul(omega);
        }
        out
    }

    #[test]
    fn folding_a_polynomial_matches_folding_its_coefficients() {
        let log_n = 6u32;
        let coeffs: Vec<Felt> = (1..=16u64).map(Felt::new).collect();
        let evals = eval_domain(&coeffs, log_n);

        let challenge = Felt::new(2882343476);
        let generator_inv = root_of_unity(log_n).inv();
        let folded = fold_layer(&evals, challenge, generator_inv);

        let mut folded_coeffs = Vec::with_capacity(coeffs.len() / 2);
        let mut i = 0;
        while i < coeffs.len() {
            let even = coeffs[i];
            let odd = coeffs[i + 1];
            folded_coeffs.push(even.add(challenge.mul(odd)));
            i += 2;
        }
        let expected = eval_domain(&folded_coeffs, log_n - 1);
        assert_eq!(folded, expected);
    }

    #[test]
    fn folding_a_constant_leaves_it_constant() {
        let log_n = 5u32;
        let coeffs = vec![Felt::new(42)];
        let evals = eval_domain(&coeffs, log_n);
        let generator_inv = root_of_unity(log_n).inv();
        let folded = fold_layer(&evals, Felt::new(7), generator_inv);
        assert!(folded.iter().all(|v| *v == Felt::new(42)));
    }

    #[test]
    fn distinct_challenge_draws_differ() {
        let mut transcript = Transcript::new();
        transcript.absorb(b"root");
        let first = transcript.challenge_felt();
        let second = transcript.challenge_felt();
        assert_ne!(first, second);
    }

    #[test]
    fn transcripts_are_deterministic() {
        let mut a = Transcript::new();
        let mut b = Transcript::new();
        a.absorb(b"same");
        b.absorb(b"same");
        assert_eq!(a.challenge_felt(), b.challenge_felt());
        assert_eq!(a.challenge_index(64), b.challenge_index(64));
    }

    #[test]
    fn extension_challenges_are_deterministic_and_full_width() {
        let mut a = Transcript::new();
        let mut b = Transcript::new();
        a.absorb(b"same ext seed");
        b.absorb(b"same ext seed");
        let x = a.challenge_ext();
        let y = b.challenge_ext();
        assert_eq!(x, y);
        // A transcript draw should exercise the whole extension, not just the base.
        assert!(!x.is_base());
        let z = a.challenge_ext();
        assert_ne!(x, z);
    }

    #[test]
    fn a_proof_has_the_scheduled_shape() {
        let params = FriParams {
            log_domain_size: 8,
            num_queries: 12,
            blowup: 4,
        };
        let coeffs: Vec<Felt> = (0..params.degree_bound() as u64).map(Felt::new).collect();
        let evals = eval_domain(&coeffs, params.log_domain_size);
        let proof = prove(&evals, &params);

        assert_eq!(proof.layer_roots.len(), params.rounds());
        assert_eq!(proof.final_layer.len(), params.blowup);
        assert_eq!(proof.queries.len(), params.num_queries);
        for query in &proof.queries {
            assert_eq!(query.layers.len(), params.rounds());
        }
        let constant = proof.final_layer[0];
        assert!(proof.final_layer.iter().all(|v| *v == constant));
    }

    fn sample_params() -> FriParams {
        FriParams {
            log_domain_size: 10,
            num_queries: 24,
            blowup: 8,
        }
    }

    #[test]
    fn a_low_degree_vector_is_accepted() {
        let params = sample_params();
        let coeffs: Vec<Felt> = (0..params.degree_bound() as u64)
            .map(|i| Felt::new(i.wrapping_mul(2654435769) ^ 81))
            .collect();
        let evals = eval_domain(&coeffs, params.log_domain_size);
        let proof = prove(&evals, &params);
        assert!(verify(&params, &proof));
    }

    #[test]
    fn a_high_degree_vector_is_rejected() {
        let params = sample_params();
        let coeffs: Vec<Felt> = (0..params.domain_size() as u64)
            .map(|i| Felt::new(i.wrapping_mul(3518319154) ^ 47))
            .collect();
        let evals = eval_domain(&coeffs, params.log_domain_size);
        let proof = prove(&evals, &params);
        assert!(!verify(&params, &proof));
    }

    #[test]
    fn a_tampered_opening_is_rejected() {
        let params = sample_params();
        let coeffs: Vec<Felt> = (0..params.degree_bound() as u64).map(Felt::new).collect();
        let evals = eval_domain(&coeffs, params.log_domain_size);
        let mut proof = prove(&evals, &params);
        proof.queries[0].layers[0].eval = proof.queries[0].layers[0].eval.add(Felt::ONE);
        assert!(!verify(&params, &proof));
    }

    #[test]
    fn a_forged_final_constant_is_rejected() {
        let params = sample_params();
        let coeffs: Vec<Felt> = (0..params.degree_bound() as u64).map(Felt::new).collect();
        let evals = eval_domain(&coeffs, params.log_domain_size);
        let mut proof = prove(&evals, &params);
        let last = proof.final_layer.len() - 1;
        proof.final_layer[last] = proof.final_layer[last].add(Felt::ONE);
        assert!(!verify(&params, &proof));
    }

    // The same FRI protocol run over the cubic extension field.
    #[test]
    fn an_extension_low_degree_vector_is_accepted() {
        let params = sample_params();
        let coeffs: Vec<Fp3> = (0..params.degree_bound() as u64)
            .map(|i| {
                Fp3::new(
                    Felt::new(i.wrapping_mul(2654435769) ^ 81),
                    Felt::new(i.wrapping_mul(40503) ^ 17),
                    Felt::new(i.wrapping_mul(2246822519) ^ 5),
                )
            })
            .collect();
        let evals = eval_domain_ext(&coeffs, params.log_domain_size);
        let proof = prove(&evals, &params);
        assert!(verify(&params, &proof));
    }

    #[test]
    fn an_extension_high_degree_vector_is_rejected() {
        let params = sample_params();
        let coeffs: Vec<Fp3> = (0..params.domain_size() as u64)
            .map(|i| {
                Fp3::new(
                    Felt::new(i.wrapping_mul(3518319154) ^ 47),
                    Felt::new(i.wrapping_mul(1013904223) ^ 9),
                    Felt::new(i.wrapping_mul(22695477) ^ 3),
                )
            })
            .collect();
        let evals = eval_domain_ext(&coeffs, params.log_domain_size);
        let proof = prove(&evals, &params);
        assert!(!verify(&params, &proof));
    }

    #[test]
    fn an_extension_tampered_opening_is_rejected() {
        let params = sample_params();
        let coeffs: Vec<Fp3> = (0..params.degree_bound() as u64)
            .map(|i| Fp3::from_base(Felt::new(i)))
            .collect();
        let evals = eval_domain_ext(&coeffs, params.log_domain_size);
        let mut proof = prove(&evals, &params);
        proof.queries[0].layers[0].eval = proof.queries[0].layers[0].eval.add(Fp3::ONE);
        assert!(!verify(&params, &proof));
    }

    #[test]
    fn a_context_seeded_transcript_diverges_from_the_bare_protocol_seed() {
        let bare = Transcript::with_domain(&[]).challenge_felt();
        let context = Transcript::with_domain(b"chain-7/corridor-2").challenge_felt();
        assert_ne!(bare, context);
    }

    #[test]
    fn a_low_degree_proof_under_one_context_is_rejected_under_another() {
        let params = sample_params();
        let coeffs: Vec<Felt> = (0..params.degree_bound() as u64).map(Felt::new).collect();
        let evals = eval_domain(&coeffs, params.log_domain_size);
        let proof = prove_with_domain(&evals, &params, &mut Transcript::with_domain(b"chain-a/corridor-x"));
        assert!(verify_with_domain(&params, &proof, &mut Transcript::with_domain(b"chain-a/corridor-x")));
        assert!(!verify_with_domain(&params, &proof, &mut Transcript::with_domain(b"chain-b/corridor-x")));
        assert!(!verify_with_domain(&params, &proof, &mut Transcript::with_domain(b"chain-a/corridor-y")));
    }

    #[test]
    fn an_extension_folding_challenge_lives_in_the_extension() {
        // Sanity check that the FRI folding challenge for the Fp3 instance is
        // a genuine extension element (not accidentally reduced to the base).
        let mut transcript = Transcript::new();
        transcript.absorb_digest(&[9u8; 32]);
        let challenge = <Fp3 as FriField>::sample(&mut transcript);
        assert!(!challenge.is_base());
    }
}
