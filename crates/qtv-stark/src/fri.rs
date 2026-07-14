//! FRI folding for the low degree test.

use crate::field::{root_of_unity, Felt, MODULUS};
use crate::merkle::{hash_leaf, Digest, MerkleProof, MerkleTree};
use qtv_crypto::sha3::sha3_256;

/// Parameters that fix the FRI schedule.
#[derive(Clone, Debug)]
pub struct FriParams {
    /// The base two logarithm of the initial evaluation domain size.
    pub log_domain_size: u32,
    /// The number of query openings that back the soundness argument.
    pub num_queries: usize,
    /// The blow up factor of the low degree extension. Must be a power of two.
    pub blowup: usize,
}

impl FriParams {
    /// The initial evaluation domain size.
    pub fn domain_size(&self) -> usize {
        1usize << self.log_domain_size
    }

    /// The number of folding rounds, one per halving down to the blow up size.
    pub fn rounds(&self) -> usize {
        (self.log_domain_size - self.blowup.trailing_zeros()) as usize
    }

    /// The exclusive degree bound the test enforces on the committed vector.
    pub fn degree_bound(&self) -> usize {
        self.domain_size() / self.blowup
    }
}

/// Combines a pair of sibling evaluations into a single folded evaluation.
pub fn fold_pair(low: Felt, high: Felt, challenge: Felt, x_inv: Felt) -> Felt {
    let inv_two = Felt::new(2).inv();
    let sum = low.add(high);
    let diff = low.sub(high);
    sum.add(challenge.mul(diff).mul(x_inv)).mul(inv_two)
}

/// Folds an evaluation vector by two using a single challenge.
pub fn fold_layer(evaluations: &[Felt], challenge: Felt, generator_inv: Felt) -> Vec<Felt> {
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

/// A running SHA3 transcript for the Fiat Shamir challenges.
pub struct Transcript {
    state: Digest,
}

impl Transcript {
    /// Starts an empty transcript.
    pub fn new() -> Self {
        Transcript { state: [0u8; 32] }
    }

    /// Binds a byte string into the transcript state.
    pub fn absorb(&mut self, bytes: &[u8]) {
        let mut preimage = Vec::with_capacity(32 + bytes.len());
        preimage.extend_from_slice(&self.state);
        preimage.extend_from_slice(bytes);
        self.state = sha3_256(&preimage);
    }

    /// Binds a digest into the transcript state.
    pub fn absorb_digest(&mut self, digest: &Digest) {
        self.absorb(digest);
    }

    /// Binds a field element into the transcript state.
    pub fn absorb_felt(&mut self, value: Felt) {
        self.absorb(&value.to_u64().to_le_bytes());
    }

    fn squeeze(&mut self, domain: u8) -> Digest {
        let mut preimage = [0u8; 33];
        preimage[..32].copy_from_slice(&self.state);
        preimage[32] = domain;
        let out = sha3_256(&preimage);
        self.state = out;
        out
    }

    /// Draws a field element challenge.
    pub fn challenge_felt(&mut self) -> Felt {
        let out = self.squeeze(0x01);
        let mut wide: u128 = 0;
        for byte in &out[..16] {
            wide = (wide << 8) | (*byte as u128);
        }
        Felt::new((wide % (MODULUS as u128)) as u64)
    }

    /// Draws an index below the given bound.
    pub fn challenge_index(&mut self, bound: usize) -> usize {
        let out = self.squeeze(0x02);
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

/// One opened sibling pair inside a single folding layer.
pub struct QueryLayer {
    /// The value at the queried position.
    pub eval: Felt,
    /// The value at the paired position half a domain away.
    pub sibling: Felt,
    /// The authentication path for the queried value.
    pub eval_path: MerkleProof,
    /// The authentication path for the paired value.
    pub sibling_path: MerkleProof,
}

/// The openings that back one query across all folding layers.
pub struct QueryProof {
    /// The sampled position in the first folded domain.
    pub position: usize,
    /// The opened pair at each folding layer.
    pub layers: Vec<QueryLayer>,
}

/// A low degree proof over a committed evaluation vector.
pub struct FriProof {
    /// The Merkle roots of the committed folding layers.
    pub layer_roots: Vec<Digest>,
    /// The final folded layer, a constant vector sent in the clear.
    pub final_layer: Vec<Felt>,
    /// The query openings that tie the layers together.
    pub queries: Vec<QueryProof>,
}

fn commit_layer(values: &[Felt]) -> MerkleTree {
    let leaves: Vec<Digest> = values.iter().map(|v| hash_leaf(*v)).collect();
    MerkleTree::commit(&leaves)
}

/// Produces a low degree proof that the evaluation vector is close to a
pub fn prove(evaluations: &[Felt], params: &FriParams) -> FriProof {
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

    let mut transcript = Transcript::new();
    let mut layers: Vec<Vec<Felt>> = vec![evaluations.to_vec()];
    let mut trees: Vec<MerkleTree> = Vec::with_capacity(rounds);
    let mut layer_roots: Vec<Digest> = Vec::with_capacity(rounds);

    let first_tree = commit_layer(&layers[0]);
    transcript.absorb_digest(&first_tree.root());
    layer_roots.push(first_tree.root());
    trees.push(first_tree);

    let mut generator_inv = root_of_unity(params.log_domain_size).inv();
    let mut final_layer: Vec<Felt> = Vec::new();

    for round in 0..rounds {
        let challenge = transcript.challenge_felt();
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
                transcript.absorb_felt(*value);
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

/// Checks a low degree proof against the FRI schedule.
pub fn verify(params: &FriParams, proof: &FriProof) -> bool {
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

    let mut transcript = Transcript::new();
    transcript.absorb_digest(&proof.layer_roots[0]);
    let mut challenges = Vec::with_capacity(rounds);
    for round in 0..rounds {
        challenges.push(transcript.challenge_felt());
        if round < rounds - 1 {
            transcript.absorb_digest(&proof.layer_roots[round + 1]);
        } else {
            for value in &proof.final_layer {
                transcript.absorb_felt(*value);
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
                &hash_leaf(layer.eval),
                &layer.eval_path,
            ) {
                return false;
            }
            if !crate::merkle::verify(
                &proof.layer_roots[round],
                &hash_leaf(layer.sibling),
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

    #[test]
    fn folding_a_polynomial_matches_folding_its_coefficients() {
        let log_n = 6u32;
        let coeffs: Vec<Felt> = (1..=16u64).map(Felt::new).collect();
        let evals = eval_domain(&coeffs, log_n);

        let challenge = Felt::new(0xabcd_1234);
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
            .map(|i| Felt::new(i.wrapping_mul(0x9e37_79b9) ^ 0x51))
            .collect();
        let evals = eval_domain(&coeffs, params.log_domain_size);
        let proof = prove(&evals, &params);
        assert!(verify(&params, &proof));
    }

    #[test]
    fn a_high_degree_vector_is_rejected() {
        let params = sample_params();
        let coeffs: Vec<Felt> = (0..params.domain_size() as u64)
            .map(|i| Felt::new(i.wrapping_mul(0xd1b5_4a32) ^ 0x2f))
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
}
