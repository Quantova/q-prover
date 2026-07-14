//! FRI folding for the low degree test.
//!
//! The prover commits to an evaluation vector and folds it round by round using
//! a verifier challenge, until the remaining polynomial is a constant that can
//! be sent in the clear. Each fold halves the evaluation domain. The challenges
//! and the query positions are all drawn from SHA3 over the transcript, so the
//! protocol is non interactive.

use crate::field::{Felt, MODULUS};
use crate::merkle::Digest;
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
///
/// The pair is f at x and f at minus x. With x_inv the inverse of x the result
/// is the value at x squared of the folded polynomial even part plus challenge
/// times odd part.
pub fn fold_pair(low: Felt, high: Felt, challenge: Felt, x_inv: Felt) -> Felt {
    let inv_two = Felt::new(2).inv();
    let sum = low.add(high);
    let diff = low.sub(high);
    sum.add(challenge.mul(diff).mul(x_inv)).mul(inv_two)
}

/// Folds an evaluation vector by two using a single challenge.
///
/// The generator inverse is the inverse of the root of unity that spans the
/// current domain, so index i pairs with index i plus half as x with minus x.
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
///
/// The state is the digest of everything absorbed so far. Squeezing a challenge
/// also advances the state so that repeated draws differ.
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
}
