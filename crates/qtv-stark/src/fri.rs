//! FRI folding for the low degree test.

use crate::field::Felt;

/// Parameters that fix the FRI schedule.
pub struct FriParams {
    /// The base two logarithm of the initial evaluation domain size.
    pub log_domain_size: usize,
    /// The number of query openings that back the soundness argument.
    pub num_queries: usize,
    /// The blow up factor of the low degree extension.
    pub blowup: usize,
}

/// Folds an evaluation vector by two using a single challenge.
pub fn fold_once(evaluations: &[Felt], challenge: Felt) -> Vec<Felt> {
    let half = evaluations.len() / 2;
    let mut folded = Vec::with_capacity(half);
    for i in 0..half {
        let low = evaluations[i];
        let high = evaluations[i + half];
        folded.push(low.add(challenge.mul(high)));
    }
    folded
}

/// Folds an evaluation vector down to the final small polynomial, drawing one
pub fn fold_all(mut evaluations: Vec<Felt>, challenges: &[Felt]) -> Vec<Felt> {
    for challenge in challenges {
        if evaluations.len() <= 1 {
            break;
        }
        evaluations = fold_once(&evaluations, *challenge);
    }
    evaluations
}
