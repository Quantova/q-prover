//! Worked computations for the proof protocol.

use crate::air::{Air, TraceTable};
use crate::field::Felt;

/// A squaring chain together with its description and public values.
pub struct SquaringChain {
    /// The algebraic description of the chain.
    pub air: Air,
    /// The filled trace.
    pub trace: TraceTable,
    /// The pinned first value.
    pub seed: Felt,
    /// The pinned last value.
    pub output: Felt,
}

/// Builds a squaring chain whose length is two to the log length. The running
pub fn squaring_chain(log_length: u32, seed: Felt) -> SquaringChain {
    let length = 1usize << log_length;
    let mut trace = TraceTable::new(1, length);
    let mut value = seed;
    for row in 0..length {
        trace.set(0, row, value);
        value = value.mul(value);
    }
    let output = trace.get(0, length - 1);

    let mut air = Air::new(1, length);
    air.add_transition(2, |current, next| next[0].sub(current[0].mul(current[0])));
    air.add_boundary(0, 0, seed);
    air.add_boundary(0, length - 1, output);

    SquaringChain {
        air,
        trace,
        seed,
        output,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark::{prove, verify, StarkParams};

    #[test]
    fn the_chain_squares_each_step() {
        let chain = squaring_chain(4, Felt::new(3));
        assert_eq!(chain.trace.get(0, 0), Felt::new(3));
        assert_eq!(chain.trace.get(0, 1), Felt::new(9));
        assert_eq!(chain.trace.get(0, 2), Felt::new(81));
        assert!(chain.air.is_satisfied(&chain.trace));
    }

    #[test]
    fn the_chain_proves_and_verifies() {
        let chain = squaring_chain(8, Felt::new(7));
        let params = StarkParams {
            lde_blowup: 8,
            num_queries: 32,
        };
        let proof = prove(&chain.air, &chain.trace, &params);
        assert!(verify(&chain.air, &params, &proof));
    }
}
