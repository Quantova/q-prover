//! The two hashing steps of the module lattice verify relation.

use crate::lattice::{MATRIX_COLS, MATRIX_ROWS};
use crate::sponge::{shake_trace, SpongeInstance, SHAKE128_RATE, SHAKE256_RATE};

/// The seed byte length, the public matrix seed rho.
pub const SEED_BYTES: usize = 32;

/// The message digest byte length, the collision resistant hash of the message.
pub const MU_BYTES: usize = 64;

/// The challenge encoding byte length for the parameter set, lambda over four.
pub const CTILDE_BYTES: usize = 48;

/// Builds the SHAKE128 seed of one matrix entry, the public seed joined with the
pub fn matrix_entry_seed(rho: &[u8; SEED_BYTES], row: usize, col: usize) -> Vec<u8> {
    assert!(row < MATRIX_ROWS && col < MATRIX_COLS);
    let mut seed = Vec::with_capacity(SEED_BYTES + 2);
    seed.extend_from_slice(rho);
    seed.push(col as u8);
    seed.push(row as u8);
    seed
}

/// The number of SHAKE128 blocks that cover the candidate bytes for one ring of
pub fn matrix_entry_blocks() -> usize {
    let candidate_bytes: usize = 256 * 3;
    candidate_bytes.div_ceil(SHAKE128_RATE)
}

/// The number of squeeze permutations of one matrix entry trace, the block count
pub fn matrix_entry_perms() -> usize {
    matrix_entry_blocks().next_power_of_two()
}

/// Builds the sponge trace of one matrix entry expansion, the SHAKE128 stream
pub fn matrix_entry_hash(rho: &[u8; SEED_BYTES], row: usize, col: usize) -> SpongeInstance {
    let seed = matrix_entry_seed(rho, row, col);
    shake_trace(SHAKE128_RATE, matrix_entry_perms(), &seed)
}

/// Builds the sponge trace of the challenge squeeze, the SHAKE256 stream over the
pub fn challenge_hash(input: &[u8]) -> SpongeInstance {
    assert!(
        input.len() < SHAKE256_RATE,
        "the single block challenge hash covers a one block input"
    );
    shake_trace(SHAKE256_RATE, 1, input)
}

/// The count of matrix entries that the expansion hashes for the parameter set.
pub fn matrix_entries() -> usize {
    MATRIX_ROWS * MATRIX_COLS
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sponge::{shake_air, shake_output};
    use crate::stark::{prove, verify, StarkParams};
    use qtv_crypto::sha3::{shake128, shake256};

    fn params() -> StarkParams {
        StarkParams {
            lde_blowup: 32,
            num_queries: 24,
        }
    }

    fn sample_seed() -> [u8; SEED_BYTES] {
        let mut rho = [0u8; SEED_BYTES];
        for (i, b) in rho.iter_mut().enumerate() {
            *b = (i as u8).wrapping_mul(37).wrapping_add(1);
        }
        rho
    }

    #[test]
    fn the_matrix_entry_stream_matches_the_crypto_shake128() {
        let rho = sample_seed();
        let blocks = matrix_entry_perms();
        for row in 0..MATRIX_ROWS {
            for col in 0..MATRIX_COLS {
                let seed = matrix_entry_seed(&rho, row, col);
                let ours = shake_output(SHAKE128_RATE, blocks, &seed);
                let mut expected = vec![0u8; blocks * SHAKE128_RATE];
                shake128(&seed, &mut expected);
                assert_eq!(ours, expected);
            }
        }
    }

    #[test]
    fn the_matrix_entry_seed_has_the_expected_shape() {
        let rho = sample_seed();
        let seed = matrix_entry_seed(&rho, 5, 4);
        assert_eq!(seed.len(), SEED_BYTES + 2);
        assert_eq!(seed[SEED_BYTES], 4);
        assert_eq!(seed[SEED_BYTES + 1], 5);
        assert_eq!(matrix_entries(), 30);
    }

    #[test]
    fn the_challenge_stream_matches_the_crypto_shake256() {
        // A representative single block challenge input standing in for the
        // message digest joined with a short commitment.
        let mut input = vec![0u8; MU_BYTES];
        for (i, b) in input.iter_mut().enumerate() {
            *b = (i as u8).wrapping_mul(29).wrapping_add(7);
        }
        let instance = challenge_hash(&input);
        let mut expected = vec![0u8; SHAKE256_RATE];
        shake256(&input, &mut expected);
        assert_eq!(instance.output, expected);
        // The challenge encoding is the leading bytes of the squeeze.
        assert!(CTILDE_BYTES <= instance.output.len());
    }

    #[test]
    fn the_matrix_entry_hash_arithmetic_holds() {
        let rho = sample_seed();
        let instance = matrix_entry_hash(&rho, 2, 3);
        assert!(instance.air.is_satisfied(&instance.trace));
    }

    #[test]
    fn the_challenge_hash_proves_and_verifies() {
        let mut input = vec![0u8; MU_BYTES];
        for (i, b) in input.iter_mut().enumerate() {
            *b = (i as u8).wrapping_mul(13).wrapping_add(3);
        }
        let instance = challenge_hash(&input);
        let proof = prove(&instance.air, &instance.trace, &params());
        let air = shake_air(SHAKE256_RATE, 1, &input, &instance.output);
        assert!(verify(&air, &params(), &proof));
    }
}
