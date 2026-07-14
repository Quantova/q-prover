//! The Keccak f permutation, the core of SHA3 and SHAKE, and its arithmetization.

use crate::field::Felt;

/// The number of lanes in the state.
pub const LANES: usize = 25;

/// The bit width of a lane.
pub const LANE_BITS: usize = 64;

/// The number of rounds in the standard permutation.
pub const KECCAK_ROUNDS: usize = 24;

/// The rotation offsets of the rho step, indexed by the lane coordinates x and y
const RHO: [[u32; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];

/// Generates the round constants of the iota step by the FIPS 202 linear
pub fn round_constants(count: usize) -> Vec<u64> {
    let mut lfsr: u8 = 0x01;
    let mut step = || {
        let bit = lfsr & 0x01 != 0;
        lfsr = if lfsr & 0x80 != 0 {
            (lfsr << 1) ^ 0x71
        } else {
            lfsr << 1
        };
        bit
    };
    let mut out = Vec::with_capacity(count);
    for _ in 0..count {
        let mut rc = 0u64;
        for j in 0..7 {
            if step() {
                rc |= 1u64 << ((1usize << j) - 1);
            }
        }
        out.push(rc);
    }
    out
}

/// Applies one round of the permutation to a state under the round constant.
pub fn keccak_round(state: &[u64; LANES], rc: u64) -> [u64; LANES] {
    let mut s = *state;

    // Theta.
    let mut c = [0u64; 5];
    for (x, cell) in c.iter_mut().enumerate() {
        *cell = s[x] ^ s[x + 5] ^ s[x + 10] ^ s[x + 15] ^ s[x + 20];
    }
    let mut d = [0u64; 5];
    for (x, cell) in d.iter_mut().enumerate() {
        *cell = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
    }
    for x in 0..5 {
        for y in 0..5 {
            s[x + 5 * y] ^= d[x];
        }
    }

    // Rho and pi.
    let mut b = [0u64; LANES];
    for x in 0..5 {
        for y in 0..5 {
            let rotated = s[x + 5 * y].rotate_left(RHO[x][y]);
            b[y + 5 * ((2 * x + 3 * y) % 5)] = rotated;
        }
    }

    // Chi.
    for x in 0..5 {
        for y in 0..5 {
            s[x + 5 * y] = b[x + 5 * y] ^ ((!b[(x + 1) % 5 + 5 * y]) & b[(x + 2) % 5 + 5 * y]);
        }
    }

    // Iota.
    s[0] ^= rc;
    s
}

/// Runs the given number of rounds and records the state before each round and
pub fn keccak_states(input: &[u64; LANES], rounds: usize) -> Vec<[u64; LANES]> {
    let rc = round_constants(rounds);
    let mut states = Vec::with_capacity(rounds + 1);
    let mut state = *input;
    states.push(state);
    for r in 0..rounds {
        state = keccak_round(&state, rc[r]);
        states.push(state);
    }
    states
}

/// The full twenty four round permutation.
pub fn keccak_f1600(input: &[u64; LANES]) -> [u64; LANES] {
    let states = keccak_states(input, KECCAK_ROUNDS);
    states[KECCAK_ROUNDS]
}

/// An exclusive or of two field elements that are constrained to be bits.
pub fn xor2(a: Felt, b: Felt) -> Felt {
    let ab = a.mul(b);
    a.add(b).sub(ab).sub(ab)
}

/// An exclusive or of three bits.
pub fn xor3(a: Felt, b: Felt, c: Felt) -> Felt {
    xor2(xor2(a, b), c)
}

/// An exclusive or over a slice of bits.
pub fn xor_all(bits: &[Felt]) -> Felt {
    let mut acc = Felt::ZERO;
    for bit in bits {
        acc = xor2(acc, *bit);
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use qtv_crypto::sha3::{sha3_256, shake256};

    // The twenty four standard round constants from the crypto crate table.
    const REFERENCE_RC: [u64; 24] = [
        0x0000000000000001,
        0x0000000000008082,
        0x800000000000808a,
        0x8000000080008000,
        0x000000000000808b,
        0x0000000080000001,
        0x8000000080008081,
        0x8000000000008009,
        0x000000000000008a,
        0x0000000000000088,
        0x0000000080008009,
        0x000000008000000a,
        0x000000008000808b,
        0x800000000000008b,
        0x8000000000008089,
        0x8000000000008003,
        0x8000000000008002,
        0x8000000000000080,
        0x000000000000800a,
        0x800000008000000a,
        0x8000000080008081,
        0x8000000000008080,
        0x0000000080000001,
        0x8000000080008008,
    ];

    #[test]
    fn the_round_constants_match_the_standard_table() {
        let rc = round_constants(24);
        assert_eq!(rc, REFERENCE_RC);
    }

    // A byte oriented sponge built on the reference permutation, so a match with
    // the crypto crate confirms the permutation.
    fn reference_sponge(rate: usize, domain: u8, input: &[u8], out_len: usize) -> Vec<u8> {
        let mut lanes = [0u64; LANES];
        let absorb = |lanes: &mut [u64; LANES], block: &[u8]| {
            for (i, byte) in block.iter().enumerate() {
                lanes[i / 8] ^= (*byte as u64) << (8 * (i % 8));
            }
        };
        let mut offset = 0;
        let mut block = vec![0u8; rate];
        for &byte in input {
            block[offset] = byte;
            offset += 1;
            if offset == rate {
                absorb(&mut lanes, &block);
                lanes = keccak_f1600(&lanes);
                block = vec![0u8; rate];
                offset = 0;
            }
        }
        block[offset] = domain;
        block[rate - 1] ^= 0x80;
        absorb(&mut lanes, &block);
        lanes = keccak_f1600(&lanes);

        let mut out = Vec::with_capacity(out_len);
        let mut pos = 0;
        while out.len() < out_len {
            if pos == rate {
                lanes = keccak_f1600(&lanes);
                pos = 0;
            }
            out.push((lanes[pos / 8] >> (8 * (pos % 8))) as u8);
            pos += 1;
        }
        out
    }

    #[test]
    fn the_reference_sponge_matches_the_crypto_sha3() {
        for input in [
            b"".as_slice(),
            b"abc".as_slice(),
            b"quantova prover".as_slice(),
        ] {
            let ours = reference_sponge(136, 0x06, input, 32);
            assert_eq!(&ours[..], &sha3_256(input)[..]);
        }
    }

    #[test]
    fn the_reference_sponge_matches_the_crypto_shake256() {
        let input = b"module lattice batch";
        let mut expected = [0u8; 96];
        shake256(input, &mut expected);
        let ours = reference_sponge(136, 0x1f, input, 96);
        assert_eq!(&ours[..], &expected[..]);
    }

    #[test]
    fn the_permutation_is_a_bijection_on_a_sample() {
        let mut state = [0u64; LANES];
        for (i, lane) in state.iter_mut().enumerate() {
            *lane = (i as u64)
                .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                .wrapping_add(1);
        }
        let permuted = keccak_f1600(&state);
        assert_ne!(permuted, state);
        // Two distinct inputs give distinct outputs at this sample.
        let mut other = state;
        other[3] ^= 1;
        assert_ne!(keccak_f1600(&other), permuted);
    }

    #[test]
    fn the_bit_operations_follow_the_truth_tables() {
        let zero = Felt::ZERO;
        let one = Felt::ONE;
        assert_eq!(xor2(zero, zero), zero);
        assert_eq!(xor2(one, zero), one);
        assert_eq!(xor2(one, one), zero);
        assert_eq!(xor3(one, one, one), one);
        assert_eq!(xor3(one, one, zero), zero);
        assert_eq!(xor_all(&[one, one, one, zero, one]), zero);
    }
}
