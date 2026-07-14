//! The Keccak f permutation, the core of SHA3 and SHAKE, and its arithmetization.
//!
//! The permutation runs twenty four rounds over a state of twenty five sixty
//! four bit lanes. Each round is theta, rho, pi, chi, and iota. The reference
//! here follows FIPS 202 and matches the crypto crate sponge on known inputs.
//! The arithmetization that follows represents the state as bit columns in the
//! field and expresses every Boolean step as field arithmetic, an exclusive or
//! of two bits as a plus b minus two a b, an and as a b, a not as one minus a.

use crate::air::{Air, TraceTable};
use crate::field::Felt;

/// The number of lanes in the state.
pub const LANES: usize = 25;

/// The bit width of a lane.
pub const LANE_BITS: usize = 64;

/// The number of rounds in the standard permutation.
pub const KECCAK_ROUNDS: usize = 24;

/// The rotation offsets of the rho step, indexed by the lane coordinates x and y
/// with the lane at x plus five y.
const RHO: [[u32; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];

/// Generates the round constants of the iota step by the FIPS 202 linear
/// feedback shift register. The register runs across the rounds without a reset,
/// so this returns as many constants as asked, the first twenty four matching the
/// standard table.
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
/// after the last, so entry i is the state after i rounds.
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

// The column layout of the arithmetized permutation. The state bits come first,
// then the theta parity column, the round constant bits, the state half lanes
// that bind the public bits, and the round constant half lanes.
const S_OFF: usize = 0;
const STATE_BITS: usize = LANES * LANE_BITS;
const C_OFF: usize = S_OFF + STATE_BITS;
const C_BITS: usize = 5 * LANE_BITS;
const RC_OFF: usize = C_OFF + C_BITS;
const HALF_OFF: usize = RC_OFF + LANE_BITS;
const HALVES: usize = 2 * LANES;
const RCHALF_OFF: usize = HALF_OFF + HALVES;

/// The full column width of the permutation trace.
pub const KECCAK_WIDTH: usize = RCHALF_OFF + 2;

/// The number of rows in the permutation trace, a power of two above the round
/// count. Rows past the twenty fourth carry further genuine rounds so the wrap
/// around transition never has to hold.
pub const KECCAK_TRACE_ROWS: usize = 32;

fn s_idx(x: usize, y: usize, z: usize) -> usize {
    (x + 5 * y) * LANE_BITS + z
}

fn c_idx(x: usize, z: usize) -> usize {
    C_OFF + x * LANE_BITS + z
}

// The theta output bit at the coordinates x, y, z read from the current row.
fn theta_bit(row: &[Felt], x: usize, y: usize, z: usize) -> Felt {
    let a = row[s_idx(x, y, z)];
    let c1 = row[c_idx((x + 4) % 5, z)];
    let c2 = row[c_idx((x + 1) % 5, (z + LANE_BITS - 1) % LANE_BITS)];
    xor3(a, c1, c2)
}

// The rho and pi rewired bit at the coordinates px, py, z, read from the theta
// output of its source lane.
fn b_bit(row: &[Felt], px: usize, py: usize, z: usize) -> Felt {
    let sx = (px + 3 * py) % 5;
    let sy = px;
    let r = (RHO[sx][sy] % LANE_BITS as u32) as usize;
    let sz = (z + LANE_BITS - r) % LANE_BITS;
    theta_bit(row, sx, sy, sz)
}

// The round output bit at x, y, z, chi over the rewired theta with iota on the
// zero lane.
fn round_bit(row: &[Felt], x: usize, y: usize, z: usize) -> Felt {
    let b0 = b_bit(row, x, y, z);
    let b1 = b_bit(row, (x + 1) % 5, y, z);
    let b2 = b_bit(row, (x + 2) % 5, y, z);
    let and = Felt::ONE.sub(b1).mul(b2);
    let chi = xor2(b0, and);
    if x == 0 && y == 0 {
        xor2(chi, row[RC_OFF + z])
    } else {
        chi
    }
}

// The field value of a thirty two bit half lane from its bits.
fn half_value(row: &[Felt], base_bit: usize, start: usize) -> Felt {
    let two = Felt::new(2);
    let mut acc = Felt::ZERO;
    let mut weight = Felt::ONE;
    for z in start..start + 32 {
        acc = acc.add(row[base_bit + z].mul(weight));
        weight = weight.mul(two);
    }
    acc
}

/// Builds the description of the permutation over a public input and output. The
/// input and output are bound bit exact through the half lane columns.
pub fn keccak_air(input: &[u64; LANES], output: &[u64; LANES]) -> Air {
    let mut air = Air::new(KECCAK_WIDTH, KECCAK_TRACE_ROWS);

    // Every state bit and round constant bit is zero or one.
    for i in 0..STATE_BITS {
        air.add_single_row(2, move |row| row[i].mul(row[i].sub(Felt::ONE)));
    }
    for z in 0..LANE_BITS {
        let col = RC_OFF + z;
        air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
    }

    // The theta parity column is the exclusive or over the y axis.
    for x in 0..5 {
        for z in 0..LANE_BITS {
            air.add_single_row(5, move |row| {
                let bits = [
                    row[s_idx(x, 0, z)],
                    row[s_idx(x, 1, z)],
                    row[s_idx(x, 2, z)],
                    row[s_idx(x, 3, z)],
                    row[s_idx(x, 4, z)],
                ];
                row[c_idx(x, z)].sub(xor_all(&bits))
            });
        }
    }

    // The half lanes recompose the state bits, low then high. A thirty two bit
    // sum stays below the field, so the bits are pinned uniquely.
    for l in 0..LANES {
        let lo = HALF_OFF + 2 * l;
        let hi = HALF_OFF + 2 * l + 1;
        let base = l * LANE_BITS;
        air.add_single_row(1, move |row| row[lo].sub(half_value(row, base, 0)));
        air.add_single_row(1, move |row| row[hi].sub(half_value(row, base, 32)));
    }
    air.add_single_row(1, |row| row[RCHALF_OFF].sub(half_value(row, RC_OFF, 0)));
    air.add_single_row(1, |row| {
        row[RCHALF_OFF + 1].sub(half_value(row, RC_OFF, 32))
    });

    // The round relation, the next state bit is chi over the rewired theta of the
    // current state with iota folded in on the zero lane.
    for x in 0..5 {
        for y in 0..5 {
            for z in 0..LANE_BITS {
                let target = s_idx(x, y, z);
                air.add_transition(10, move |current, next| {
                    next[target].sub(round_bit(current, x, y, z))
                });
            }
        }
    }

    // The public input at the first row and the output at the round count row.
    for l in 0..LANES {
        let lo = HALF_OFF + 2 * l;
        let hi = HALF_OFF + 2 * l + 1;
        air.add_boundary(lo, 0, Felt::new(input[l] & 0xffff_ffff));
        air.add_boundary(hi, 0, Felt::new(input[l] >> 32));
        air.add_boundary(lo, KECCAK_ROUNDS, Felt::new(output[l] & 0xffff_ffff));
        air.add_boundary(hi, KECCAK_ROUNDS, Felt::new(output[l] >> 32));
    }

    // The round constant at every row, so the iota step reads a pinned value.
    let rc = round_constants(KECCAK_TRACE_ROWS);
    for (r, value) in rc.iter().enumerate() {
        air.add_boundary(RCHALF_OFF, r, Felt::new(value & 0xffff_ffff));
        air.add_boundary(RCHALF_OFF + 1, r, Felt::new(value >> 32));
    }

    air
}

fn fill_row(trace: &mut TraceTable, row: usize, state: &[u64; LANES], rc: u64) {
    for l in 0..LANES {
        for z in 0..LANE_BITS {
            trace.set(l * LANE_BITS + z, row, Felt::new((state[l] >> z) & 1));
        }
    }
    let mut c = [0u64; 5];
    for (x, cell) in c.iter_mut().enumerate() {
        *cell = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
    }
    for (x, cell) in c.iter().enumerate() {
        for z in 0..LANE_BITS {
            trace.set(C_OFF + x * LANE_BITS + z, row, Felt::new((cell >> z) & 1));
        }
    }
    for z in 0..LANE_BITS {
        trace.set(RC_OFF + z, row, Felt::new((rc >> z) & 1));
    }
    for l in 0..LANES {
        trace.set(HALF_OFF + 2 * l, row, Felt::new(state[l] & 0xffff_ffff));
        trace.set(HALF_OFF + 2 * l + 1, row, Felt::new(state[l] >> 32));
    }
    trace.set(RCHALF_OFF, row, Felt::new(rc & 0xffff_ffff));
    trace.set(RCHALF_OFF + 1, row, Felt::new(rc >> 32));
}

/// A filled permutation trace with its description and the output state.
pub struct KeccakInstance {
    /// The description shared with the verifier.
    pub air: Air,
    /// The filled trace.
    pub trace: TraceTable,
    /// The output after the standard round count.
    pub output: [u64; LANES],
}

/// Builds the permutation trace over the input state. The trace runs further
/// genuine rounds past the twenty fourth to fill the power of two length, and the
/// output is read at the round count row.
pub fn keccak_trace(input: &[u64; LANES]) -> KeccakInstance {
    let rc = round_constants(KECCAK_TRACE_ROWS);
    let mut states: Vec<[u64; LANES]> = Vec::with_capacity(KECCAK_TRACE_ROWS);
    let mut state = *input;
    states.push(state);
    for value in rc.iter().take(KECCAK_TRACE_ROWS - 1) {
        state = keccak_round(&state, *value);
        states.push(state);
    }
    let output = states[KECCAK_ROUNDS];

    let mut trace = TraceTable::new(KECCAK_WIDTH, KECCAK_TRACE_ROWS);
    for row in 0..KECCAK_TRACE_ROWS {
        fill_row(&mut trace, row, &states[row], rc[row]);
    }

    KeccakInstance {
        air: keccak_air(input, &output),
        trace,
        output,
    }
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

    fn sample_input() -> [u64; LANES] {
        let mut state = [0u64; LANES];
        for (i, lane) in state.iter_mut().enumerate() {
            *lane = (i as u64)
                .wrapping_mul(0x0123_4567_89ab_cdef)
                .wrapping_add(0xdead_beef);
        }
        state
    }

    #[test]
    fn the_trace_output_matches_the_permutation() {
        let input = sample_input();
        let instance = keccak_trace(&input);
        assert_eq!(instance.output, keccak_f1600(&input));
    }

    #[test]
    fn the_arithmetic_holds_on_every_row() {
        let instance = keccak_trace(&sample_input());
        assert!(instance.air.is_satisfied(&instance.trace));
    }

    #[test]
    fn the_all_zero_state_is_arithmetized() {
        let instance = keccak_trace(&[0u64; LANES]);
        assert!(instance.air.is_satisfied(&instance.trace));
        assert_eq!(instance.output, keccak_f1600(&[0u64; LANES]));
    }

    #[test]
    fn a_tampered_state_bit_is_rejected() {
        let mut instance = keccak_trace(&sample_input());
        // Flip a state bit on an interior round, which breaks the round relation
        // that produced it.
        let cell = instance.trace.get(37, 5);
        instance.trace.set(37, 5, xor2(cell, Felt::ONE));
        assert!(!instance.air.is_satisfied(&instance.trace));
    }

    #[test]
    fn a_tampered_output_is_rejected() {
        let input = sample_input();
        let instance = keccak_trace(&input);
        let mut wrong = keccak_f1600(&input);
        wrong[0] ^= 1;
        let air = keccak_air(&input, &wrong);
        assert!(!air.is_satisfied(&instance.trace));
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
