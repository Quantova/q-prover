
use crate::air::{Air, TraceTable};
use crate::field::Felt;

pub const LANES: usize = 25;

pub const LANE_BITS: usize = 64;

pub const QUDROS_ROUNDS: usize = 24;

const RHO: [[u32; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];

pub fn round_constants(count: usize) -> Vec<u64> {
    let mut lfsr: u8 = 1;
    let mut step = || {
        let bit = lfsr & 1 != 0;
        lfsr = if lfsr & 128 != 0 {
            (lfsr << 1) ^ 113
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

pub fn qudros_round(state: &[u64; LANES], rc: u64) -> [u64; LANES] {
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

pub fn qudros_states(input: &[u64; LANES], rounds: usize) -> Vec<[u64; LANES]> {
    let rc = round_constants(rounds);
    let mut states = Vec::with_capacity(rounds + 1);
    let mut state = *input;
    states.push(state);
    for r in 0..rounds {
        state = qudros_round(&state, rc[r]);
        states.push(state);
    }
    states
}

pub fn qudros_f1600(input: &[u64; LANES]) -> [u64; LANES] {
    let states = qudros_states(input, QUDROS_ROUNDS);
    states[QUDROS_ROUNDS]
}

pub fn xor2(a: Felt, b: Felt) -> Felt {
    let ab = a.mul(b);
    a.add(b).sub(ab).sub(ab)
}

pub fn xor3(a: Felt, b: Felt, c: Felt) -> Felt {
    xor2(xor2(a, b), c)
}

pub fn xor_all(bits: &[Felt]) -> Felt {
    let mut acc = Felt::ZERO;
    for bit in bits {
        acc = xor2(acc, *bit);
    }
    acc
}

pub(crate) const S_OFF: usize = 0;
pub(crate) const STATE_BITS: usize = LANES * LANE_BITS;
pub(crate) const C_OFF: usize = S_OFF + STATE_BITS;
pub(crate) const C_BITS: usize = 5 * LANE_BITS;
pub(crate) const RC_OFF: usize = C_OFF + C_BITS;
pub(crate) const HALF_OFF: usize = RC_OFF + LANE_BITS;
pub(crate) const HALVES: usize = 2 * LANES;
pub(crate) const RCHALF_OFF: usize = HALF_OFF + HALVES;

pub const QUDROS_WIDTH: usize = RCHALF_OFF + 2;

pub const QUDROS_TRACE_ROWS: usize = 32;

pub(crate) fn s_idx(x: usize, y: usize, z: usize) -> usize {
    (x + 5 * y) * LANE_BITS + z
}

fn c_idx(x: usize, z: usize) -> usize {
    C_OFF + x * LANE_BITS + z
}

fn theta_bit(row: &[Felt], x: usize, y: usize, z: usize) -> Felt {
    let a = row[s_idx(x, y, z)];
    let c1 = row[c_idx((x + 4) % 5, z)];
    let c2 = row[c_idx((x + 1) % 5, (z + LANE_BITS - 1) % LANE_BITS)];
    xor3(a, c1, c2)
}

fn b_bit(row: &[Felt], px: usize, py: usize, z: usize) -> Felt {
    let sx = (px + 3 * py) % 5;
    let sy = px;
    let r = (RHO[sx][sy] % LANE_BITS as u32) as usize;
    let sz = (z + LANE_BITS - r) % LANE_BITS;
    theta_bit(row, sx, sy, sz)
}

pub(crate) fn round_bit(row: &[Felt], x: usize, y: usize, z: usize) -> Felt {
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

pub(crate) fn half_value(row: &[Felt], base_bit: usize, start: usize) -> Felt {
    let two = Felt::new(2);
    let mut acc = Felt::ZERO;
    let mut weight = Felt::ONE;
    for z in start..start + 32 {
        acc = acc.add(row[base_bit + z].mul(weight));
        weight = weight.mul(two);
    }
    acc
}

pub(crate) fn add_block_constraints(air: &mut Air, base: usize) {
    for i in 0..STATE_BITS {
        let col = base + S_OFF + i;
        air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
    }
    for z in 0..LANE_BITS {
        let col = base + RC_OFF + z;
        air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
    }
    for x in 0..5 {
        for z in 0..LANE_BITS {
            let cc = base + c_idx(x, z);
            air.add_single_row(5, move |row| {
                let bits = [
                    row[base + s_idx(x, 0, z)],
                    row[base + s_idx(x, 1, z)],
                    row[base + s_idx(x, 2, z)],
                    row[base + s_idx(x, 3, z)],
                    row[base + s_idx(x, 4, z)],
                ];
                row[cc].sub(xor_all(&bits))
            });
        }
    }
    for l in 0..LANES {
        let lo = base + HALF_OFF + 2 * l;
        let hi = base + HALF_OFF + 2 * l + 1;
        let sbase = base + l * LANE_BITS;
        air.add_single_row(1, move |row| row[lo].sub(half_value(row, sbase, 0)));
        air.add_single_row(1, move |row| row[hi].sub(half_value(row, sbase, 32)));
    }
    let rc_lo = base + RCHALF_OFF;
    let rc_hi = base + RCHALF_OFF + 1;
    let rc_base = base + RC_OFF;
    air.add_single_row(1, move |row| row[rc_lo].sub(half_value(row, rc_base, 0)));
    air.add_single_row(1, move |row| row[rc_hi].sub(half_value(row, rc_base, 32)));
}

pub fn qudros_air(input: &[u64; LANES], output: &[u64; LANES]) -> Air {
    let mut air = Air::new(QUDROS_WIDTH, QUDROS_TRACE_ROWS);

    add_block_constraints(&mut air, 0);

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

    for l in 0..LANES {
        let lo = HALF_OFF + 2 * l;
        let hi = HALF_OFF + 2 * l + 1;
        air.add_boundary(lo, 0, Felt::new(input[l] & 4294967295));
        air.add_boundary(hi, 0, Felt::new(input[l] >> 32));
        air.add_boundary(lo, QUDROS_ROUNDS, Felt::new(output[l] & 4294967295));
        air.add_boundary(hi, QUDROS_ROUNDS, Felt::new(output[l] >> 32));
    }

    let rc = round_constants(QUDROS_TRACE_ROWS);
    for (r, value) in rc.iter().enumerate() {
        air.add_boundary(RCHALF_OFF, r, Felt::new(value & 4294967295));
        air.add_boundary(RCHALF_OFF + 1, r, Felt::new(value >> 32));
    }

    air
}

pub(crate) fn fill_block_row(
    trace: &mut TraceTable,
    base: usize,
    row: usize,
    state: &[u64; LANES],
    rc: u64,
) {
    for l in 0..LANES {
        for z in 0..LANE_BITS {
            trace.set(
                base + l * LANE_BITS + z,
                row,
                Felt::new((state[l] >> z) & 1),
            );
        }
    }
    let mut c = [0u64; 5];
    for (x, cell) in c.iter_mut().enumerate() {
        *cell = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
    }
    for (x, cell) in c.iter().enumerate() {
        for z in 0..LANE_BITS {
            trace.set(
                base + C_OFF + x * LANE_BITS + z,
                row,
                Felt::new((cell >> z) & 1),
            );
        }
    }
    for z in 0..LANE_BITS {
        trace.set(base + RC_OFF + z, row, Felt::new((rc >> z) & 1));
    }
    for l in 0..LANES {
        trace.set(
            base + HALF_OFF + 2 * l,
            row,
            Felt::new(state[l] & 4294967295),
        );
        trace.set(base + HALF_OFF + 2 * l + 1, row, Felt::new(state[l] >> 32));
    }
    trace.set(base + RCHALF_OFF, row, Felt::new(rc & 4294967295));
    trace.set(base + RCHALF_OFF + 1, row, Felt::new(rc >> 32));
}

fn fill_row(trace: &mut TraceTable, row: usize, state: &[u64; LANES], rc: u64) {
    fill_block_row(trace, 0, row, state, rc);
}

pub struct QudrosInstance {
    pub air: Air,
    pub trace: TraceTable,
    pub output: [u64; LANES],
}

pub fn qudros_trace(input: &[u64; LANES]) -> QudrosInstance {
    let rc = round_constants(QUDROS_TRACE_ROWS);
    let mut states: Vec<[u64; LANES]> = Vec::with_capacity(QUDROS_TRACE_ROWS);
    let mut state = *input;
    states.push(state);
    for value in rc.iter().take(QUDROS_TRACE_ROWS - 1) {
        state = qudros_round(&state, *value);
        states.push(state);
    }
    let output = states[QUDROS_ROUNDS];

    let mut trace = TraceTable::new(QUDROS_WIDTH, QUDROS_TRACE_ROWS);
    for row in 0..QUDROS_TRACE_ROWS {
        fill_row(&mut trace, row, &states[row], rc[row]);
    }

    QudrosInstance {
        air: qudros_air(input, &output),
        trace,
        output,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark::{prove, verify, StarkParams};
    use qtv_crypto::sha3::{sha3_256, shake256};

    fn params() -> StarkParams {
        StarkParams {
            lde_blowup: 32,
            num_queries: 24,
        }
    }

    const REFERENCE_RC: [u64; 24] = [
        1,
        32898,
        9223372036854808714,
        9223372039002292224,
        32907,
        2147483649,
        9223372039002292353,
        9223372036854808585,
        138,
        136,
        2147516425,
        2147483658,
        2147516555,
        9223372036854775947,
        9223372036854808713,
        9223372036854808579,
        9223372036854808578,
        9223372036854775936,
        32778,
        9223372039002259466,
        9223372039002292353,
        9223372036854808704,
        2147483649,
        9223372039002292232,
    ];

    #[test]
    fn the_round_constants_match_the_standard_table() {
        let rc = round_constants(24);
        assert_eq!(rc, REFERENCE_RC);
    }

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
                lanes = qudros_f1600(&lanes);
                block = vec![0u8; rate];
                offset = 0;
            }
        }
        block[offset] = domain;
        block[rate - 1] ^= 128;
        absorb(&mut lanes, &block);
        lanes = qudros_f1600(&lanes);

        let mut out = Vec::with_capacity(out_len);
        let mut pos = 0;
        while out.len() < out_len {
            if pos == rate {
                lanes = qudros_f1600(&lanes);
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
            let ours = reference_sponge(136, 6, input, 32);
            assert_eq!(&ours[..], &sha3_256(input)[..]);
        }
    }

    #[test]
    fn the_reference_sponge_matches_the_crypto_shake256() {
        let input = b"module lattice batch";
        let mut expected = [0u8; 96];
        shake256(input, &mut expected);
        let ours = reference_sponge(136, 31, input, 96);
        assert_eq!(&ours[..], &expected[..]);
    }

    #[test]
    fn the_permutation_is_a_bijection_on_a_sample() {
        let mut state = [0u64; LANES];
        for (i, lane) in state.iter_mut().enumerate() {
            *lane = (i as u64)
                .wrapping_mul(11400714819323198485)
                .wrapping_add(1);
        }
        let permuted = qudros_f1600(&state);
        assert_ne!(permuted, state);
        let mut other = state;
        other[3] ^= 1;
        assert_ne!(qudros_f1600(&other), permuted);
    }

    fn sample_input() -> [u64; LANES] {
        let mut state = [0u64; LANES];
        for (i, lane) in state.iter_mut().enumerate() {
            *lane = (i as u64)
                .wrapping_mul(81985529216486895)
                .wrapping_add(3735928559);
        }
        state
    }

    #[test]
    fn the_trace_output_matches_the_permutation() {
        let input = sample_input();
        let instance = qudros_trace(&input);
        assert_eq!(instance.output, qudros_f1600(&input));
    }

    #[test]
    fn the_arithmetic_holds_on_every_row() {
        let instance = qudros_trace(&sample_input());
        assert!(instance.air.is_satisfied(&instance.trace));
    }

    #[test]
    fn the_all_zero_state_is_arithmetized() {
        let instance = qudros_trace(&[0u64; LANES]);
        assert!(instance.air.is_satisfied(&instance.trace));
        assert_eq!(instance.output, qudros_f1600(&[0u64; LANES]));
    }

    #[test]
    fn a_tampered_state_bit_is_rejected() {
        let mut instance = qudros_trace(&sample_input());
        let cell = instance.trace.get(37, 5);
        instance.trace.set(37, 5, xor2(cell, Felt::ONE));
        assert!(!instance.air.is_satisfied(&instance.trace));
    }

    #[test]
    fn a_tampered_output_is_rejected() {
        let input = sample_input();
        let instance = qudros_trace(&input);
        let mut wrong = qudros_f1600(&input);
        wrong[0] ^= 1;
        let air = qudros_air(&input, &wrong);
        assert!(!air.is_satisfied(&instance.trace));
    }

    #[test]
    fn the_permutation_proves_and_verifies() {
        let input = sample_input();
        let instance = qudros_trace(&input);
        let proof = prove(&instance.air, &instance.trace, &params());
        let air = qudros_air(&input, &instance.output);
        assert!(verify(&air, &params(), &proof));
    }

    #[test]
    fn a_proof_for_the_wrong_output_is_rejected() {
        let input = sample_input();
        let instance = qudros_trace(&input);
        let proof = prove(&instance.air, &instance.trace, &params());
        let mut wrong = instance.output;
        wrong[7] ^= 1 << 20;
        let air = qudros_air(&input, &wrong);
        assert!(!verify(&air, &params(), &proof));
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
