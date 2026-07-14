//! The SHAKE sponge over the arithmetized Keccak permutation.

use std::sync::Arc;

use crate::air::{Air, TraceTable};
use crate::field::Felt;
use crate::keccak::{
    add_block_constraints, fill_block_row, keccak_f1600, keccak_states, round_bit, round_constants,
    s_idx, HALF_OFF, KECCAK_ROUNDS, KECCAK_TRACE_ROWS, KECCAK_WIDTH, LANES, LANE_BITS, RCHALF_OFF,
};

/// The byte rate of SHAKE128.
pub const SHAKE128_RATE: usize = 168;

/// The byte rate of SHAKE256.
pub const SHAKE256_RATE: usize = 136;

/// The SHAKE domain separation byte of the FIPS 202 padding.
pub const SHAKE_DOMAIN: u8 = 0x1f;

const SEG_ROWS: usize = KECCAK_TRACE_ROWS;
const SEL_COL: usize = KECCAK_WIDTH;

/// The full column width of the sponge trace, one keccak block plus the round
pub const SPONGE_WIDTH: usize = KECCAK_WIDTH + 1;

fn block_to_lanes(block: &[u8]) -> [u64; LANES] {
    let mut lanes = [0u64; LANES];
    for (i, byte) in block.iter().enumerate() {
        lanes[i / 8] |= (*byte as u64) << (8 * (i % 8));
    }
    lanes
}

fn bytes_to_lane(bytes: &[u8]) -> u64 {
    let mut lane = 0u64;
    for (i, byte) in bytes.iter().enumerate() {
        lane |= (*byte as u64) << (8 * i);
    }
    lane
}

// The single padded input block for a message that fits in one rate block.
fn padded_block(rate: usize, message: &[u8]) -> Vec<u8> {
    assert!(message.len() < rate, "message must fit in one block");
    let mut block = vec![0u8; rate];
    block[..message.len()].copy_from_slice(message);
    block[message.len()] ^= SHAKE_DOMAIN;
    block[rate - 1] ^= 0x80;
    block
}

// The state fed into each permutation and produced out of it, one entry per
// squeeze block. Each output is the input of the next, the squeeze recurrence.
fn sponge_states(
    rate: usize,
    perms: usize,
    message: &[u8],
) -> (Vec<[u64; LANES]>, Vec<[u64; LANES]>) {
    let input = block_to_lanes(&padded_block(rate, message));
    let mut ins = Vec::with_capacity(perms);
    let mut outs = Vec::with_capacity(perms);
    let mut state = input;
    for _ in 0..perms {
        ins.push(state);
        let out = keccak_f1600(&state);
        outs.push(out);
        state = out;
    }
    (ins, outs)
}

/// The SHAKE output of the given rate over a single block message, the rate lanes
pub fn shake_output(rate: usize, perms: usize, message: &[u8]) -> Vec<u8> {
    let (_, outs) = sponge_states(rate, perms, message);
    let mut out = Vec::with_capacity(perms * rate);
    for state in &outs {
        for l in 0..rate / 8 {
            out.extend_from_slice(&state[l].to_le_bytes());
        }
    }
    out
}

/// Builds the sponge description over a public single block message and the
pub fn shake_air(rate: usize, perms: usize, message: &[u8], output: &[u8]) -> Air {
    let rows = perms * SEG_ROWS;
    let mut air = Air::new(SPONGE_WIDTH, rows);
    add_block_constraints(&mut air, 0);

    // The combined round and carry transition. On a round row the next state bit
    // is the keccak round output; on a carry row it is the current state bit, so
    // the output of one permutation flows into the input of the next.
    for x in 0..5 {
        for y in 0..5 {
            for z in 0..LANE_BITS {
                let target = s_idx(x, y, z);
                air.add_transition(11, move |current, next| {
                    let sel = current[SEL_COL];
                    let round = round_bit(current, x, y, z);
                    let carried = current[target];
                    let combined = sel.mul(round).add(Felt::ONE.sub(sel).mul(carried));
                    next[target].sub(combined)
                });
            }
        }
    }

    // The round selector and round constant at every row. The selector is one on
    // the twenty four round rows of a segment and zero on the carry rows.
    let rc = round_constants(SEG_ROWS);
    for global in 0..rows {
        let r = global % SEG_ROWS;
        let sel = if r < KECCAK_ROUNDS {
            Felt::ONE
        } else {
            Felt::ZERO
        };
        air.add_boundary(SEL_COL, global, sel);
        air.add_boundary(RCHALF_OFF, global, Felt::new(rc[r] & 0xffff_ffff));
        air.add_boundary(RCHALF_OFF + 1, global, Felt::new(rc[r] >> 32));
    }

    // The absorbed input block, all lanes at the first row.
    let input = block_to_lanes(&padded_block(rate, message));
    for l in 0..LANES {
        let lo = HALF_OFF + 2 * l;
        let hi = HALF_OFF + 2 * l + 1;
        air.add_boundary(lo, 0, Felt::new(input[l] & 0xffff_ffff));
        air.add_boundary(hi, 0, Felt::new(input[l] >> 32));
    }

    // The squeeze blocks, the rate lanes at the round count row of each segment.
    let rate_lanes = rate / 8;
    for j in 0..perms {
        let out_row = j * SEG_ROWS + KECCAK_ROUNDS;
        for l in 0..rate_lanes {
            let lane = bytes_to_lane(&output[j * rate + l * 8..j * rate + l * 8 + 8]);
            let lo = HALF_OFF + 2 * l;
            let hi = HALF_OFF + 2 * l + 1;
            air.add_boundary(lo, out_row, Felt::new(lane & 0xffff_ffff));
            air.add_boundary(hi, out_row, Felt::new(lane >> 32));
        }
    }

    air
}

/// A filled sponge trace with its description and the squeeze output.
pub struct SpongeInstance {
    /// The description shared with the verifier.
    pub air: Air,
    /// The filled trace.
    pub trace: TraceTable,
    /// The squeeze output bytes, the block count times the rate.
    pub output: Vec<u8>,
}

/// Builds the sponge trace over a single block message and the requested number
pub fn shake_trace(rate: usize, perms: usize, message: &[u8]) -> SpongeInstance {
    let (ins, _) = sponge_states(rate, perms, message);
    let rc = round_constants(SEG_ROWS);
    let rows = perms * SEG_ROWS;
    let mut trace = TraceTable::new(SPONGE_WIDTH, rows);

    for (j, state_in) in ins.iter().enumerate() {
        let states = keccak_states(state_in, KECCAK_ROUNDS);
        for r in 0..SEG_ROWS {
            let global = j * SEG_ROWS + r;
            let state = if r < KECCAK_ROUNDS {
                &states[r]
            } else {
                &states[KECCAK_ROUNDS]
            };
            fill_block_row(&mut trace, 0, global, state, rc[r]);
            let sel = if r < KECCAK_ROUNDS {
                Felt::ONE
            } else {
                Felt::ZERO
            };
            trace.set(SEL_COL, global, sel);
        }
    }

    let output = shake_output(rate, perms, message);
    let air = shake_air(rate, perms, message, &output);
    SpongeInstance { air, trace, output }
}

// The rate expressed in lanes.
fn rate_lanes(rate: usize) -> usize {
    rate / 8
}

// The padded blocks to absorb, each as a lane array. Full rate blocks come first
// and the trailing block carries the domain byte and the final bit, the FIPS 202
// pad ten star one.
fn absorb_blocks(rate: usize, message: &[u8]) -> Vec<[u64; LANES]> {
    let mut blocks = Vec::new();
    let mut i = 0;
    while message.len() - i >= rate {
        blocks.push(block_to_lanes(&message[i..i + rate]));
        i += rate;
    }
    let rem = message.len() - i;
    let mut last = vec![0u8; rate];
    last[..rem].copy_from_slice(&message[i..]);
    last[rem] ^= SHAKE_DOMAIN;
    last[rate - 1] ^= 0x80;
    blocks.push(block_to_lanes(&last));
    blocks
}

// The absorbed input state fed into each of the given number of permutation
// segments. The first is the first block over a zero state, each later absorb folds
// the next block into the rate lanes of the previous output, and any segments past
// the block count carry the sponge forward as plain squeeze permutations so the
// segment count can round up to a power of two.
fn absorb_states(rate: usize, message: &[u8], segments: usize) -> Vec<[u64; LANES]> {
    let blocks = absorb_blocks(rate, message);
    let nblocks = blocks.len();
    let rl = rate_lanes(rate);
    let mut states = Vec::with_capacity(segments);
    let mut state = blocks[0];
    for j in 0..segments {
        states.push(state);
        let out = keccak_f1600(&state);
        if j + 1 < nblocks {
            let mut next = out;
            for l in 0..rl {
                next[l] ^= blocks[j + 1][l];
            }
            state = next;
        } else {
            state = out;
        }
    }
    states
}

/// The number of blocks a message of the given rate absorbs, the full blocks and
pub fn absorb_block_count(rate: usize, message: &[u8]) -> usize {
    message.len() / rate + 1
}

/// The number of permutation segments the absorb trace runs, the block count
pub fn absorb_segments(rate: usize, message: &[u8]) -> usize {
    absorb_block_count(rate, message).next_power_of_two()
}

/// The first squeeze block after absorbing the full multi block message, the rate
pub fn absorb_output(rate: usize, message: &[u8]) -> Vec<u8> {
    let nblocks = absorb_block_count(rate, message);
    let states = absorb_states(rate, message, nblocks);
    let out = keccak_f1600(&states[nblocks - 1]);
    let mut bytes = Vec::with_capacity(rate);
    for l in 0..rate_lanes(rate) {
        bytes.extend_from_slice(&out[l].to_le_bytes());
    }
    bytes
}

/// Builds the multi block absorb description over a public message and the public
pub fn absorb_air(rate: usize, message: &[u8], output: &[u8]) -> Air {
    let blocks = Arc::new(absorb_blocks(rate, message));
    let nblocks = blocks.len();
    let segments = nblocks.next_power_of_two();
    let rl = rate_lanes(rate);
    let rows = segments * SEG_ROWS;
    let selb0 = SPONGE_WIDTH;
    let width = SPONGE_WIDTH + nblocks - 1;
    let mut air = Air::new(width, rows);
    add_block_constraints(&mut air, 0);

    // The round and carry transition per state bit, with the rate lanes taking the
    // absorb fold at the boundary rows. On a round row the next bit is the round
    // output, on a plain carry row it is the current bit, and on the boundary row of
    // a rate lane the current bit is exclusive ored with the next block bit.
    for x in 0..5 {
        for y in 0..5 {
            let l = x + 5 * y;
            for z in 0..LANE_BITS {
                let target = s_idx(x, y, z);
                if l < rl {
                    let blocks = blocks.clone();
                    air.add_transition(11, move |current, next| {
                        let sel = current[SEL_COL];
                        let round = round_bit(current, x, y, z);
                        let carried = current[target];
                        let base = sel.mul(round).add(Felt::ONE.sub(sel).mul(carried));
                        let mut adj = Felt::ZERO;
                        for b in 0..nblocks - 1 {
                            let bit = (blocks[b + 1][l] >> z) & 1;
                            if bit == 1 {
                                let flip = Felt::ONE.sub(carried).sub(carried);
                                adj = adj.add(current[selb0 + b].mul(flip));
                            }
                        }
                        next[target].sub(base.add(adj))
                    });
                } else {
                    air.add_transition(11, move |current, next| {
                        let sel = current[SEL_COL];
                        let round = round_bit(current, x, y, z);
                        let carried = current[target];
                        let combined = sel.mul(round).add(Felt::ONE.sub(sel).mul(carried));
                        next[target].sub(combined)
                    });
                }
            }
        }
    }

    // The round selector and round constant at every row.
    let rc = round_constants(SEG_ROWS);
    for global in 0..rows {
        let r = global % SEG_ROWS;
        let sel = if r < KECCAK_ROUNDS {
            Felt::ONE
        } else {
            Felt::ZERO
        };
        air.add_boundary(SEL_COL, global, sel);
        air.add_boundary(RCHALF_OFF, global, Felt::new(rc[r] & 0xffff_ffff));
        air.add_boundary(RCHALF_OFF + 1, global, Felt::new(rc[r] >> 32));
    }

    // The absorb selectors, one per boundary, hot on the last carry row of each non
    // final segment and pinned to zero everywhere else.
    for b in 0..nblocks - 1 {
        let hot = b * SEG_ROWS + SEG_ROWS - 1;
        for global in 0..rows {
            let value = if global == hot { Felt::ONE } else { Felt::ZERO };
            air.add_boundary(selb0 + b, global, value);
        }
    }

    // The first block absorbed over the zero state, all lanes at the first row.
    let first = blocks[0];
    for l in 0..LANES {
        let lo = HALF_OFF + 2 * l;
        let hi = HALF_OFF + 2 * l + 1;
        air.add_boundary(lo, 0, Felt::new(first[l] & 0xffff_ffff));
        air.add_boundary(hi, 0, Felt::new(first[l] >> 32));
    }

    // The first squeeze block, the rate lanes at the round count row of the last
    // segment.
    let out_row = (nblocks - 1) * SEG_ROWS + KECCAK_ROUNDS;
    for l in 0..rl {
        let lane = bytes_to_lane(&output[l * 8..l * 8 + 8]);
        let lo = HALF_OFF + 2 * l;
        let hi = HALF_OFF + 2 * l + 1;
        air.add_boundary(lo, out_row, Felt::new(lane & 0xffff_ffff));
        air.add_boundary(hi, out_row, Felt::new(lane >> 32));
    }

    air
}

/// A filled multi block absorb trace with its description and first squeeze block.
pub struct AbsorbInstance {
    /// The description shared with the verifier.
    pub air: Air,
    /// The filled trace.
    pub trace: TraceTable,
    /// The first squeeze block bytes, the rate.
    pub output: Vec<u8>,
}

/// Builds the multi block absorb trace over the full message. Each segment runs one
pub fn absorb_trace(rate: usize, message: &[u8]) -> AbsorbInstance {
    let nblocks = absorb_block_count(rate, message);
    let segments = nblocks.next_power_of_two();
    let states = absorb_states(rate, message, segments);
    let rc = round_constants(SEG_ROWS);
    let rows = segments * SEG_ROWS;
    let width = SPONGE_WIDTH + nblocks - 1;
    let mut trace = TraceTable::new(width, rows);

    for (j, state_in) in states.iter().enumerate() {
        let seg_states = keccak_states(state_in, KECCAK_ROUNDS);
        for r in 0..SEG_ROWS {
            let global = j * SEG_ROWS + r;
            let state = if r < KECCAK_ROUNDS {
                &seg_states[r]
            } else {
                &seg_states[KECCAK_ROUNDS]
            };
            fill_block_row(&mut trace, 0, global, state, rc[r]);
            let sel = if r < KECCAK_ROUNDS {
                Felt::ONE
            } else {
                Felt::ZERO
            };
            trace.set(SEL_COL, global, sel);
        }
    }
    for b in 0..nblocks - 1 {
        let hot = b * SEG_ROWS + SEG_ROWS - 1;
        trace.set(SPONGE_WIDTH + b, hot, Felt::ONE);
    }

    let output = absorb_output(rate, message);
    let air = absorb_air(rate, message, &output);
    AbsorbInstance { air, trace, output }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark::{prove, verify, StarkParams};
    use qtv_crypto::sha3::{shake128, shake256};

    fn params() -> StarkParams {
        StarkParams {
            lde_blowup: 32,
            num_queries: 24,
        }
    }

    #[test]
    fn the_squeeze_matches_the_crypto_shake256() {
        let message = b"quantova sponge input";
        let perms = 3;
        let ours = shake_output(SHAKE256_RATE, perms, message);
        let mut expected = vec![0u8; perms * SHAKE256_RATE];
        shake256(message, &mut expected);
        assert_eq!(ours, expected);
    }

    #[test]
    fn the_squeeze_matches_the_crypto_shake128() {
        let message = b"seed";
        let perms = 2;
        let ours = shake_output(SHAKE128_RATE, perms, message);
        let mut expected = vec![0u8; perms * SHAKE128_RATE];
        shake128(message, &mut expected);
        assert_eq!(ours, expected);
    }

    #[test]
    fn the_sponge_arithmetic_holds_on_every_row() {
        let instance = shake_trace(SHAKE256_RATE, 2, b"module lattice");
        assert!(instance.air.is_satisfied(&instance.trace));
    }

    // A message spanning several SHAKE256 rate blocks, standing in for the message
    // digest joined with the encoded commitment of the challenge input.
    fn multi_block_message() -> Vec<u8> {
        (0..300u16)
            .map(|i| (i.wrapping_mul(31).wrapping_add(7)) as u8)
            .collect()
    }

    #[test]
    fn the_multi_block_absorb_matches_the_crypto_shake256() {
        let message = multi_block_message();
        assert!(absorb_block_count(SHAKE256_RATE, &message) >= 3);
        let ours = absorb_output(SHAKE256_RATE, &message);
        let mut expected = vec![0u8; SHAKE256_RATE];
        shake256(&message, &mut expected);
        assert_eq!(ours, expected);
    }

    #[test]
    fn the_multi_block_absorb_arithmetic_holds() {
        let instance = absorb_trace(SHAKE256_RATE, &multi_block_message());
        assert!(instance.air.is_satisfied(&instance.trace));
    }

    #[test]
    fn the_multi_block_absorb_proves_and_verifies() {
        let message = multi_block_message();
        let instance = absorb_trace(SHAKE256_RATE, &message);
        let proof = prove(&instance.air, &instance.trace, &params());
        let air = absorb_air(SHAKE256_RATE, &message, &instance.output);
        assert!(verify(&air, &params(), &proof));
    }

    #[test]
    fn a_dropped_absorb_block_is_rejected() {
        // Proving the first block alone against the full input squeeze must fail, so
        // the absorb cannot silently skip the later blocks.
        let message = multi_block_message();
        let full = absorb_output(SHAKE256_RATE, &message);
        let first_block_only = &message[..SHAKE256_RATE - 1];
        let instance = absorb_trace(SHAKE256_RATE, first_block_only);
        let proof = prove(&instance.air, &instance.trace, &params());
        let air = absorb_air(SHAKE256_RATE, first_block_only, &full);
        assert!(!verify(&air, &params(), &proof));
    }

    #[test]
    fn a_tampered_absorb_squeeze_is_rejected() {
        let message = multi_block_message();
        let instance = absorb_trace(SHAKE256_RATE, &message);
        let proof = prove(&instance.air, &instance.trace, &params());
        let mut wrong = instance.output.clone();
        wrong[10] ^= 1;
        let air = absorb_air(SHAKE256_RATE, &message, &wrong);
        assert!(!verify(&air, &params(), &proof));
    }

    #[test]
    fn the_sponge_output_matches_the_crypto_crate() {
        let message = b"digest";
        let instance = shake_trace(SHAKE256_RATE, 2, message);
        let mut expected = vec![0u8; 2 * SHAKE256_RATE];
        shake256(message, &mut expected);
        assert_eq!(instance.output, expected);
    }

    #[test]
    fn a_tampered_squeeze_row_is_rejected() {
        let mut instance = shake_trace(SHAKE256_RATE, 2, b"tamper");
        // Flip a state bit inside the second permutation, which breaks the round
        // that produced it and the squeeze that reads it.
        let cell = instance.trace.get(11, SEG_ROWS + 3);
        instance
            .trace
            .set(11, SEG_ROWS + 3, crate::keccak::xor2(cell, Felt::ONE));
        assert!(!instance.air.is_satisfied(&instance.trace));
    }

    #[test]
    fn the_sponge_proves_and_verifies() {
        let message = b"prove me";
        let instance = shake_trace(SHAKE256_RATE, 2, message);
        let proof = prove(&instance.air, &instance.trace, &params());
        let air = shake_air(SHAKE256_RATE, 2, message, &instance.output);
        assert!(verify(&air, &params(), &proof));
    }

    #[test]
    fn a_proof_for_a_wrong_output_is_rejected() {
        let message = b"prove me";
        let instance = shake_trace(SHAKE256_RATE, 2, message);
        let proof = prove(&instance.air, &instance.trace, &params());
        let mut wrong = instance.output.clone();
        wrong[200] ^= 1;
        let air = shake_air(SHAKE256_RATE, 2, message, &wrong);
        assert!(!verify(&air, &params(), &proof));
    }
}
