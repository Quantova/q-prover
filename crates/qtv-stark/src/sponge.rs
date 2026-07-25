// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT


use std::sync::Arc;

use crate::air::{Air, TraceTable};
use crate::field::Felt;
use crate::qudros::{
    add_block_constraints, fill_block_row, qudros_f1600, qudros_states, round_bit, round_constants,
    s_idx, HALF_OFF, QUDROS_ROUNDS, QUDROS_TRACE_ROWS, QUDROS_WIDTH, LANES, LANE_BITS, RCHALF_OFF,
};

pub const SHAKE128_RATE: usize = 168;

pub const SHAKE256_RATE: usize = 136;

pub const SHAKE_DOMAIN: u8 = 31;

const SEG_ROWS: usize = QUDROS_TRACE_ROWS;
const SEL_COL: usize = QUDROS_WIDTH;

pub const SPONGE_WIDTH: usize = QUDROS_WIDTH + 1;

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

fn padded_block(rate: usize, message: &[u8]) -> Vec<u8> {
    assert!(message.len() < rate, "message must fit in one block");
    let mut block = vec![0u8; rate];
    block[..message.len()].copy_from_slice(message);
    block[message.len()] ^= SHAKE_DOMAIN;
    block[rate - 1] ^= 128;
    block
}

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
        let out = qudros_f1600(&state);
        outs.push(out);
        state = out;
    }
    (ins, outs)
}

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

pub const SEGMENT_ROWS: usize = SEG_ROWS;

pub fn squeeze_row(segment: usize) -> usize {
    segment * SEG_ROWS + QUDROS_ROUNDS
}

pub fn lane_low_col(lane: usize) -> usize {
    HALF_OFF + 2 * lane
}

pub fn add_sponge_constraints(
    air: &mut Air,
    rate: usize,
    perms: usize,
    message: &[u8],
    output: &[u8],
) {
    let rows = perms * SEG_ROWS;
    add_block_constraints(air, 0);

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

    let rc = round_constants(SEG_ROWS);
    for global in 0..rows {
        let r = global % SEG_ROWS;
        let sel = if r < QUDROS_ROUNDS {
            Felt::ONE
        } else {
            Felt::ZERO
        };
        air.add_boundary(SEL_COL, global, sel);
        air.add_boundary(RCHALF_OFF, global, Felt::new(rc[r] & 4294967295));
        air.add_boundary(RCHALF_OFF + 1, global, Felt::new(rc[r] >> 32));
    }

    let input = block_to_lanes(&padded_block(rate, message));
    for l in 0..LANES {
        let lo = HALF_OFF + 2 * l;
        let hi = HALF_OFF + 2 * l + 1;
        air.add_boundary(lo, 0, Felt::new(input[l] & 4294967295));
        air.add_boundary(hi, 0, Felt::new(input[l] >> 32));
    }

    let rate_lanes = rate / 8;
    for j in 0..perms {
        let out_row = j * SEG_ROWS + QUDROS_ROUNDS;
        for l in 0..rate_lanes {
            let lane = bytes_to_lane(&output[j * rate + l * 8..j * rate + l * 8 + 8]);
            let lo = HALF_OFF + 2 * l;
            let hi = HALF_OFF + 2 * l + 1;
            air.add_boundary(lo, out_row, Felt::new(lane & 4294967295));
            air.add_boundary(hi, out_row, Felt::new(lane >> 32));
        }
    }
}

pub fn fill_sponge_columns(trace: &mut TraceTable, rate: usize, perms: usize, message: &[u8]) {
    let (ins, _) = sponge_states(rate, perms, message);
    let rc = round_constants(SEG_ROWS);
    for (j, state_in) in ins.iter().enumerate() {
        let states = qudros_states(state_in, QUDROS_ROUNDS);
        for r in 0..SEG_ROWS {
            let global = j * SEG_ROWS + r;
            let state = if r < QUDROS_ROUNDS {
                &states[r]
            } else {
                &states[QUDROS_ROUNDS]
            };
            fill_block_row(trace, 0, global, state, rc[r]);
            let sel = if r < QUDROS_ROUNDS {
                Felt::ONE
            } else {
                Felt::ZERO
            };
            trace.set(SEL_COL, global, sel);
        }
    }
}

pub fn shake_air(rate: usize, perms: usize, message: &[u8], output: &[u8]) -> Air {
    let rows = perms * SEG_ROWS;
    let mut air = Air::new(SPONGE_WIDTH, rows);
    add_sponge_constraints(&mut air, rate, perms, message, output);
    air
}

pub struct SpongeInstance {
    pub air: Air,
    pub trace: TraceTable,
    pub output: Vec<u8>,
}

pub fn shake_trace(rate: usize, perms: usize, message: &[u8]) -> SpongeInstance {
    let rows = perms * SEG_ROWS;
    let mut trace = TraceTable::new(SPONGE_WIDTH, rows);
    fill_sponge_columns(&mut trace, rate, perms, message);
    let output = shake_output(rate, perms, message);
    let air = shake_air(rate, perms, message, &output);
    SpongeInstance { air, trace, output }
}

fn rate_lanes(rate: usize) -> usize {
    rate / 8
}

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
    last[rate - 1] ^= 128;
    blocks.push(block_to_lanes(&last));
    blocks
}

fn absorb_states(rate: usize, message: &[u8], segments: usize) -> Vec<[u64; LANES]> {
    let blocks = absorb_blocks(rate, message);
    let nblocks = blocks.len();
    let rl = rate_lanes(rate);
    let mut states = Vec::with_capacity(segments);
    let mut state = blocks[0];
    for j in 0..segments {
        states.push(state);
        let out = qudros_f1600(&state);
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

pub fn absorb_block_count(rate: usize, message: &[u8]) -> usize {
    message.len() / rate + 1
}

pub fn absorb_segments(rate: usize, message: &[u8]) -> usize {
    absorb_block_count(rate, message).next_power_of_two()
}

pub fn absorb_output(rate: usize, message: &[u8]) -> Vec<u8> {
    let nblocks = absorb_block_count(rate, message);
    let states = absorb_states(rate, message, nblocks);
    let out = qudros_f1600(&states[nblocks - 1]);
    let mut bytes = Vec::with_capacity(rate);
    for l in 0..rate_lanes(rate) {
        bytes.extend_from_slice(&out[l].to_le_bytes());
    }
    bytes
}

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

    let rc = round_constants(SEG_ROWS);
    for global in 0..rows {
        let r = global % SEG_ROWS;
        let sel = if r < QUDROS_ROUNDS {
            Felt::ONE
        } else {
            Felt::ZERO
        };
        air.add_boundary(SEL_COL, global, sel);
        air.add_boundary(RCHALF_OFF, global, Felt::new(rc[r] & 4294967295));
        air.add_boundary(RCHALF_OFF + 1, global, Felt::new(rc[r] >> 32));
    }

    for b in 0..nblocks - 1 {
        let hot = b * SEG_ROWS + SEG_ROWS - 1;
        for global in 0..rows {
            let value = if global == hot { Felt::ONE } else { Felt::ZERO };
            air.add_boundary(selb0 + b, global, value);
        }
    }

    let first = blocks[0];
    for l in 0..LANES {
        let lo = HALF_OFF + 2 * l;
        let hi = HALF_OFF + 2 * l + 1;
        air.add_boundary(lo, 0, Felt::new(first[l] & 4294967295));
        air.add_boundary(hi, 0, Felt::new(first[l] >> 32));
    }

    let out_row = (nblocks - 1) * SEG_ROWS + QUDROS_ROUNDS;
    for l in 0..rl {
        let lane = bytes_to_lane(&output[l * 8..l * 8 + 8]);
        let lo = HALF_OFF + 2 * l;
        let hi = HALF_OFF + 2 * l + 1;
        air.add_boundary(lo, out_row, Felt::new(lane & 4294967295));
        air.add_boundary(hi, out_row, Felt::new(lane >> 32));
    }

    air
}

pub struct AbsorbInstance {
    pub air: Air,
    pub trace: TraceTable,
    pub output: Vec<u8>,
}

pub fn absorb_trace(rate: usize, message: &[u8]) -> AbsorbInstance {
    let nblocks = absorb_block_count(rate, message);
    let segments = nblocks.next_power_of_two();
    let states = absorb_states(rate, message, segments);
    let rc = round_constants(SEG_ROWS);
    let rows = segments * SEG_ROWS;
    let width = SPONGE_WIDTH + nblocks - 1;
    let mut trace = TraceTable::new(width, rows);

    for (j, state_in) in states.iter().enumerate() {
        let seg_states = qudros_states(state_in, QUDROS_ROUNDS);
        for r in 0..SEG_ROWS {
            let global = j * SEG_ROWS + r;
            let state = if r < QUDROS_ROUNDS {
                &seg_states[r]
            } else {
                &seg_states[QUDROS_ROUNDS]
            };
            fill_block_row(&mut trace, 0, global, state, rc[r]);
            let sel = if r < QUDROS_ROUNDS {
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
        let cell = instance.trace.get(11, SEG_ROWS + 3);
        instance
            .trace
            .set(11, SEG_ROWS + 3, crate::qudros::xor2(cell, Felt::ONE));
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
