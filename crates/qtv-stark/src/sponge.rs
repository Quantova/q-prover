//! The SHAKE sponge over the arithmetized Keccak permutation.
//!
//! A sponge absorbs an input into the state, permutes, and squeezes an output
//! block, permuting again for each further block. This module lays out a trace of
//! several permutations back to back, one thirty two row segment each. Inside a
//! segment the state runs the twenty four rounds; the eight rows past the round
//! count carry the state forward unchanged, so the output of one permutation is
//! the input of the next without a separate wiring argument. The absorb is the
//! padded input block pinned at the first row, and each squeeze block is the rate
//! lanes pinned at the round count row of its segment.
//!
//! The input here fits in one block, which covers a short seed or digest. A
//! proof over this trace shows a SHAKE output was computed correctly from the
//! input, and it matches the crypto crate on known inputs.

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
/// selector.
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
/// of each successive permutation output concatenated to the requested block
/// count.
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
/// public squeeze output. The input block is pinned at the first row and each
/// squeeze block at the round count row of its segment.
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
/// of squeeze permutations.
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
