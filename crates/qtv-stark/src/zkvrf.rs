// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT


use crate::air::{Air, TraceTable};
use crate::codec::{decode_proof, encode_proof};
use crate::field::Felt;
use crate::rescue::{self, ALPHA, ROUNDS, WIDTH};
use crate::stark::{prove_zk, verify_zk, ZkParams};
use qtv_crypto::sha3::shake256;

pub const SK_ELEMS: usize = 4;

pub const X_ELEMS: usize = 4;

pub const OUT_ELEMS: usize = 4;

const RATE: usize = rescue::RATE;

const SEG: usize = 16;

const ROWS: usize = 2 * SEG;

const SEL_COL: usize = WIDTH;

const CA_OFF: usize = WIDTH + 1;

const CB_OFF: usize = CA_OFF + WIDTH;

const INSEL_COL: usize = CB_OFF + WIDTH;

const CARRIER_OFF: usize = INSEL_COL + 1;

const BASE_WIDTH: usize = CARRIER_OFF + SK_ELEMS;

pub const VRF_BLOWUP: usize = 2048;

pub const VRF_QUERIES: usize = 64;

pub const VRF_BLIND: usize = 448;

fn active_round(global: usize) -> Option<usize> {
    if global < ROUNDS {
        Some(global)
    } else if global >= SEG && global < SEG + ROUNDS {
        Some(global - SEG)
    } else {
        None
    }
}

fn state_input(sk: &[Felt; SK_ELEMS], x: &[Felt; X_ELEMS]) -> [Felt; WIDTH] {
    let mut state = [Felt::ZERO; WIDTH];
    state[..SK_ELEMS].copy_from_slice(sk);
    state[SK_ELEMS..RATE].copy_from_slice(x);
    state
}

pub fn vrf_output(sk: &[Felt; SK_ELEMS], x: &[Felt; X_ELEMS]) -> [Felt; OUT_ELEMS] {
    let states = rescue::permute_states(&state_input(sk, x));
    let mut out = [Felt::ZERO; OUT_ELEMS];
    out.copy_from_slice(&states[ROUNDS][..OUT_ELEMS]);
    out
}

pub fn vrf_commit(sk: &[Felt; SK_ELEMS]) -> [Felt; OUT_ELEMS] {
    vrf_output(sk, &[Felt::ZERO; X_ELEMS])
}

pub fn vrf_air(x: &[Felt; X_ELEMS], output: &[Felt; OUT_ELEMS], commit: &[Felt; OUT_ELEMS]) -> Air {
    let m = rescue::mds();
    let minv = rescue::mds_inverse();
    let rc = rescue::round_constants();

    let mut air = Air::new(BASE_WIDTH, ROWS);

    for i in 0..WIDTH {
        air.add_transition(ALPHA as usize + 1, move |cur, next| {
            let sel = cur[SEL_COL];
            let mut lhs = cur[CA_OFF + i];
            for j in 0..WIDTH {
                lhs = lhs.add(m[i][j].mul(cur[j].pow(ALPHA)));
            }
            let mut inner = Felt::ZERO;
            for j in 0..WIDTH {
                inner = inner.add(minv[i][j].mul(next[j].sub(cur[CB_OFF + j])));
            }
            sel.mul(lhs.sub(inner.pow(ALPHA)))
        });
    }

    for k in 0..SK_ELEMS {
        let carrier = CARRIER_OFF + k;
        air.add_transition(1, move |cur, next| next[carrier].sub(cur[carrier]));
    }

    for k in 0..SK_ELEMS {
        let carrier = CARRIER_OFF + k;
        air.add_single_row(2, move |row| row[INSEL_COL].mul(row[k].sub(row[carrier])));
    }

    for global in 0..ROWS {
        let round = active_round(global);
        let sel = if round.is_some() {
            Felt::ONE
        } else {
            Felt::ZERO
        };
        air.add_boundary(SEL_COL, global, sel);
        let insel = if global == 0 || global == SEG {
            Felt::ONE
        } else {
            Felt::ZERO
        };
        air.add_boundary(INSEL_COL, global, insel);
        if let Some(round) = round {
            for i in 0..WIDTH {
                air.add_boundary(CA_OFF + i, global, rc[2 * round][i]);
                air.add_boundary(CB_OFF + i, global, rc[2 * round + 1][i]);
            }
        }
    }

    for j in SK_ELEMS..RATE {
        air.add_boundary(j, 0, x[j - SK_ELEMS]);
    }
    for j in RATE..WIDTH {
        air.add_boundary(j, 0, Felt::ZERO);
    }
    for j in 0..OUT_ELEMS {
        air.add_boundary(j, ROUNDS, output[j]);
    }
    for j in SK_ELEMS..WIDTH {
        air.add_boundary(j, SEG, Felt::ZERO);
    }
    for j in 0..OUT_ELEMS {
        air.add_boundary(j, SEG + ROUNDS, commit[j]);
    }

    air
}

pub fn params() -> ZkParams {
    ZkParams {
        lde_blowup: VRF_BLOWUP,
        num_queries: VRF_QUERIES,
        blind: VRF_BLIND,
    }
}

pub struct Draw {
    pub output: [Felt; OUT_ELEMS],
    pub commit: [Felt; OUT_ELEMS],
    pub proof: Vec<u8>,
}

fn blind_seed(sk: &[Felt; SK_ELEMS], x: &[Felt; X_ELEMS], context: &[u8]) -> [u8; 32] {
    let mut buf = Vec::with_capacity(16 + (SK_ELEMS + X_ELEMS) * 8 + context.len());
    buf.extend_from_slice(b"QVRF/rescue/blind/v1");
    for e in sk {
        buf.extend_from_slice(&e.to_u64().to_le_bytes());
    }
    for e in x {
        buf.extend_from_slice(&e.to_u64().to_le_bytes());
    }
    buf.extend_from_slice(context);
    let mut out = [0u8; 32];
    shake256(&buf, &mut out);
    out
}

pub fn prove(sk: &[Felt; SK_ELEMS], x: &[Felt; X_ELEMS], context: &[u8]) -> Draw {
    let seed = blind_seed(sk, x, context);
    let instance = vrf_trace(sk, x);
    let proof = prove_zk(&instance.air, &instance.trace, &params(), context, &seed);
    Draw {
        output: instance.output,
        commit: instance.commit,
        proof: encode_proof(&proof),
    }
}

pub fn verify(
    x: &[Felt; X_ELEMS],
    output: &[Felt; OUT_ELEMS],
    commit: &[Felt; OUT_ELEMS],
    proof: &[u8],
    context: &[u8],
) -> bool {
    let proof = match decode_proof(proof) {
        Some(proof) => proof,
        None => return false,
    };
    let air = vrf_air(x, output, commit);
    verify_zk(&air, &params(), &proof, context)
}

pub struct VrfInstance {
    pub air: Air,
    pub trace: TraceTable,
    pub output: [Felt; OUT_ELEMS],
    pub commit: [Felt; OUT_ELEMS],
}

fn fill_segment(trace: &mut TraceTable, base_row: usize, input: &[Felt; WIDTH], rc: &[[Felt; WIDTH]]) {
    let states = rescue::permute_states(input);
    for r in 0..SEG {
        let global = base_row + r;
        let state = if r <= ROUNDS { &states[r] } else { &states[ROUNDS] };
        for (col, value) in state.iter().enumerate() {
            trace.set(col, global, *value);
        }
        let round = active_round(global);
        let sel = if round.is_some() {
            Felt::ONE
        } else {
            Felt::ZERO
        };
        trace.set(SEL_COL, global, sel);
        if let Some(round) = round {
            for i in 0..WIDTH {
                trace.set(CA_OFF + i, global, rc[2 * round][i]);
                trace.set(CB_OFF + i, global, rc[2 * round + 1][i]);
            }
        }
    }
}

pub fn vrf_trace(sk: &[Felt; SK_ELEMS], x: &[Felt; X_ELEMS]) -> VrfInstance {
    let output = vrf_output(sk, x);
    let commit = vrf_commit(sk);
    let rc = rescue::round_constants();

    let mut trace = TraceTable::new(BASE_WIDTH, ROWS);
    fill_segment(&mut trace, 0, &state_input(sk, x), &rc);
    fill_segment(&mut trace, SEG, &state_input(sk, &[Felt::ZERO; X_ELEMS]), &rc);

    for global in 0..ROWS {
        let insel = if global == 0 || global == SEG {
            Felt::ONE
        } else {
            Felt::ZERO
        };
        trace.set(INSEL_COL, global, insel);
        for k in 0..SK_ELEMS {
            trace.set(CARRIER_OFF + k, global, sk[k]);
        }
    }

    let air = vrf_air(x, &output, &commit);
    VrfInstance {
        air,
        trace,
        output,
        commit,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark::{prove, verify, StarkParams};
    use std::collections::HashSet;

    fn sk() -> [Felt; SK_ELEMS] {
        [
            Felt::new(111111111),
            Felt::new(222222222),
            Felt::new(333333333),
            Felt::new(444444444),
        ]
    }

    fn input() -> [Felt; X_ELEMS] {
        [
            Felt::new(9001),
            Felt::new(9002),
            Felt::new(9003),
            Felt::new(9004),
        ]
    }

    fn sound_params() -> StarkParams {
        StarkParams {
            lde_blowup: 16,
            num_queries: 32,
        }
    }

    #[test]
    fn the_reference_output_matches_the_permutation() {
        let s = sk();
        let x = input();
        let mut state = state_input(&s, &x);
        rescue::permute(&mut state);
        assert_eq!(&vrf_output(&s, &x)[..], &state[..OUT_ELEMS]);
    }

    #[test]
    fn the_arithmetic_holds_on_every_row() {
        let instance = vrf_trace(&sk(), &input());
        assert!(instance.air.is_satisfied(&instance.trace));
    }

    #[test]
    fn a_valid_draw_proves_and_verifies() {
        let instance = vrf_trace(&sk(), &input());
        let proof = prove(&instance.air, &instance.trace, &sound_params());
        let air = vrf_air(&input(), &instance.output, &instance.commit);
        assert!(verify(&air, &sound_params(), &proof));
    }

    #[test]
    fn a_forged_output_is_rejected() {
        let instance = vrf_trace(&sk(), &input());
        let proof = prove(&instance.air, &instance.trace, &sound_params());
        let mut wrong = instance.output;
        wrong[0] = wrong[0].add(Felt::ONE);
        let air = vrf_air(&input(), &wrong, &instance.commit);
        assert!(!verify(&air, &sound_params(), &proof));
    }

    #[test]
    fn a_wrong_commitment_is_rejected() {
        let instance = vrf_trace(&sk(), &input());
        let proof = prove(&instance.air, &instance.trace, &sound_params());
        let mut wrong = instance.commit;
        wrong[2] = wrong[2].add(Felt::ONE);
        let air = vrf_air(&input(), &instance.output, &wrong);
        assert!(!verify(&air, &sound_params(), &proof));
    }

    #[test]
    fn a_different_input_is_rejected() {
        let instance = vrf_trace(&sk(), &input());
        let proof = prove(&instance.air, &instance.trace, &sound_params());
        let mut other = input();
        other[0] = other[0].add(Felt::ONE);
        let air = vrf_air(&other, &instance.output, &instance.commit);
        assert!(!verify(&air, &sound_params(), &proof));
    }

    #[test]
    fn a_key_split_between_the_two_sponges_is_rejected() {
        let mut instance = vrf_trace(&sk(), &input());
        let mut other = sk();
        other[0] = other[0].add(Felt::ONE);
        let rc = rescue::round_constants();
        fill_segment(&mut instance.trace, SEG, &state_input(&other, &[Felt::ZERO; X_ELEMS]), &rc);
        assert!(!instance.air.is_satisfied(&instance.trace));
    }

    #[test]
    fn a_tampered_carrier_is_rejected() {
        let mut instance = vrf_trace(&sk(), &input());
        let cell = instance.trace.get(CARRIER_OFF, 0);
        instance.trace.set(CARRIER_OFF, 0, cell.add(Felt::ONE));
        assert!(!instance.air.is_satisfied(&instance.trace));
    }

    #[test]
    fn a_blinded_draw_proves_and_verifies() {
        let instance = vrf_trace(&sk(), &input());
        let proof = prove_zk(&instance.air, &instance.trace, &params(), b"vrf", &[1u8; 32]);
        let air = vrf_air(&input(), &instance.output, &instance.commit);
        assert!(verify_zk(&air, &params(), &proof, b"vrf"));
    }

    #[test]
    fn a_blinded_forged_output_is_rejected() {
        let instance = vrf_trace(&sk(), &input());
        let proof = prove_zk(&instance.air, &instance.trace, &params(), b"vrf", &[2u8; 32]);
        let mut wrong = instance.output;
        wrong[1] = wrong[1].add(Felt::ONE);
        let air = vrf_air(&input(), &wrong, &instance.commit);
        assert!(!verify_zk(&air, &params(), &proof, b"vrf"));
    }

    #[test]
    fn blinding_randomizes_the_commitment_across_seeds() {
        let instance = vrf_trace(&sk(), &input());
        let a = prove_zk(&instance.air, &instance.trace, &params(), b"vrf", &[3u8; 32]);
        let b = prove_zk(&instance.air, &instance.trace, &params(), b"vrf", &[4u8; 32]);
        assert_ne!(a.trace_root, b.trace_root);
        let air = vrf_air(&input(), &instance.output, &instance.commit);
        assert!(verify_zk(&air, &params(), &a, b"vrf"));
        assert!(verify_zk(&air, &params(), &b, b"vrf"));
    }

    #[test]
    fn the_blinding_margin_covers_every_opening() {
        let instance = vrf_trace(&sk(), &input());
        let proof = prove_zk(&instance.air, &instance.trace, &params(), b"vrf", &[5u8; 32]);
        let mut positions = HashSet::new();
        for q in &proof.openings {
            for r in &q.rows {
                positions.insert(r.index);
            }
        }
        for q in &proof.trace_openings {
            for r in &q.rows {
                positions.insert(r.index);
            }
        }
        assert!(
            VRF_BLIND >= positions.len(),
            "blinding {} must cover {} openings",
            VRF_BLIND,
            positions.len()
        );
    }

    #[test]
    fn the_parameters_meet_the_target_soundness() {
        let n = ROWS;
        let max_degree = ALPHA as usize + 1;
        let size = n * VRF_BLOWUP;
        let comp_bound = (max_degree * (n + VRF_BLIND)).next_power_of_two();
        let comp_fri_blowup = size / comp_bound;
        let bits = VRF_QUERIES as f64 * 0.5 * (comp_fri_blowup as f64).log2();
        assert!(bits >= 128.0, "composition soundness {bits} bits below target");
        let openings = 6 * VRF_QUERIES;
        assert!(
            VRF_BLIND >= openings,
            "blinding {VRF_BLIND} below the {openings} openings"
        );
    }

    #[test]
    fn the_byte_api_round_trips_and_binds_context() {
        let draw = super::prove(&sk(), &input(), b"chain/slot-7");
        assert!(super::verify(&input(), &draw.output, &draw.commit, &draw.proof, b"chain/slot-7"));
        assert!(!super::verify(&input(), &draw.output, &draw.commit, &draw.proof, b"chain/slot-8"));
    }

    #[test]
    fn a_tampered_proof_is_rejected() {
        let draw = super::prove(&sk(), &input(), b"vrf");
        let mut bad = draw.proof.clone();
        let mid = bad.len() / 2;
        bad[mid] ^= 1;
        assert!(!super::verify(&input(), &draw.output, &draw.commit, &bad, b"vrf"));
    }

    #[test]
    fn the_byte_api_rejects_a_swapped_output() {
        let draw = super::prove(&sk(), &input(), b"vrf");
        let mut wrong = draw.output;
        wrong[0] = wrong[0].add(Felt::ONE);
        assert!(!super::verify(&input(), &wrong, &draw.commit, &draw.proof, b"vrf"));
    }

    #[test]
    fn the_blinding_is_deterministic_and_key_dependent() {
        let a = super::prove(&sk(), &input(), b"vrf");
        let b = super::prove(&sk(), &input(), b"vrf");
        assert_eq!(a.proof, b.proof);
        let mut other = sk();
        other[0] = other[0].add(Felt::ONE);
        let c = super::prove(&other, &input(), b"vrf");
        assert_ne!(a.proof, c.proof);
    }
}
