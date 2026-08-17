// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT


use crate::field::Felt;
use qtv_crypto::sha3::shake256;

pub const WIDTH: usize = 12;

pub const RATE: usize = 8;

pub const CAPACITY: usize = WIDTH - RATE;

pub const ALPHA: u64 = 7;

pub const ALPHA_INV: u64 = 10540996611094048183;

pub const ROUNDS: usize = 8;

const CONSTANT_SEED: &[u8] = b"QVRF/rescue/v1/round-constants";

pub(crate) fn mds() -> [[Felt; WIDTH]; WIDTH] {
    let mut m = [[Felt::ZERO; WIDTH]; WIDTH];
    for (i, row) in m.iter_mut().enumerate() {
        for (j, cell) in row.iter_mut().enumerate() {
            let x = Felt::new(i as u64);
            let y = Felt::new((WIDTH + j) as u64);
            *cell = x.add(y).inv();
        }
    }
    m
}

pub(crate) fn mds_inverse() -> [[Felt; WIDTH]; WIDTH] {
    let mut a = mds();
    let mut inv = [[Felt::ZERO; WIDTH]; WIDTH];
    for i in 0..WIDTH {
        inv[i][i] = Felt::ONE;
    }
    for col in 0..WIDTH {
        let mut pivot = col;
        while a[pivot][col] == Felt::ZERO {
            pivot += 1;
        }
        a.swap(pivot, col);
        inv.swap(pivot, col);
        let scale = a[col][col].inv();
        for k in 0..WIDTH {
            a[col][k] = a[col][k].mul(scale);
            inv[col][k] = inv[col][k].mul(scale);
        }
        for row in 0..WIDTH {
            if row == col {
                continue;
            }
            let factor = a[row][col];
            for k in 0..WIDTH {
                a[row][k] = a[row][k].sub(factor.mul(a[col][k]));
                inv[row][k] = inv[row][k].sub(factor.mul(inv[col][k]));
            }
        }
    }
    inv
}

pub(crate) fn round_constants() -> [[Felt; WIDTH]; 2 * ROUNDS] {
    let mut bytes = vec![0u8; 2 * ROUNDS * WIDTH * 8];
    shake256(CONSTANT_SEED, &mut bytes);
    let mut out = [[Felt::ZERO; WIDTH]; 2 * ROUNDS];
    let mut k = 0;
    for row in out.iter_mut() {
        for cell in row.iter_mut() {
            let mut word = [0u8; 8];
            word.copy_from_slice(&bytes[k * 8..k * 8 + 8]);
            *cell = Felt::new(u64::from_le_bytes(word));
            k += 1;
        }
    }
    out
}

fn apply_mds(m: &[[Felt; WIDTH]; WIDTH], state: &[Felt; WIDTH]) -> [Felt; WIDTH] {
    let mut out = [Felt::ZERO; WIDTH];
    for (i, cell) in out.iter_mut().enumerate() {
        let mut acc = Felt::ZERO;
        for (j, value) in state.iter().enumerate() {
            acc = acc.add(m[i][j].mul(*value));
        }
        *cell = acc;
    }
    out
}

fn sbox(state: &mut [Felt; WIDTH]) {
    for cell in state.iter_mut() {
        *cell = cell.pow(ALPHA);
    }
}

fn inverse_sbox(state: &mut [Felt; WIDTH]) {
    for cell in state.iter_mut() {
        *cell = cell.pow(ALPHA_INV);
    }
}

pub fn permute_states(input: &[Felt; WIDTH]) -> Vec<[Felt; WIDTH]> {
    let m = mds();
    let rc = round_constants();
    let mut states = Vec::with_capacity(ROUNDS + 1);
    let mut state = *input;
    states.push(state);
    for r in 0..ROUNDS {
        sbox(&mut state);
        state = apply_mds(&m, &state);
        for (cell, c) in state.iter_mut().zip(rc[2 * r].iter()) {
            *cell = cell.add(*c);
        }
        inverse_sbox(&mut state);
        state = apply_mds(&m, &state);
        for (cell, c) in state.iter_mut().zip(rc[2 * r + 1].iter()) {
            *cell = cell.add(*c);
        }
        states.push(state);
    }
    states
}

pub fn permute(state: &mut [Felt; WIDTH]) {
    *state = permute_states(state)[ROUNDS];
}

#[cfg(test)]
mod tests {
    use super::*;

    fn inverse_permute(state: &mut [Felt; WIDTH]) {
        let m_inv = mds_inverse();
        let rc = round_constants();
        for r in (0..ROUNDS).rev() {
            for (cell, c) in state.iter_mut().zip(rc[2 * r + 1].iter()) {
                *cell = cell.sub(*c);
            }
            *state = apply_mds(&m_inv, state);
            sbox(state);
            for (cell, c) in state.iter_mut().zip(rc[2 * r].iter()) {
                *cell = cell.sub(*c);
            }
            *state = apply_mds(&m_inv, state);
            inverse_sbox(state);
        }
    }

    fn sample(seed: u64) -> [Felt; WIDTH] {
        let mut state = [Felt::ZERO; WIDTH];
        let mut x = seed | 1;
        for cell in state.iter_mut() {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            *cell = Felt::new(x);
        }
        state
    }

    fn log2_binom(a: u64, b: u64) -> f64 {
        let mut s = 0.0;
        for i in 0..b {
            s += ((a - i) as f64).log2() - ((i + 1) as f64).log2();
        }
        s
    }

    fn rescue_prime_rounds(m: u64, capacity: u64, alpha: u64, security: u64) -> usize {
        let rate = m - capacity;
        let mut l1 = 1u64;
        loop {
            let v = m * (l1 - 1) + rate;
            let dcon = ((alpha - 1) * m * (l1 - 1)) / 2 + 2;
            if log2_binom(v + dcon, v) > security as f64 / 2.0 {
                break;
            }
            l1 += 1;
        }
        let base = l1.max(5) as f64;
        (1.5 * base).ceil() as usize
    }

    #[test]
    fn the_round_count_matches_the_rescue_prime_formula() {
        assert_eq!(
            ROUNDS,
            rescue_prime_rounds(WIDTH as u64, CAPACITY as u64, ALPHA, 128),
            "round count must equal the Rescue-Prime security formula"
        );
    }

    #[test]
    fn the_sbox_exponents_are_inverse() {
        for raw in [2u64, 3, 7, 123456789, 81985529216486895] {
            let x = Felt::new(raw);
            assert_eq!(x.pow(ALPHA).pow(ALPHA_INV), x);
        }
    }

    #[test]
    fn the_mds_is_invertible() {
        let m = mds();
        let inv = mds_inverse();
        let product = apply_mds(&m, &apply_mds(&inv, &sample(1)));
        assert_eq!(product, sample(1));
    }

    #[test]
    fn the_permutation_round_trips_through_its_inverse() {
        let input = sample(42);
        let mut state = input;
        permute(&mut state);
        assert_ne!(state, input);
        inverse_permute(&mut state);
        assert_eq!(state, input);
    }

    #[test]
    fn distinct_inputs_stay_distinct() {
        let mut a = sample(7);
        let mut b = sample(7);
        b[3] = b[3].add(Felt::ONE);
        permute(&mut a);
        permute(&mut b);
        assert_ne!(a, b);
    }

    #[test]
    fn a_one_element_change_avalanches() {
        let mut a = sample(9);
        let mut b = a;
        b[0] = b[0].add(Felt::ONE);
        permute(&mut a);
        permute(&mut b);
        let differing = a.iter().zip(b.iter()).filter(|(x, y)| x != y).count();
        assert!(differing >= WIDTH - 1, "weak diffusion: {differing}");
    }
}
