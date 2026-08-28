// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::air::{Air, TraceTable};
use crate::field::Felt;
use crate::lattice::{Q, RESIDUE_BITS};

const A: usize = 0;
const B: usize = 1;
const W: usize = 2;
const M: usize = 3;
const S: usize = 4;
const D: usize = 5;
const MQ: usize = 6;
const CS: usize = 7;
const CD: usize = 8;
const A_ID: usize = 9;
const B_ID: usize = 10;
const S_ID: usize = 11;
const D_ID: usize = 12;
const M_BITS: usize = 13;
const M_SLACK: usize = M_BITS + RESIDUE_BITS;
const S_BITS: usize = M_SLACK + RESIDUE_BITS;
const S_SLACK: usize = S_BITS + RESIDUE_BITS;
const D_BITS: usize = S_SLACK + RESIDUE_BITS;
const D_SLACK: usize = D_BITS + RESIDUE_BITS;
const MQ_BITS: usize = D_SLACK + RESIDUE_BITS;
const SEL0: usize = MQ_BITS + RESIDUE_BITS;

fn width(layers: u32) -> usize {
    SEL0 + layers as usize
}

fn pow_mod(base: u64, mut exp: u64, modulus: u64) -> u64 {
    let mut result = 1u128;
    let mut b = base as u128 % modulus as u128;
    while exp > 0 {
        if exp & 1 == 1 {
            result = result * b % modulus as u128;
        }
        b = b * b % modulus as u128;
        exp >>= 1;
    }
    result as u64
}

pub fn root_of_unity_q(n: usize) -> u64 {
    assert!(n.is_power_of_two());
    let exponent = (Q - 1) / n as u64;
    for base in 2u64..64 {
        let candidate = pow_mod(base, exponent, Q);
        if pow_mod(candidate, n as u64, Q) == 1 && pow_mod(candidate, (n / 2) as u64, Q) != 1 {
            return candidate;
        }
    }
    panic!("no primitive root of unity of the requested order");
}

fn recompose(row: &[Felt], base: usize) -> Felt {
    let two = Felt::new(2);
    let mut acc = Felt::ZERO;
    let mut weight = Felt::ONE;
    for k in 0..RESIDUE_BITS {
        acc = acc.add(row[base + k].mul(weight));
        weight = weight.mul(two);
    }
    acc
}

fn set_bits(trace: &mut TraceTable, base: usize, row: usize, value: u64) {
    for k in 0..RESIDUE_BITS {
        trace.set(base + k, row, Felt::new((value >> k) & 1));
    }
}

fn bit_reverse(mut value: usize, log_n: u32) -> usize {
    let mut result = 0usize;
    for _ in 0..log_n {
        result = (result << 1) | (value & 1);
        value >>= 1;
    }
    result
}

pub struct NttInstance {
    pub air: Air,
    pub trace: TraceTable,
    pub input: Vec<u64>,
    pub output: Vec<u64>,
}

struct Butterfly {
    row: usize,
    step: u32,
    i0: usize,
    i1: usize,
    twiddle: u64,
}

fn schedule(n: usize, layers: u32, omega: u64) -> Vec<Butterfly> {
    let mut out = Vec::with_capacity((n / 2) * layers as usize);
    for step in 0..layers {
        let len = 1usize << (step + 1);
        let half = len / 2;
        let root = pow_mod(omega, (n / len) as u64, Q);
        for p in 0..n / 2 {
            let block = p / half;
            let offset = p % half;
            let base = block * len;
            let i0 = base + offset;
            let i1 = base + half + offset;
            let twiddle = pow_mod(root, offset as u64, Q);
            let row = p * layers as usize + step as usize;
            out.push(Butterfly {
                row,
                step,
                i0,
                i1,
                twiddle,
            });
        }
    }
    out
}

fn identity(layer: u32, index: usize, n: usize) -> u64 {
    (layer as u64) * (n as u64) + index as u64
}

pub fn ntt_trace(input: &[u64]) -> NttInstance {
    let n = input.len();
    assert!(
        n.is_power_of_two() && n >= 2,
        "ring degree must be a power of two"
    );
    let layers = n.trailing_zeros();
    let rows = (n / 2) * layers as usize;
    assert!(
        rows.is_power_of_two(),
        "the row count must be a power of two"
    );

    let omega = root_of_unity_q(n);
    let plan = schedule(n, layers, omega);

    let mut state: Vec<u64> = input.to_vec();
    let mut trace = TraceTable::new(width(layers), rows);

    for bf in &plan {
        let a = state[bf.i0];
        let b = state[bf.i1];
        let product = (bf.twiddle as u128) * (b as u128);
        let mq = (product / Q as u128) as u64;
        let m = (product % Q as u128) as u64;
        let sum = a + m;
        let cs = if sum >= Q { 1u64 } else { 0 };
        let s = sum - cs * Q;
        let cd = if a >= m { 0u64 } else { 1 };
        let d = a + cd * Q - m;

        trace.set(A, bf.row, Felt::new(a));
        trace.set(B, bf.row, Felt::new(b));
        trace.set(W, bf.row, Felt::new(bf.twiddle));
        trace.set(M, bf.row, Felt::new(m));
        trace.set(S, bf.row, Felt::new(s));
        trace.set(D, bf.row, Felt::new(d));
        trace.set(MQ, bf.row, Felt::new(mq));
        trace.set(CS, bf.row, Felt::new(cs));
        trace.set(CD, bf.row, Felt::new(cd));
        trace.set(A_ID, bf.row, Felt::new(identity(bf.step, bf.i0, n)));
        trace.set(B_ID, bf.row, Felt::new(identity(bf.step, bf.i1, n)));
        trace.set(S_ID, bf.row, Felt::new(identity(bf.step + 1, bf.i0, n)));
        trace.set(D_ID, bf.row, Felt::new(identity(bf.step + 1, bf.i1, n)));
        set_bits(&mut trace, M_BITS, bf.row, m);
        set_bits(&mut trace, M_SLACK, bf.row, Q - 1 - m);
        set_bits(&mut trace, S_BITS, bf.row, s);
        set_bits(&mut trace, S_SLACK, bf.row, Q - 1 - s);
        set_bits(&mut trace, D_BITS, bf.row, d);
        set_bits(&mut trace, D_SLACK, bf.row, Q - 1 - d);
        set_bits(&mut trace, MQ_BITS, bf.row, mq);

        state[bf.i0] = s;
        state[bf.i1] = d;
    }

    for row in 0..rows {
        let step = row % layers as usize;
        trace.set(SEL0 + step, row, Felt::ONE);
    }

    let output = state;
    let air = ntt_air(n, input, &output);
    NttInstance {
        air,
        trace,
        input: input.to_vec(),
        output,
    }
}

pub fn ntt_air(n: usize, input: &[u64], output: &[u64]) -> Air {
    let layers = n.trailing_zeros();
    let rows = (n / 2) * layers as usize;
    let mut air = Air::new(width(layers), rows);
    let modulus = Felt::new(Q);
    let modulus_minus_one = Felt::new(Q - 1);
    let last = layers as usize - 1;

    let omega = root_of_unity_q(n);
    for bf in &schedule(n, layers, omega) {
        air.add_boundary(W, bf.row, Felt::new(bf.twiddle));
    }

    air.add_single_row(2, move |row| {
        row[W].mul(row[B]).sub(row[MQ].mul(modulus)).sub(row[M])
    });
    air.add_single_row(1, |row| recompose(row, M_BITS).sub(row[M]));
    air.add_single_row(1, move |row| {
        recompose(row, M_SLACK).sub(modulus_minus_one.sub(row[M]))
    });
    air.add_single_row(1, |row| recompose(row, MQ_BITS).sub(row[MQ]));

    air.add_single_row(1, move |row| {
        row[A].add(row[M]).sub(row[CS].mul(modulus)).sub(row[S])
    });
    air.add_single_row(2, |row| row[CS].mul(row[CS].sub(Felt::ONE)));
    air.add_single_row(1, |row| recompose(row, S_BITS).sub(row[S]));
    air.add_single_row(1, move |row| {
        recompose(row, S_SLACK).sub(modulus_minus_one.sub(row[S]))
    });

    air.add_single_row(1, move |row| {
        row[A].sub(row[M]).add(row[CD].mul(modulus)).sub(row[D])
    });
    air.add_single_row(2, |row| row[CD].mul(row[CD].sub(Felt::ONE)));
    air.add_single_row(1, |row| recompose(row, D_BITS).sub(row[D]));
    air.add_single_row(1, move |row| {
        recompose(row, D_SLACK).sub(modulus_minus_one.sub(row[D]))
    });

    for base in [M_BITS, M_SLACK, S_BITS, S_SLACK, D_BITS, D_SLACK, MQ_BITS] {
        for k in 0..RESIDUE_BITS {
            let col = base + k;
            air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
        }
    }

    air.add_boundary(SEL0, 0, Felt::ONE);
    for k in 1..layers as usize {
        air.add_boundary(SEL0 + k, 0, Felt::ZERO);
    }
    for j in 0..layers as usize {
        let target = SEL0 + j;
        let source = SEL0 + (j + layers as usize - 1) % layers as usize;
        air.add_wrap_transition(1, move |current, next| next[target].sub(current[source]));
    }

    let alpha = air.add_challenge();
    let gamma = air.add_challenge();
    let sel_first = SEL0;
    let sel_last = SEL0 + last;
    air.add_permutation(
        3,
        move |row, ch| {
            let mask = row[sel_last];
            let cs = ch[gamma].sub(ch[alpha].scale(row[S_ID]).add_base(row[S]));
            let cd = ch[gamma].sub(ch[alpha].scale(row[D_ID]).add_base(row[D]));
            cs.mul(cd).scale(Felt::ONE.sub(mask)).add_base(mask)
        },
        move |row, ch| {
            let mask = row[sel_first];
            let ca = ch[gamma].sub(ch[alpha].scale(row[A_ID]).add_base(row[A]));
            let cb = ch[gamma].sub(ch[alpha].scale(row[B_ID]).add_base(row[B]));
            ca.mul(cb).scale(Felt::ONE.sub(mask)).add_base(mask)
        },
    );

    let half = n / 2;
    for p in 0..half {
        let first_row = p * layers as usize;
        air.add_boundary(A, first_row, Felt::new(input[2 * p]));
        air.add_boundary(B, first_row, Felt::new(input[2 * p + 1]));
        let last_row = p * layers as usize + last;
        air.add_boundary(S, last_row, Felt::new(output[p]));
        air.add_boundary(D, last_row, Felt::new(output[p + half]));
    }

    air
}

pub fn to_layer_zero(coeffs: &[u64]) -> Vec<u64> {
    let n = coeffs.len();
    let log_n = n.trailing_zeros();
    (0..n).map(|i| coeffs[bit_reverse(i, log_n)]).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field_ext::Fp3;
    use crate::stark::{prove, verify, StarkParams};

    fn params() -> StarkParams {
        StarkParams {
            lde_blowup: 8,
            num_queries: 24,
        }
    }

    fn naive_dft(coeffs: &[u64]) -> Vec<u64> {
        let n = coeffs.len();
        let omega = root_of_unity_q(n);
        (0..n)
            .map(|k| {
                let mut acc = 0u128;
                for (j, c) in coeffs.iter().enumerate() {
                    let tw = pow_mod(omega, (j as u64) * (k as u64), Q);
                    acc = (acc + (*c as u128) * (tw as u128)) % Q as u128;
                }
                acc as u64
            })
            .collect()
    }

    fn sample_coeffs(n: usize) -> Vec<u64> {
        (0..n as u64)
            .map(|i| i.wrapping_mul(2654435769).wrapping_add(7) % Q)
            .collect()
    }

    #[test]
    fn the_schedule_computes_the_transform() {
        let n = 16;
        let coeffs = sample_coeffs(n);
        let instance = ntt_trace(&to_layer_zero(&coeffs));
        assert_eq!(instance.output, naive_dft(&coeffs));
    }

    #[test]
    fn the_arithmetic_holds_on_every_row() {
        let instance = ntt_trace(&to_layer_zero(&sample_coeffs(16)));
        assert!(instance.air.is_satisfied(&instance.trace));
    }

    #[test]
    fn the_whole_relation_holds_under_challenges() {
        let instance = ntt_trace(&to_layer_zero(&sample_coeffs(16)));
        let challenges = [Fp3::new(Felt::new(305419896), Felt::new(11), Felt::new(97)), Fp3::new(Felt::new(2596069104), Felt::new(23), Felt::new(131))];
        assert!(instance.air.is_satisfied_with(&instance.trace, &challenges));
    }

    #[test]
    fn a_broken_butterfly_is_rejected() {
        let mut instance = ntt_trace(&to_layer_zero(&sample_coeffs(16)));
        instance
            .trace
            .set(S, 5, instance.trace.get(S, 5).add(Felt::ONE));
        assert!(!instance.air.is_satisfied(&instance.trace));
    }

    #[test]
    fn a_broken_wire_is_rejected() {
        let mut instance = ntt_trace(&to_layer_zero(&sample_coeffs(16)));
        let challenges = [Fp3::new(Felt::new(305419896), Felt::new(11), Felt::new(97)), Fp3::new(Felt::new(2596069104), Felt::new(23), Felt::new(131))];
        assert!(instance.air.is_satisfied_with(&instance.trace, &challenges));
        let s = instance.trace.get(S, 1);
        let d = instance.trace.get(D, 1);
        instance.trace.set(S, 1, d);
        instance.trace.set(D, 1, s);
        assert!(!instance.air.is_satisfied_with(&instance.trace, &challenges));
    }

    #[test]
    fn a_forged_butterfly_product_is_rejected() {
        let a = 1234u64;
        let b = 5678u64;
        let input = vec![a, b];
        let forged_m = b + 1;
        assert!(forged_m < Q);
        let mq = Felt::new(b)
            .sub(Felt::new(forged_m))
            .mul(Felt::new(Q).inv());
        let (s, cs) = if a + forged_m >= Q {
            (a + forged_m - Q, 1u64)
        } else {
            (a + forged_m, 0)
        };
        let (d, cd) = if a >= forged_m {
            (a - forged_m, 0u64)
        } else {
            (a + Q - forged_m, 1)
        };
        let output = vec![s, d];
        assert_ne!(forged_m, (Felt::ONE.mul(Felt::new(b))).to_u64());
        let mut trace = TraceTable::new(width(1), 1);
        trace.set(A, 0, Felt::new(a));
        trace.set(B, 0, Felt::new(b));
        trace.set(W, 0, Felt::ONE);
        trace.set(M, 0, Felt::new(forged_m));
        trace.set(S, 0, Felt::new(s));
        trace.set(D, 0, Felt::new(d));
        trace.set(MQ, 0, mq);
        trace.set(CS, 0, Felt::new(cs));
        trace.set(CD, 0, Felt::new(cd));
        trace.set(A_ID, 0, Felt::new(identity(0, 0, 2)));
        trace.set(B_ID, 0, Felt::new(identity(0, 1, 2)));
        trace.set(S_ID, 0, Felt::new(identity(1, 0, 2)));
        trace.set(D_ID, 0, Felt::new(identity(1, 1, 2)));
        set_bits(&mut trace, M_BITS, 0, forged_m);
        set_bits(&mut trace, M_SLACK, 0, Q - 1 - forged_m);
        set_bits(&mut trace, S_BITS, 0, s);
        set_bits(&mut trace, S_SLACK, 0, Q - 1 - s);
        set_bits(&mut trace, D_BITS, 0, d);
        set_bits(&mut trace, D_SLACK, 0, Q - 1 - d);
        trace.set(SEL0, 0, Felt::ONE);
        let air = ntt_air(2, &input, &output);
        assert!(!air.is_satisfied(&trace));
    }

    #[test]
    fn the_twiddle_column_is_pinned_on_every_row() {
        let n = 16usize;
        let layers = (n as u32).trailing_zeros();
        let omega = root_of_unity_q(n);
        let plan = schedule(n, layers, omega);
        let air = ntt_air(n, &to_layer_zero(&sample_coeffs(n)), &vec![0u64; n]);
        for bf in &plan {
            assert!(air
                .boundaries()
                .iter()
                .any(|b| b.column == W && b.row == bf.row && b.value == Felt::new(bf.twiddle)));
        }
    }

    #[test]
    fn a_forged_twiddle_producing_a_false_output_is_rejected() {
        let coeffs = sample_coeffs(16);
        let instance = ntt_trace(&to_layer_zero(&coeffs));
        let challenges = [Fp3::new(Felt::new(305419896), Felt::new(11), Felt::new(97)), Fp3::new(Felt::new(2596069104), Felt::new(23), Felt::new(131))];
        let n = 16usize;
        let layers = (n as u32).trailing_zeros();
        let last = layers as usize - 1;
        let victim_row = last;
        let input = instance.input.clone();
        let honest_output = instance.output.clone();
        let a_val = instance.trace.get(A, victim_row).to_u64();
        let b_val = instance.trace.get(B, victim_row).to_u64();
        let honest_w = instance.trace.get(W, victim_row).to_u64();
        let forged_w = 3u64;
        assert_ne!(forged_w, honest_w);
        let product = forged_w as u128 * b_val as u128;
        let mq = (product / Q as u128) as u64;
        let m = (product % Q as u128) as u64;
        let (s, cs) = {
            let sum = a_val + m;
            if sum >= Q {
                (sum - Q, 1u64)
            } else {
                (sum, 0)
            }
        };
        let (d, cd) = if a_val >= m {
            (a_val - m, 0u64)
        } else {
            (a_val + Q - m, 1)
        };
        let half = n / 2;
        let mut forged_output = honest_output.clone();
        forged_output[0] = s;
        forged_output[half] = d;
        assert_ne!(forged_output, honest_output);
        let mut trace = instance.trace;
        trace.set(W, victim_row, Felt::new(forged_w));
        trace.set(M, victim_row, Felt::new(m));
        trace.set(MQ, victim_row, Felt::new(mq));
        trace.set(S, victim_row, Felt::new(s));
        trace.set(D, victim_row, Felt::new(d));
        trace.set(CS, victim_row, Felt::new(cs));
        trace.set(CD, victim_row, Felt::new(cd));
        set_bits(&mut trace, M_BITS, victim_row, m);
        set_bits(&mut trace, M_SLACK, victim_row, Q - 1 - m);
        set_bits(&mut trace, S_BITS, victim_row, s);
        set_bits(&mut trace, S_SLACK, victim_row, Q - 1 - s);
        set_bits(&mut trace, D_BITS, victim_row, d);
        set_bits(&mut trace, D_SLACK, victim_row, Q - 1 - d);
        set_bits(&mut trace, MQ_BITS, victim_row, mq);
        let air = ntt_air(n, &input, &forged_output);
        assert!(!air.is_satisfied_with(&trace, &challenges));
        let proof = prove(&air, &trace, &params());
        assert!(!verify(&air, &params(), &proof));
    }

    #[test]
    fn the_transform_proves_and_verifies() {
        let instance = ntt_trace(&to_layer_zero(&sample_coeffs(16)));
        let proof = prove(&instance.air, &instance.trace, &params());
        assert!(verify(&instance.air, &params(), &proof));
    }
}
