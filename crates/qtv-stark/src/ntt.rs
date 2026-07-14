//! Number theoretic transform over the signature modulus, wired into one trace.
//!
//! The transform runs a radix two decimation in time butterfly network over the
//! ring Z_q, where q is the signature modulus. Each row of the trace holds one
//! butterfly. It reads two inputs and a twiddle, forms the twiddle product with
//! its modular reduction, and forms the add and subtract outputs with their own
//! modular reductions, every residue forced into the canonical range by a bit
//! expansion.
//!
//! The butterflies of one layer feed the butterflies of the next, but in the row
//! layout those two rows are far apart. The wiring is carried by a permutation
//! argument. Every produced output and every consumed input is tagged with a
//! wire identity that encodes its layer and index. The argument proves that the
//! multiset of internal produced cells equals the multiset of internal consumed
//! cells, so a value written at one layer index is exactly the value read at the
//! same layer index by the downstream butterfly. The layer zero inputs and the
//! layer L outputs are the public endpoints, pinned by boundaries.

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
const SEL0: usize = D_SLACK + RESIDUE_BITS;

/// The number of base columns for a transform whose layer count is layers.
fn width(layers: u32) -> usize {
    SEL0 + layers as usize
}

/// Modular exponentiation over the signature modulus.
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

/// A primitive n-th root of unity over the signature modulus. The modulus minus
/// one carries a two adic factor large enough for the ring degree.
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

/// Reverses the low log_n bits of an index.
fn bit_reverse(mut value: usize, log_n: u32) -> usize {
    let mut result = 0usize;
    for _ in 0..log_n {
        result = (result << 1) | (value & 1);
        value >>= 1;
    }
    result
}

/// A filled transform trace with its description and public endpoints.
pub struct NttInstance {
    /// The description shared with the verifier.
    pub air: Air,
    /// The filled base trace.
    pub trace: TraceTable,
    /// The layer zero input in the order the butterflies consume it.
    pub input: Vec<u64>,
    /// The layer L output the transform produces.
    pub output: Vec<u64>,
}

// A single butterfly at one layer.
struct Butterfly {
    row: usize,
    step: u32,
    i0: usize,
    i1: usize,
    twiddle: u64,
}

// The decimation in time schedule, interleaved so that the step of a row is the
// row index modulo the layer count. This makes the layer selector a periodic
// rotation that a short constraint can pin.
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

/// Builds the transform trace over the given layer zero input. The input is
/// already in the order the first layer consumes, which is the bit reversal of
/// the natural coefficient order.
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

        state[bf.i0] = s;
        state[bf.i1] = d;
    }

    // The rotating one hot layer selector, hot on the column of the current step.
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

/// Builds the transform description for a ring degree of n over the given public
/// input and output.
pub fn ntt_air(n: usize, input: &[u64], output: &[u64]) -> Air {
    let layers = n.trailing_zeros();
    let rows = (n / 2) * layers as usize;
    let mut air = Air::new(width(layers), rows);
    let modulus = Felt::new(Q);
    let modulus_minus_one = Felt::new(Q - 1);
    let last = layers as usize - 1;

    // The twiddle product residue and its canonical range.
    air.add_single_row(2, move |row| {
        row[W].mul(row[B]).sub(row[MQ].mul(modulus)).sub(row[M])
    });
    air.add_single_row(1, |row| recompose(row, M_BITS).sub(row[M]));
    air.add_single_row(1, move |row| {
        recompose(row, M_SLACK).sub(modulus_minus_one.sub(row[M]))
    });

    // The add output residue with its carry and canonical range.
    air.add_single_row(1, move |row| {
        row[A].add(row[M]).sub(row[CS].mul(modulus)).sub(row[S])
    });
    air.add_single_row(2, |row| row[CS].mul(row[CS].sub(Felt::ONE)));
    air.add_single_row(1, |row| recompose(row, S_BITS).sub(row[S]));
    air.add_single_row(1, move |row| {
        recompose(row, S_SLACK).sub(modulus_minus_one.sub(row[S]))
    });

    // The subtract output residue with its borrow and canonical range.
    air.add_single_row(1, move |row| {
        row[A].sub(row[M]).add(row[CD].mul(modulus)).sub(row[D])
    });
    air.add_single_row(2, |row| row[CD].mul(row[CD].sub(Felt::ONE)));
    air.add_single_row(1, |row| recompose(row, D_BITS).sub(row[D]));
    air.add_single_row(1, move |row| {
        recompose(row, D_SLACK).sub(modulus_minus_one.sub(row[D]))
    });

    // Every range bit is zero or one.
    for base in [M_BITS, M_SLACK, S_BITS, S_SLACK, D_BITS, D_SLACK] {
        for k in 0..RESIDUE_BITS {
            let col = base + k;
            air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
        }
    }

    // The rotating one hot selector, pinned at the first row and shifted by one
    // column each step, so column SEL0 plus k is hot exactly on the rows whose
    // step is k.
    air.add_boundary(SEL0, 0, Felt::ONE);
    for k in 1..layers as usize {
        air.add_boundary(SEL0 + k, 0, Felt::ZERO);
    }
    for j in 0..layers as usize {
        let target = SEL0 + j;
        let source = SEL0 + (j + layers as usize - 1) % layers as usize;
        air.add_wrap_transition(1, move |current, next| next[target].sub(current[source]));
    }

    // The permutation wiring. The compression folds a value with its wire
    // identity under one challenge, and the product runs under a second. Layer
    // zero consumers and layer L producers are masked out, since those cells are
    // the public endpoints.
    let alpha = air.add_challenge();
    let gamma = air.add_challenge();
    let sel_first = SEL0;
    let sel_last = SEL0 + last;
    air.add_permutation(
        3,
        move |row, ch| {
            let mask = row[sel_last];
            let cs = ch[gamma].sub(row[S].add(ch[alpha].mul(row[S_ID])));
            let cd = ch[gamma].sub(row[D].add(ch[alpha].mul(row[D_ID])));
            Felt::ONE.sub(mask).mul(cs.mul(cd)).add(mask)
        },
        move |row, ch| {
            let mask = row[sel_first];
            let ca = ch[gamma].sub(row[A].add(ch[alpha].mul(row[A_ID])));
            let cb = ch[gamma].sub(row[B].add(ch[alpha].mul(row[B_ID])));
            Felt::ONE.sub(mask).mul(ca.mul(cb)).add(mask)
        },
    );

    // Pin the public endpoints. The layer zero inputs are the a and b cells of
    // the first step rows, the layer L outputs are the s and d cells of the last
    // step rows.
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

/// The natural coefficient order rearranged into the layer zero input order.
pub fn to_layer_zero(coeffs: &[u64]) -> Vec<u64> {
    let n = coeffs.len();
    let log_n = n.trailing_zeros();
    (0..n).map(|i| coeffs[bit_reverse(i, log_n)]).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
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
            .map(|i| i.wrapping_mul(0x9e37_79b9).wrapping_add(7) % Q)
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
        let challenges = [Felt::new(0x1234_5678), Felt::new(0x9abc_def0)];
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
        // Corrupt an internal produced value and its bit expansions so the local
        // arithmetic still holds but the wiring no longer matches the consumer.
        let mut instance = ntt_trace(&to_layer_zero(&sample_coeffs(16)));
        let challenges = [Felt::new(0x1234_5678), Felt::new(0x9abc_def0)];
        assert!(instance.air.is_satisfied_with(&instance.trace, &challenges));
        // Row 1 is step one, an internal producer. Swap its two outputs, which
        // keeps the multiset within the row but breaks the per identity match.
        let s = instance.trace.get(S, 1);
        let d = instance.trace.get(D, 1);
        instance.trace.set(S, 1, d);
        instance.trace.set(D, 1, s);
        assert!(!instance.air.is_satisfied_with(&instance.trace, &challenges));
    }

    #[test]
    fn the_transform_proves_and_verifies() {
        let instance = ntt_trace(&to_layer_zero(&sample_coeffs(16)));
        let proof = prove(&instance.air, &instance.trace, &params());
        assert!(verify(&instance.air, &params(), &proof));
    }
}
