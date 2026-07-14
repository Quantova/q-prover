//! Polynomial transforms over the Goldilocks subgroups.

use crate::field::{root_of_unity, Felt};

/// In place radix two transform. On return values[i] holds the evaluation of the
pub fn ntt(values: &mut [Felt], omega: Felt) {
    let n = values.len();
    assert!(n.is_power_of_two(), "length must be a power of two");

    let mut j = 0usize;
    for i in 1..n {
        let mut bit = n >> 1;
        while j & bit != 0 {
            j ^= bit;
            bit >>= 1;
        }
        j ^= bit;
        if i < j {
            values.swap(i, j);
        }
    }

    let mut len = 2usize;
    while len <= n {
        let step = omega.pow((n / len) as u64);
        let mut base = 0usize;
        while base < n {
            let mut twiddle = Felt::ONE;
            for k in 0..(len / 2) {
                let low = values[base + k];
                let high = values[base + k + len / 2].mul(twiddle);
                values[base + k] = low.add(high);
                values[base + k + len / 2] = low.sub(high);
                twiddle = twiddle.mul(step);
            }
            base += len;
        }
        len <<= 1;
    }
}

/// Interpolates evaluations sampled over the subgroup of their own length and
pub fn interpolate(evaluations: &[Felt]) -> Vec<Felt> {
    let n = evaluations.len();
    assert!(n.is_power_of_two(), "length must be a power of two");
    let log_n = n.trailing_zeros();
    let omega = root_of_unity(log_n);
    let mut coeffs = evaluations.to_vec();
    ntt(&mut coeffs, omega.inv());
    let scale = Felt::new(n as u64).inv();
    for c in coeffs.iter_mut() {
        *c = c.mul(scale);
    }
    coeffs
}

/// Evaluates a coefficient vector over the subgroup of a chosen larger order.
pub fn evaluate_subgroup(coeffs: &[Felt], log_size: u32) -> Vec<Felt> {
    let size = 1usize << log_size;
    assert!(
        coeffs.len() <= size,
        "target domain is smaller than the input"
    );
    let mut padded = coeffs.to_vec();
    padded.resize(size, Felt::ZERO);
    ntt(&mut padded, root_of_unity(log_size));
    padded
}

/// Evaluates a coefficient vector over a coset of the subgroup, namely the shift
pub fn evaluate_coset(coeffs: &[Felt], log_size: u32, shift: Felt) -> Vec<Felt> {
    let size = 1usize << log_size;
    assert!(
        coeffs.len() <= size,
        "target domain is smaller than the input"
    );
    let mut padded = coeffs.to_vec();
    padded.resize(size, Felt::ZERO);
    let mut power = Felt::ONE;
    for c in padded.iter_mut() {
        *c = c.mul(power);
        power = power.mul(shift);
    }
    ntt(&mut padded, root_of_unity(log_size));
    padded
}

/// Evaluates a coefficient vector at a single point by Horner folding.
pub fn eval_at(coeffs: &[Felt], point: Felt) -> Felt {
    let mut acc = Felt::ZERO;
    for c in coeffs.iter().rev() {
        acc = acc.mul(point).add(*c);
    }
    acc
}

/// Inverts a whole vector with one field inversion by the running product
pub fn batch_inverse(values: &[Felt]) -> Vec<Felt> {
    let n = values.len();
    let mut prefix = vec![Felt::ONE; n];
    let mut running = Felt::ONE;
    for i in 0..n {
        prefix[i] = running;
        running = running.mul(values[i]);
    }
    let mut inverse = running.inv();
    let mut out = vec![Felt::ZERO; n];
    for i in (0..n).rev() {
        out[i] = prefix[i].mul(inverse);
        inverse = inverse.mul(values[i]);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn naive_eval_domain(coeffs: &[Felt], log_n: u32) -> Vec<Felt> {
        let n = 1usize << log_n;
        let omega = root_of_unity(log_n);
        let mut point = Felt::ONE;
        let mut out = Vec::with_capacity(n);
        for _ in 0..n {
            out.push(eval_at(coeffs, point));
            point = point.mul(omega);
        }
        out
    }

    #[test]
    fn transform_matches_direct_evaluation() {
        let coeffs: Vec<Felt> = (1..=16u64).map(Felt::new).collect();
        let mut fast = coeffs.clone();
        ntt(&mut fast, root_of_unity(4));
        assert_eq!(fast, naive_eval_domain(&coeffs, 4));
    }

    #[test]
    fn interpolate_inverts_evaluation() {
        let coeffs: Vec<Felt> = (0..32u64)
            .map(|i| Felt::new(i.wrapping_mul(7) + 1))
            .collect();
        let evals = evaluate_subgroup(&coeffs, 5);
        let recovered = interpolate(&evals);
        assert_eq!(recovered, coeffs);
    }

    #[test]
    fn coset_evaluation_matches_shifted_points() {
        let coeffs: Vec<Felt> = (1..=8u64).map(Felt::new).collect();
        let shift = Felt::new(7);
        let evals = evaluate_coset(&coeffs, 3, shift);
        let omega = root_of_unity(3);
        let mut point = shift;
        for value in evals {
            assert_eq!(value, eval_at(&coeffs, point));
            point = point.mul(omega);
        }
    }

    #[test]
    fn batch_inverse_matches_pointwise_inverse() {
        let values: Vec<Felt> = (1..=20u64).map(Felt::new).collect();
        let inverses = batch_inverse(&values);
        for (v, i) in values.iter().zip(inverses.iter()) {
            assert_eq!(v.mul(*i), Felt::ONE);
            assert_eq!(*i, v.inv());
        }
    }

    #[test]
    fn low_degree_extension_agrees_on_the_base_domain() {
        let base: Vec<Felt> = (0..8u64).map(|i| Felt::new(i * i + 3)).collect();
        let coeffs = interpolate(&base);
        let extended = evaluate_subgroup(&coeffs, 5);
        let blowup = 32 / 8;
        for (i, value) in base.iter().enumerate() {
            assert_eq!(extended[i * blowup], *value);
        }
    }
}
