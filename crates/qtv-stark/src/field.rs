// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT

pub const MODULUS: u64 = 18446744069414584321;

const EPSILON: u64 = 0xffff_ffff;

#[inline]
fn canonical(value: u64) -> u64 {
    let (reduced, borrow) = value.overflowing_sub(MODULUS);
    let keep = (borrow as u64).wrapping_neg();
    (value & keep) | (reduced & !keep)
}

#[inline]
fn reduce128(x: u128) -> u64 {
    let lo = x as u64;
    let hi = (x >> 64) as u64;
    let hi_hi = hi >> 32;
    let hi_lo = hi & EPSILON;
    let (t0, borrow) = lo.overflowing_sub(hi_hi);
    let t0 = t0.wrapping_sub(EPSILON & (borrow as u64).wrapping_neg());
    let t1 = hi_lo * EPSILON;
    let (t2, carry) = t0.overflowing_add(t1);
    let t2 = t2.wrapping_add(EPSILON & (carry as u64).wrapping_neg());
    canonical(t2)
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Felt(u64);

impl Felt {
    pub const ZERO: Felt = Felt(0);

    pub const ONE: Felt = Felt(1);

    pub fn new(value: u64) -> Self {
        Felt(canonical(value))
    }

    pub fn to_u64(self) -> u64 {
        self.0
    }

    pub fn add(self, other: Felt) -> Felt {
        let (sum, carry) = self.0.overflowing_add(other.0);
        let sum = sum.wrapping_add(EPSILON & (carry as u64).wrapping_neg());
        Felt(canonical(sum))
    }

    pub fn sub(self, other: Felt) -> Felt {
        let (diff, borrow) = self.0.overflowing_sub(other.0);
        Felt(diff.wrapping_add(MODULUS & (borrow as u64).wrapping_neg()))
    }

    pub fn mul(self, other: Felt) -> Felt {
        Felt(reduce128((self.0 as u128) * (other.0 as u128)))
    }

    pub fn pow(self, mut exponent: u64) -> Felt {
        let mut base = self;
        let mut acc = Felt::ONE;
        while exponent > 0 {
            if exponent & 1 == 1 {
                acc = acc.mul(base);
            }
            base = base.mul(base);
            exponent >>= 1;
        }
        acc
    }

    pub fn inv(self) -> Felt {
        assert!(self != Felt::ZERO, "zero has no inverse");
        self.pow(MODULUS - 2)
    }

    pub fn try_inv(self) -> Option<Felt> {
        if self == Felt::ZERO {
            None
        } else {
            Some(self.pow(MODULUS - 2))
        }
    }
}

pub const GENERATOR: u64 = 7;

pub const TWO_ADICITY: u32 = 32;

pub fn root_of_unity(log_n: u32) -> Felt {
    assert!(log_n <= TWO_ADICITY);
    let exponent = (MODULUS - 1) >> log_n;
    Felt::new(GENERATOR).pow(exponent)
}

#[cfg(test)]
mod tests {
    #[test]
    fn the_reductions_agree_with_the_remainder_everywhere_they_are_tested() {
        let p = MODULUS as u128;
        let edges = [
            0u64,
            1,
            2,
            EPSILON,
            EPSILON + 1,
            MODULUS - 2,
            MODULUS - 1,
            MODULUS,
            MODULUS + 1,
            u64::MAX - 1,
            u64::MAX,
            1 << 63,
            (1 << 32) - 2,
        ];
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        let mut values: Vec<u64> = edges.to_vec();
        for _ in 0..4_000 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            values.push(state);
        }
        for &a in &values {
            assert_eq!(Felt::new(a).to_u64() as u128, a as u128 % p);
        }
        for &a in &values {
            for &b in values.iter().take(300) {
                let fa = Felt::new(a);
                let fb = Felt::new(b);
                let (ca, cb) = (fa.to_u64() as u128, fb.to_u64() as u128);
                assert_eq!(fa.add(fb).to_u64() as u128, (ca + cb) % p);
                assert_eq!(fa.sub(fb).to_u64() as u128, (ca + p - cb) % p);
                assert_eq!(fa.mul(fb).to_u64() as u128, (ca * cb) % p);
            }
        }
    }

    use super::*;

    #[test]
    fn add_is_commutative_and_has_zero_identity() {
        let a = Felt::new(1311768467463790320);
        let b = Felt::new(18369614221520256751);
        assert_eq!(a.add(b), b.add(a));
        assert_eq!(a.add(Felt::ZERO), a);
    }

    #[test]
    fn sub_is_the_inverse_of_add() {
        let a = Felt::new(1085102592571150095);
        let b = Felt::new(71777214294589695);
        assert_eq!(a.add(b).sub(b), a);
        assert_eq!(a.sub(a), Felt::ZERO);
    }

    #[test]
    fn add_wraps_at_the_modulus() {
        let near = Felt::new(MODULUS - 1);
        assert_eq!(near.add(Felt::ONE), Felt::ZERO);
        assert_eq!(Felt::ZERO.sub(Felt::ONE), near);
    }

    #[test]
    fn mul_is_commutative_associative_and_distributes() {
        let a = Felt::new(54324593195745281);
        let b = Felt::new(1229801703532086340);
        let c = Felt::new(11068027678940948070);
        assert_eq!(a.mul(b), b.mul(a));
        assert_eq!(a.mul(b).mul(c), a.mul(b.mul(c)));
        assert_eq!(a.mul(b.add(c)), a.mul(b).add(a.mul(c)));
        assert_eq!(a.mul(Felt::ONE), a);
        assert_eq!(a.mul(Felt::ZERO), Felt::ZERO);
    }

    #[test]
    fn inverse_returns_the_multiplicative_unit() {
        for raw in [1u64, 2, 3, 7, 81985529216486895, MODULUS - 1] {
            let a = Felt::new(raw);
            assert_eq!(a.mul(a.inv()), Felt::ONE);
        }
    }

    #[test]
    fn pow_matches_repeated_multiplication() {
        let a = Felt::new(5);
        let mut acc = Felt::ONE;
        for _ in 0..17 {
            acc = acc.mul(a);
        }
        assert_eq!(a.pow(17), acc);
        assert_eq!(a.pow(0), Felt::ONE);
    }

    #[test]
    fn root_of_unity_has_the_requested_order() {
        for log_n in 1..=16u32 {
            let root = root_of_unity(log_n);
            assert_eq!(root.pow(1u64 << log_n), Felt::ONE);
            assert_ne!(root.pow(1u64 << (log_n - 1)), Felt::ONE);
        }
    }

    #[test]
    fn root_of_unity_squares_toward_the_smaller_domain() {
        let big = root_of_unity(10);
        let small = root_of_unity(9);
        assert_eq!(big.mul(big), small);
    }
}
