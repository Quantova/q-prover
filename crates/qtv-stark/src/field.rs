//! Prime field arithmetic for the hash based STARK backend.

/// The Goldilocks prime modulus, two to the sixty four minus two to the thirty
pub const MODULUS: u64 = 18446744069414584321;

/// An element of the prime field, stored in canonical form in the range zero to
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Felt(u64);

impl Felt {
    /// The additive identity.
    pub const ZERO: Felt = Felt(0);

    /// The multiplicative identity.
    pub const ONE: Felt = Felt(1);

    /// Builds a field element from a raw integer, reducing it into range.
    pub fn new(value: u64) -> Self {
        Felt(value % MODULUS)
    }

    /// Returns the canonical integer representation.
    pub fn to_u64(self) -> u64 {
        self.0
    }

    /// Field addition.
    pub fn add(self, other: Felt) -> Felt {
        let sum = (self.0 as u128) + (other.0 as u128);
        Felt((sum % (MODULUS as u128)) as u64)
    }

    /// Field subtraction.
    pub fn sub(self, other: Felt) -> Felt {
        let (diff, borrow) = self.0.overflowing_sub(other.0);
        let reduced = if borrow {
            diff.wrapping_add(MODULUS)
        } else {
            diff
        };
        Felt(reduced)
    }

    /// Field multiplication through a wide intermediate product.
    pub fn mul(self, other: Felt) -> Felt {
        let product = (self.0 as u128) * (other.0 as u128);
        Felt((product % (MODULUS as u128)) as u64)
    }

    /// Raises the element to an integer power by square and multiply.
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

    /// Returns the multiplicative inverse through Fermat, the element raised to
    pub fn inv(self) -> Felt {
        self.pow(MODULUS - 2)
    }
}

/// A generator of the full multiplicative group of the field.
pub const GENERATOR: u64 = 7;

/// The two adic order of the field, the largest power of two dividing the group
pub const TWO_ADICITY: u32 = 32;

/// Returns a primitive root of unity of order two to the log_n.
pub fn root_of_unity(log_n: u32) -> Felt {
    assert!(log_n <= TWO_ADICITY);
    let exponent = (MODULUS - 1) >> log_n;
    Felt::new(GENERATOR).pow(exponent)
}

#[cfg(test)]
mod tests {
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
