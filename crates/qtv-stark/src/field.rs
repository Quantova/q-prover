//! Prime field arithmetic for the hash based STARK backend.
//!
//! The field is the sixty four bit Goldilocks prime. It carries a large two adic
//! subgroup, which the low degree extension and the FRI folding both rely on for
//! their evaluation domains.

/// The Goldilocks prime modulus, two to the sixty four minus two to the thirty
/// two plus one.
pub const MODULUS: u64 = 0xFFFF_FFFF_0000_0001;

/// An element of the prime field, stored in canonical form in the range zero to
/// modulus minus one.
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
    /// the modulus minus two.
    pub fn inv(self) -> Felt {
        self.pow(MODULUS - 2)
    }
}
