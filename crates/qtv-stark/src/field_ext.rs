// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::field::Felt;

pub const NON_RESIDUE: u64 = 2;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Fp3 {
    limbs: [Felt; 3],
}

impl Fp3 {
    pub const ZERO: Fp3 = Fp3 {
        limbs: [Felt::ZERO, Felt::ZERO, Felt::ZERO],
    };

    pub const ONE: Fp3 = Fp3 {
        limbs: [Felt::ONE, Felt::ZERO, Felt::ZERO],
    };

    pub fn new(a0: Felt, a1: Felt, a2: Felt) -> Self {
        Fp3 {
            limbs: [a0, a1, a2],
        }
    }

    pub fn from_base(value: Felt) -> Self {
        Fp3 {
            limbs: [value, Felt::ZERO, Felt::ZERO],
        }
    }

    pub fn coefficients(self) -> [Felt; 3] {
        self.limbs
    }

    pub fn to_u64s(self) -> [u64; 3] {
        [
            self.limbs[0].to_u64(),
            self.limbs[1].to_u64(),
            self.limbs[2].to_u64(),
        ]
    }

    pub fn from_u64s(raw: [u64; 3]) -> Self {
        Fp3 {
            limbs: [Felt::new(raw[0]), Felt::new(raw[1]), Felt::new(raw[2])],
        }
    }

    pub fn add(self, other: Fp3) -> Fp3 {
        Fp3 {
            limbs: [
                self.limbs[0].add(other.limbs[0]),
                self.limbs[1].add(other.limbs[1]),
                self.limbs[2].add(other.limbs[2]),
            ],
        }
    }

    pub fn sub(self, other: Fp3) -> Fp3 {
        Fp3 {
            limbs: [
                self.limbs[0].sub(other.limbs[0]),
                self.limbs[1].sub(other.limbs[1]),
                self.limbs[2].sub(other.limbs[2]),
            ],
        }
    }

    pub fn mul(self, other: Fp3) -> Fp3 {
        let c = Felt::new(NON_RESIDUE);
        let [a0, a1, a2] = self.limbs;
        let [b0, b1, b2] = other.limbs;

        let t0 = a0.mul(b0);
        let t1 = a0.mul(b1).add(a1.mul(b0));
        let t2 = a0.mul(b2).add(a1.mul(b1)).add(a2.mul(b0));
        let t3 = a1.mul(b2).add(a2.mul(b1));
        let t4 = a2.mul(b2);

        let r0 = t0.add(c.mul(t3));
        let r1 = t1.add(c.mul(t4));
        let r2 = t2;
        Fp3 {
            limbs: [r0, r1, r2],
        }
    }

    pub fn scale(self, scalar: Felt) -> Fp3 {
        Fp3 {
            limbs: [
                self.limbs[0].mul(scalar),
                self.limbs[1].mul(scalar),
                self.limbs[2].mul(scalar),
            ],
        }
    }

    pub fn add_base(self, scalar: Felt) -> Fp3 {
        Fp3 {
            limbs: [self.limbs[0].add(scalar), self.limbs[1], self.limbs[2]],
        }
    }

    pub fn sub_base(self, scalar: Felt) -> Fp3 {
        Fp3 {
            limbs: [self.limbs[0].sub(scalar), self.limbs[1], self.limbs[2]],
        }
    }

    pub fn neg(self) -> Fp3 {
        Fp3::ZERO.sub(self)
    }

    fn norm(self) -> Felt {
        let c = Felt::new(NON_RESIDUE);
        let [a0, a1, a2] = self.limbs;
        let a0_cubed = a0.mul(a0).mul(a0);
        let a1_cubed = a1.mul(a1).mul(a1);
        let a2_cubed = a2.mul(a2).mul(a2);
        let cross = a0.mul(a1).mul(a2);
        let three_c = c.mul(Felt::new(3));
        a0_cubed
            .add(c.mul(a1_cubed))
            .add(c.mul(c).mul(a2_cubed))
            .sub(three_c.mul(cross))
    }

    fn adjugate(self) -> Fp3 {
        let c = Felt::new(NON_RESIDUE);
        let [a0, a1, a2] = self.limbs;
        let b0 = a0.mul(a0).sub(c.mul(a1).mul(a2));
        let b1 = c.mul(a2).mul(a2).sub(a0.mul(a1));
        let b2 = a1.mul(a1).sub(a0.mul(a2));
        Fp3 {
            limbs: [b0, b1, b2],
        }
    }

    pub fn inv(self) -> Fp3 {
        let norm_inv = self.norm().inv();
        self.adjugate().scale(norm_inv)
    }

    pub fn pow(self, mut exponent: u64) -> Fp3 {
        let mut base = self;
        let mut acc = Fp3::ONE;
        while exponent > 0 {
            if exponent & 1 == 1 {
                acc = acc.mul(base);
            }
            base = base.mul(base);
            exponent >>= 1;
        }
        acc
    }

    pub fn is_base(self) -> bool {
        self.limbs[1] == Felt::ZERO && self.limbs[2] == Felt::ZERO
    }
}

impl crate::fri::FriField for Fp3 {
    const LIMBS: usize = 3;

    fn zero() -> Self {
        Fp3::ZERO
    }
    fn add(self, other: Self) -> Self {
        Fp3::add(self, other)
    }
    fn sub(self, other: Self) -> Self {
        Fp3::sub(self, other)
    }
    fn mul(self, other: Self) -> Self {
        Fp3::mul(self, other)
    }
    fn scale(self, scalar: Felt) -> Self {
        Fp3::scale(self, scalar)
    }
    fn from_base(value: Felt) -> Self {
        Fp3::from_base(value)
    }
    fn sample(transcript: &mut crate::fri::Transcript) -> Self {
        transcript.challenge_ext()
    }
    fn absorb(self, transcript: &mut crate::fri::Transcript) {
        transcript.absorb_ext(self);
    }
    fn hash_leaf(self) -> crate::merkle::Digest {
        let mut preimage = [0u8; 25];
        preimage[0] = crate::merkle::LEAF_DOMAIN;
        for (i, limb) in self.to_u64s().iter().enumerate() {
            preimage[1 + i * 8..1 + i * 8 + 8].copy_from_slice(&limb.to_le_bytes());
        }
        qtv_crypto::sha3::sha3_256(&preimage)
    }
    fn to_limbs(self) -> Vec<u64> {
        self.to_u64s().to_vec()
    }
    fn from_limbs(limbs: &[u64]) -> Self {
        Fp3::from_u64s([limbs[0], limbs[1], limbs[2]])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::MODULUS;

    fn sample(seed: u64) -> Fp3 {
        let a = seed.wrapping_mul(2654435761).wrapping_add(1);
        let b = seed.wrapping_mul(40503).wrapping_add(7);
        let d = seed.wrapping_mul(2246822519).wrapping_add(13);
        Fp3::new(Felt::new(a), Felt::new(b), Felt::new(d))
    }

    #[test]
    fn reduction_polynomial_is_irreducible() {
        let c = Felt::new(NON_RESIDUE);
        let e = (MODULUS - 1) / 3;
        assert_ne!(c.pow(e), Felt::ONE);
    }

    #[test]
    fn addition_forms_a_group() {
        let a = sample(1);
        let b = sample(2);
        let zero = Fp3::ZERO;
        assert_eq!(a.add(b), b.add(a));
        assert_eq!(a.add(zero), a);
        assert_eq!(a.sub(a), zero);
        assert_eq!(a.add(b).sub(b), a);
        assert_eq!(a.neg().add(a), zero);
    }

    #[test]
    fn multiplication_is_commutative_associative_and_distributes() {
        let a = sample(3);
        let b = sample(4);
        let d = sample(5);
        assert_eq!(a.mul(b), b.mul(a));
        assert_eq!(a.mul(b).mul(d), a.mul(b.mul(d)));
        assert_eq!(a.mul(b.add(d)), a.mul(b).add(a.mul(d)));
        assert_eq!(a.mul(Fp3::ONE), a);
        assert_eq!(a.mul(Fp3::ZERO), Fp3::ZERO);
    }

    #[test]
    fn inverse_returns_the_multiplicative_unit() {
        for seed in 1..200u64 {
            let a = sample(seed);
            if a == Fp3::ZERO {
                continue;
            }
            assert_eq!(a.mul(a.inv()), Fp3::ONE);
        }
    }

    #[test]
    fn the_base_field_embeds_as_a_subfield() {
        for raw in [0u64, 1, 2, 7, 12345, MODULUS - 1] {
            let x = Felt::new(raw);
            let y = Felt::new(raw.wrapping_mul(3).wrapping_add(9));
            let ex = Fp3::from_base(x);
            let ey = Fp3::from_base(y);
            assert_eq!(ex.add(ey), Fp3::from_base(x.add(y)));
            assert_eq!(ex.mul(ey), Fp3::from_base(x.mul(y)));
            assert!(ex.is_base());
        }
    }

    #[test]
    fn scaling_agrees_with_embedded_multiplication() {
        let a = sample(11);
        let s = Felt::new(987654321);
        assert_eq!(a.scale(s), a.mul(Fp3::from_base(s)));
        assert_eq!(a.add_base(s), a.add(Fp3::from_base(s)));
        assert_eq!(a.sub_base(s), a.sub(Fp3::from_base(s)));
    }

    #[test]
    fn a_non_base_element_generates_the_full_extension() {
        let x = Fp3::new(Felt::ZERO, Felt::ONE, Felt::ZERO);
        assert!(!x.is_base());
        assert_eq!(x.mul(x).mul(x), Fp3::from_base(Felt::new(NON_RESIDUE)));
    }

    #[test]
    fn pow_matches_repeated_multiplication() {
        let a = sample(17);
        let mut acc = Fp3::ONE;
        for _ in 0..23 {
            acc = acc.mul(a);
        }
        assert_eq!(a.pow(23), acc);
    }
}
