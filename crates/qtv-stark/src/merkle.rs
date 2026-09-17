// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::field::Felt;
use qtv_crypto::sha3::sha3_256;

pub type Digest = [u8; 32];

pub const LEAF_DOMAIN: u8 = 0x00;
const NODE_DOMAIN: u8 = 0x01;

pub fn hash_leaf(value: Felt) -> Digest {
    let mut preimage = [0u8; 9];
    preimage[0] = LEAF_DOMAIN;
    preimage[1..].copy_from_slice(&value.to_u64().to_le_bytes());
    sha3_256(&preimage)
}

pub fn hash_row(values: &[Felt]) -> Digest {
    let mut preimage = Vec::with_capacity(1 + values.len() * 8);
    preimage.push(LEAF_DOMAIN);
    for value in values {
        preimage.extend_from_slice(&value.to_u64().to_le_bytes());
    }
    sha3_256(&preimage)
}

pub struct MerkleTree {
    layers: Vec<Vec<Digest>>,
}

pub struct MerkleProof {
    pub leaf_index: usize,
    pub siblings: Vec<Digest>,
}

impl MerkleTree {
    pub fn commit(leaves: &[Digest]) -> Self {
        let mut layers = vec![leaves.to_vec()];
        while layers.last().map(|layer| layer.len()).unwrap_or(0) > 1 {
            let current = layers.last().unwrap();
            let mut next = Vec::with_capacity(current.len().div_ceil(2));
            let mut i = 0;
            while i < current.len() {
                let left = current[i];
                let right = if i + 1 < current.len() {
                    current[i + 1]
                } else {
                    current[i]
                };
                next.push(hash_pair(&left, &right));
                i += 2;
            }
            layers.push(next);
        }
        MerkleTree { layers }
    }

    pub fn root(&self) -> Digest {
        self.layers
            .last()
            .and_then(|layer| layer.first().copied())
            .unwrap_or([0u8; 32])
    }

    pub fn open(&self, leaf_index: usize) -> MerkleProof {
        let mut siblings = Vec::new();
        let mut index = leaf_index;
        for layer in &self.layers {
            if layer.len() <= 1 {
                break;
            }
            let sibling = if index % 2 == 0 {
                if index + 1 < layer.len() {
                    layer[index + 1]
                } else {
                    layer[index]
                }
            } else {
                layer[index - 1]
            };
            siblings.push(sibling);
            index /= 2;
        }
        MerkleProof {
            leaf_index,
            siblings,
        }
    }
}

pub const MAX_MERKLE_DEPTH: usize = 64;

// The depth a commitment over `leaves` leaf digests was built at. MerkleTree::commit
// halves with div_ceil until one node remains, so this is ceil(log2(leaves)).
pub fn depth_for(leaves: usize) -> usize {
    let mut depth = 0usize;
    let mut remaining = leaves;
    while remaining > 1 {
        remaining = remaining.div_ceil(2);
        depth += 1;
    }
    depth
}

// The caller states how many leaves the commitment covers. Without that bound a shortened
// path reaches the root from an interior node, which is a second preimage on the
// commitment. The leaf and node domain bytes make it unreachable for a caller that hashes
// its own value, but the bound belongs in the verifier rather than in the discipline of
// every call site.
pub fn verify_with_leaves(
    root: &Digest,
    leaf: &Digest,
    proof: &MerkleProof,
    leaves: usize,
) -> bool {
    let depth = depth_for(leaves);
    if proof.siblings.len() != depth || proof.leaf_index >= leaves.max(1) {
        return false;
    }
    verify(root, leaf, proof)
}

pub fn verify(root: &Digest, leaf: &Digest, proof: &MerkleProof) -> bool {
    if proof.siblings.len() > MAX_MERKLE_DEPTH {
        return false;
    }
    let mut acc = *leaf;
    let mut index = proof.leaf_index;
    for sibling in &proof.siblings {
        acc = if index % 2 == 0 {
            hash_pair(&acc, sibling)
        } else {
            hash_pair(sibling, &acc)
        };
        index /= 2;
    }
    &acc == root
}

fn hash_pair(left: &Digest, right: &Digest) -> Digest {
    let mut preimage = [0u8; 65];
    preimage[0] = NODE_DOMAIN;
    preimage[1..33].copy_from_slice(left);
    preimage[33..].copy_from_slice(right);
    sha3_256(&preimage)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaves(count: usize) -> Vec<Digest> {
        (0..count).map(|i| hash_leaf(Felt::new(i as u64))).collect()
    }

    #[test]
    fn inclusion_proof_verifies_for_every_leaf() {
        let leaves = leaves(8);
        let tree = MerkleTree::commit(&leaves);
        let root = tree.root();
        for (index, leaf) in leaves.iter().enumerate() {
            let proof = tree.open(index);
            assert_eq!(proof.leaf_index, index);
            assert!(verify(&root, leaf, &proof));
        }
    }

    #[test]
    fn a_tampered_leaf_is_rejected() {
        let leaves = leaves(8);
        let tree = MerkleTree::commit(&leaves);
        let root = tree.root();
        let proof = tree.open(3);
        let forged = hash_leaf(Felt::new(999));
        assert!(!verify(&root, &forged, &proof));
    }

    #[test]
    fn a_tampered_path_is_rejected() {
        let leaves = leaves(8);
        let tree = MerkleTree::commit(&leaves);
        let root = tree.root();
        let mut proof = tree.open(5);
        proof.siblings[0][0] ^= 1;
        assert!(!verify(&root, &leaves[5], &proof));
    }

    #[test]
    fn a_row_leaf_depends_on_every_column() {
        let base = [Felt::new(1), Felt::new(2), Felt::new(3)];
        let mut changed = base;
        changed[1] = Felt::new(9);
        assert_ne!(hash_row(&base), hash_row(&changed));
        assert_eq!(hash_row(&base), hash_row(&base));
    }

    #[test]
    fn a_proof_from_a_different_position_is_rejected() {
        let leaves = leaves(8);
        let tree = MerkleTree::commit(&leaves);
        let root = tree.root();
        let proof = tree.open(2);
        assert!(!verify(&root, &leaves[6], &proof));
    }
}

#[cfg(test)]
mod domain_separation_tests {
    use super::*;

    // verify() bounds the sibling count but does not pin it to the depth the commitment
    // was built at, so a shortened path reaches the root from an interior node. What keeps
    // that unreachable is the domain byte: a leaf and an internal node are hashed under
    // different prefixes, and every caller in this crate hashes the value itself rather
    // than taking a digest off the proof, so producing the interior digest as a leaf needs
    // a preimage. These pin both halves of that argument.
    #[test]
    fn a_leaf_and_an_internal_node_never_share_a_digest() {
        let a = hash_leaf(Felt::new(1));
        let b = hash_leaf(Felt::new(2));
        assert_ne!(
            hash_pair(&a, &b),
            hash_row(&[Felt::new(1), Felt::new(2)]),
            "an internal node and a row leaf collided, which would let an interior node be \
             opened as if it were committed data"
        );
    }

    #[test]
    fn the_leaf_and_node_prefixes_are_distinct() {
        assert_ne!(
            LEAF_DOMAIN, NODE_DOMAIN,
            "the domain bytes are what separate a leaf from a node, they must differ"
        );
    }

    #[test]
    fn a_shortened_path_does_not_verify_for_a_real_leaf() {
        let leaves: Vec<Digest> = (0..8u64).map(|i| hash_leaf(Felt::new(i))).collect();
        let tree = MerkleTree::commit(&leaves);
        let root = tree.root();
        let full = tree.open(3);

        for cut in 1..full.siblings.len() {
            let shortened = MerkleProof {
                leaf_index: 3,
                siblings: full.siblings[..cut].to_vec(),
            };
            assert!(
                !verify(&root, &leaves[3], &shortened),
                "a path truncated to {cut} siblings still verified a real leaf against the root"
            );
        }
    }

    #[test]
    fn an_interior_digest_is_not_reachable_as_a_hashed_value() {
        // The callers never hand verify() a digest taken from the proof, they hash a field
        // element. So the interior node would have to be the hash_leaf of some value.
        let leaves: Vec<Digest> = (0..8u64).map(|i| hash_leaf(Felt::new(i))).collect();
        let interior = hash_pair(&leaves[0], &leaves[1]);
        for i in 0..1_000u64 {
            assert_ne!(
                hash_leaf(Felt::new(i)),
                interior,
                "a field element hashed to an interior node digest"
            );
        }
    }
}

#[cfg(test)]
mod depth_bound_tests {
    use super::*;

    #[test]
    fn the_depth_matches_what_commit_actually_builds() {
        for n in 1..=64usize {
            let leaves: Vec<Digest> = (0..n as u64).map(|i| hash_leaf(Felt::new(i))).collect();
            let tree = MerkleTree::commit(&leaves);
            let proof = tree.open(0);
            assert_eq!(
                depth_for(n),
                proof.siblings.len(),
                "depth_for disagrees with the tree commit builds at {n} leaves, so the bound \
                 would reject honest proofs or admit shortened ones"
            );
        }
    }

    #[test]
    fn an_interior_node_cannot_be_opened_as_a_leaf() {
        let n = 8usize;
        let leaves: Vec<Digest> = (0..n as u64).map(|i| hash_leaf(Felt::new(i))).collect();
        let tree = MerkleTree::commit(&leaves);
        let root = tree.root();
        let full = tree.open(0);

        let interior = hash_pair(&leaves[0], &leaves[1]);
        let shortened = MerkleProof {
            leaf_index: 0,
            siblings: full.siblings[1..].to_vec(),
        };

        assert!(
            verify(&root, &interior, &shortened),
            "without a leaf count the unbounded verifier does admit the interior node, which is \
             the weakness the bound exists to close"
        );
        assert!(
            !verify_with_leaves(&root, &interior, &shortened, n),
            "the bounded verifier must refuse an interior node opened under a shortened path"
        );
    }

    #[test]
    fn an_honest_proof_still_verifies_under_the_bound() {
        for n in [1usize, 2, 3, 5, 8, 17, 64] {
            let leaves: Vec<Digest> = (0..n as u64).map(|i| hash_leaf(Felt::new(i))).collect();
            let tree = MerkleTree::commit(&leaves);
            let root = tree.root();
            for index in 0..n {
                let proof = tree.open(index);
                assert!(
                    verify_with_leaves(&root, &leaves[index], &proof, n),
                    "an honest proof for leaf {index} of {n} was refused by the bound"
                );
            }
        }
    }

    #[test]
    fn an_index_past_the_leaf_count_is_refused() {
        let n = 8usize;
        let leaves: Vec<Digest> = (0..n as u64).map(|i| hash_leaf(Felt::new(i))).collect();
        let tree = MerkleTree::commit(&leaves);
        let root = tree.root();
        let mut proof = tree.open(3);
        proof.leaf_index = n + 1;
        assert!(
            !verify_with_leaves(&root, &leaves[3], &proof, n),
            "an index outside the committed range must be refused"
        );
    }
}
