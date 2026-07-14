//! Merkle commitments for the hash based STARK backend.

use crate::field::Felt;
use qtv_crypto::sha3::sha3_256;

/// A thirty two byte commitment digest.
pub type Digest = [u8; 32];

/// Hashes a single field element into a leaf digest.
pub fn hash_leaf(value: Felt) -> Digest {
    sha3_256(&value.to_u64().to_le_bytes())
}

/// Hashes a row of field elements into one leaf digest.
pub fn hash_row(values: &[Felt]) -> Digest {
    let mut preimage = Vec::with_capacity(values.len() * 8);
    for value in values {
        preimage.extend_from_slice(&value.to_u64().to_le_bytes());
    }
    sha3_256(&preimage)
}

/// A Merkle tree built over a vector of leaf digests.
pub struct MerkleTree {
    layers: Vec<Vec<Digest>>,
}

/// An authentication path that ties one leaf to a committed root.
pub struct MerkleProof {
    /// The index of the opened leaf in the base layer.
    pub leaf_index: usize,
    /// The sibling digests from the leaf up to the root.
    pub siblings: Vec<Digest>,
}

impl MerkleTree {
    /// Commits to a set of leaves and builds the internal layers.
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

    /// Returns the commitment root.
    pub fn root(&self) -> Digest {
        self.layers
            .last()
            .and_then(|layer| layer.first().copied())
            .unwrap_or([0u8; 32])
    }

    /// Opens the leaf at an index and returns its authentication path.
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

/// Verifies an authentication path against a committed root.
pub fn verify(root: &Digest, leaf: &Digest, proof: &MerkleProof) -> bool {
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

/// Combines two child digests into a parent digest with SHA3 256.
fn hash_pair(left: &Digest, right: &Digest) -> Digest {
    let mut preimage = [0u8; 64];
    preimage[..32].copy_from_slice(left);
    preimage[32..].copy_from_slice(right);
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
