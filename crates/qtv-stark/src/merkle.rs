//! Merkle commitments for the hash based STARK backend.
//!
//! Commitments bind the prover to its evaluation vectors. Hashing will be
//! provided by SHA3 from the crypto crate. The local stand in keeps the tree
//! skeleton compiling until that dependency is wired in.

/// A thirty two byte commitment digest.
pub type Digest = [u8; 32];

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

/// Combines two child digests into a parent digest.
///
/// This stand in will be replaced by SHA3 from the crypto crate.
fn hash_pair(left: &Digest, right: &Digest) -> Digest {
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = left[i] ^ right[i].rotate_left(1);
    }
    out
}
