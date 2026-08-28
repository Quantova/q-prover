// Copyright 2026 Quantova Inc
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::field::Felt;
use crate::field_ext::Fp3;
use crate::fri::{FriProof, QueryLayer, QueryProof};
use crate::merkle::{Digest, MerkleProof};
use crate::stark::{QueryOpening, RowOpening, StarkProof};

fn put_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_felt(out: &mut Vec<u8>, value: Felt) {
    put_u64(out, value.to_u64());
}

fn put_ext(out: &mut Vec<u8>, value: Fp3) {
    for limb in value.to_u64s() {
        put_u64(out, limb);
    }
}

fn put_digest(out: &mut Vec<u8>, digest: &Digest) {
    out.extend_from_slice(digest);
}

fn put_merkle(out: &mut Vec<u8>, proof: &MerkleProof) {
    put_u64(out, proof.leaf_index as u64);
    put_u64(out, proof.siblings.len() as u64);
    for sibling in &proof.siblings {
        put_digest(out, sibling);
    }
}

fn put_fri(out: &mut Vec<u8>, fri: &FriProof<Fp3>) {
    put_u64(out, fri.layer_roots.len() as u64);
    for root in &fri.layer_roots {
        put_digest(out, root);
    }
    put_u64(out, fri.final_layer.len() as u64);
    for value in &fri.final_layer {
        put_ext(out, *value);
    }
    put_u64(out, fri.queries.len() as u64);
    for query in &fri.queries {
        put_u64(out, query.position as u64);
        put_u64(out, query.layers.len() as u64);
        for layer in &query.layers {
            put_ext(out, layer.eval);
            put_ext(out, layer.sibling);
            put_merkle(out, &layer.eval_path);
            put_merkle(out, &layer.sibling_path);
        }
    }
}

fn put_openings(out: &mut Vec<u8>, openings: &[QueryOpening]) {
    put_u64(out, openings.len() as u64);
    for opening in openings {
        put_u64(out, opening.rows.len() as u64);
        for row in &opening.rows {
            put_u64(out, row.index as u64);
            put_u64(out, row.values.len() as u64);
            for value in &row.values {
                put_felt(out, *value);
            }
            put_merkle(out, &row.path);
            put_merkle(out, &row.aux_path);
        }
    }
}

pub fn encode_proof(proof: &StarkProof) -> Vec<u8> {
    let mut out = Vec::new();
    put_digest(&mut out, &proof.trace_root);
    put_digest(&mut out, &proof.aux_root);
    put_fri(&mut out, &proof.fri);
    put_openings(&mut out, &proof.openings);
    put_fri(&mut out, &proof.trace_fri);
    put_openings(&mut out, &proof.trace_openings);
    out
}

struct Reader<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Reader { bytes, pos: 0 }
    }

    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let end = self.pos.checked_add(n)?;
        if end > self.bytes.len() {
            return None;
        }
        let slice = &self.bytes[self.pos..end];
        self.pos = end;
        Some(slice)
    }

    fn u64(&mut self) -> Option<u64> {
        let slice = self.take(8)?;
        let mut buf = [0u8; 8];
        buf.copy_from_slice(slice);
        Some(u64::from_le_bytes(buf))
    }

    fn count(&mut self) -> Option<usize> {
        Some(self.u64()? as usize)
    }

    fn felt(&mut self) -> Option<Felt> {
        Some(Felt::new(self.u64()?))
    }

    fn ext(&mut self) -> Option<Fp3> {
        let a0 = self.u64()?;
        let a1 = self.u64()?;
        let a2 = self.u64()?;
        Some(Fp3::from_u64s([a0, a1, a2]))
    }

    fn digest(&mut self) -> Option<Digest> {
        let slice = self.take(32)?;
        let mut buf = [0u8; 32];
        buf.copy_from_slice(slice);
        Some(buf)
    }

    fn merkle(&mut self) -> Option<MerkleProof> {
        let leaf_index = self.count()?;
        let len = self.count()?;
        let mut siblings = Vec::new();
        for _ in 0..len {
            siblings.push(self.digest()?);
        }
        Some(MerkleProof {
            leaf_index,
            siblings,
        })
    }

    fn done(&self) -> bool {
        self.pos == self.bytes.len()
    }

    fn fri(&mut self) -> Option<FriProof<Fp3>> {
        let layer_count = self.count()?;
        let mut layer_roots = Vec::new();
        for _ in 0..layer_count {
            layer_roots.push(self.digest()?);
        }
        let final_count = self.count()?;
        let mut final_layer = Vec::new();
        for _ in 0..final_count {
            final_layer.push(self.ext()?);
        }
        let query_count = self.count()?;
        let mut queries = Vec::new();
        for _ in 0..query_count {
            let position = self.count()?;
            let layer_count = self.count()?;
            let mut layers = Vec::new();
            for _ in 0..layer_count {
                let eval = self.ext()?;
                let sibling = self.ext()?;
                let eval_path = self.merkle()?;
                let sibling_path = self.merkle()?;
                layers.push(QueryLayer {
                    eval,
                    sibling,
                    eval_path,
                    sibling_path,
                });
            }
            queries.push(QueryProof { position, layers });
        }
        Some(FriProof {
            layer_roots,
            final_layer,
            queries,
        })
    }

    fn openings(&mut self) -> Option<Vec<QueryOpening>> {
        let opening_count = self.count()?;
        let mut openings = Vec::new();
        for _ in 0..opening_count {
            let row_count = self.count()?;
            let mut rows = Vec::new();
            for _ in 0..row_count {
                let index = self.count()?;
                let value_count = self.count()?;
                let mut values = Vec::new();
                for _ in 0..value_count {
                    values.push(self.felt()?);
                }
                let path = self.merkle()?;
                let aux_path = self.merkle()?;
                rows.push(RowOpening {
                    index,
                    values,
                    path,
                    aux_path,
                });
            }
            openings.push(QueryOpening { rows });
        }
        Some(openings)
    }
}

pub fn decode_proof(bytes: &[u8]) -> Option<StarkProof> {
    let mut reader = Reader::new(bytes);
    let trace_root = reader.digest()?;
    let aux_root = reader.digest()?;
    let fri = reader.fri()?;
    let openings = reader.openings()?;
    let trace_fri = reader.fri()?;
    let trace_openings = reader.openings()?;

    if !reader.done() {
        return None;
    }
    Some(StarkProof {
        trace_root,
        aux_root,
        fri,
        openings,
        trace_fri,
        trace_openings,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::certificate::certificate_trace;
    use crate::stark::{prove, verify, StarkParams};

    fn params() -> StarkParams {
        StarkParams {
            lde_blowup: 32,
            num_queries: 24,
        }
    }

    fn sample_proof() -> (crate::air::Air, StarkProof) {
        let hints: Vec<u64> = (0..2u64).map(|i| i & 1).collect();
        let responses = [11_111u64, 22_222];
        let cert = certificate_trace(2, b"module lattice codec round trip", &hints, &responses);
        let proof = prove(&cert.air, &cert.trace, &params());
        let air = crate::certificate::certificate_air(
            2,
            b"module lattice codec round trip",
            &cert.output,
        );
        (air, proof)
    }

    #[test]
    fn a_proof_round_trips_through_bytes() {
        let (air, proof) = sample_proof();
        let bytes = encode_proof(&proof);
        let decoded = decode_proof(&bytes).expect("decode");
        assert!(verify(&air, &params(), &decoded));
    }

    #[test]
    fn the_encoding_is_stable() {
        let (_, proof) = sample_proof();
        assert_eq!(
            encode_proof(&proof),
            encode_proof(&decode_proof(&encode_proof(&proof)).unwrap())
        );
    }

    #[test]
    fn a_truncated_proof_decodes_to_none() {
        let (_, proof) = sample_proof();
        let bytes = encode_proof(&proof);
        assert!(decode_proof(&bytes[..bytes.len() - 1]).is_none());
    }

    #[test]
    fn trailing_bytes_are_rejected() {
        let (_, proof) = sample_proof();
        let mut bytes = encode_proof(&proof);
        bytes.push(0);
        assert!(decode_proof(&bytes).is_none());
    }

    #[test]
    fn a_bogus_length_does_not_allocate_unbounded() {
        let mut bytes = vec![0u8; 64];
        bytes.extend_from_slice(&u64::MAX.to_le_bytes());
        assert!(decode_proof(&bytes).is_none());
    }

    #[test]
    fn a_tampered_opening_no_longer_verifies() {
        let (air, proof) = sample_proof();
        let mut bytes = encode_proof(&proof);
        let mid = bytes.len() / 2;
        bytes[mid] ^= 1;
        if let Some(decoded) = decode_proof(&bytes) {
            assert!(!verify(&air, &params(), &decoded));
        }
    }
}
