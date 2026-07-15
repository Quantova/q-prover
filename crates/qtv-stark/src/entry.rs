//! A high level entry point over the fused module lattice certificate.

use qtv_crypto::sha3::shake256;

use crate::certificate::{certificate_air, certificate_trace};
use crate::codec::{decode_proof, encode_proof};
use crate::sponge::{shake_output, SHAKE256_RATE};
use crate::stark::{prove, verify, StarkParams};

/// The low degree extension blow up the fused certificate needs for its degree
pub const CERT_BLOWUP: usize = 32;

/// The number of query openings that back the certificate soundness.
pub const CERT_QUERIES: usize = 32;

/// The largest message the fused certificate absorbs, one SHAKE256 rate block.
pub const MAX_MESSAGE_BYTES: usize = SHAKE256_RATE - 1;

fn params() -> StarkParams {
    StarkParams {
        lde_blowup: CERT_BLOWUP,
        num_queries: CERT_QUERIES,
    }
}

// The per segment hint bit, one bit per squeeze word, derived from the message
// so the certificate is reproducible from its public inputs alone. The hint
// recovery band proves the recomposition relation over these bits; they are
// witness data and never reach the verifier.
fn derive_hints(message: &[u8], segments: usize) -> Vec<u64> {
    let mut bits = vec![0u8; segments.max(1)];
    shake256(message, &mut bits);
    bits.iter().map(|b| (*b & 1) as u64).collect()
}

/// A self contained batch certificate: the segment count and the serialized
#[derive(Clone)]
pub struct BatchProof {
    /// The number of SHAKE256 squeeze segments, one hash derived coefficient each.
    pub segments: usize,
    /// The serialized proof bytes.
    pub proof: Vec<u8>,
}

/// Proves the fused certificate over a public message and returns a batch
pub fn prove_batch(message: &[u8], segments: usize) -> BatchProof {
    assert!(
        message.len() <= MAX_MESSAGE_BYTES,
        "message must fit one SHAKE256 rate block"
    );
    assert!(segments >= 1, "a certificate needs at least one segment");
    let hints = derive_hints(message, segments);
    let cert = certificate_trace(segments, message, &hints);
    let proof = prove(&cert.air, &cert.trace, &params());
    BatchProof {
        segments,
        proof: encode_proof(&proof),
    }
}

/// Checks a batch certificate against the public message it claims. The squeeze
pub fn verify_batch(message: &[u8], cert: &BatchProof) -> bool {
    if message.len() > MAX_MESSAGE_BYTES || cert.segments == 0 {
        return false;
    }
    let proof = match decode_proof(&cert.proof) {
        Some(proof) => proof,
        None => return false,
    };
    let output = shake_output(SHAKE256_RATE, cert.segments, message);
    let air = certificate_air(cert.segments, message, &output);
    verify(&air, &params(), &proof)
}

impl BatchProof {
    /// Serializes the certificate to bytes, the segment count then the proof.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(8 + self.proof.len());
        out.extend_from_slice(&(self.segments as u64).to_le_bytes());
        out.extend_from_slice(&self.proof);
        out
    }

    /// Reads a certificate back from bytes, or None when they are too short.
    pub fn from_bytes(bytes: &[u8]) -> Option<BatchProof> {
        if bytes.len() < 8 {
            return None;
        }
        let mut segments = [0u8; 8];
        segments.copy_from_slice(&bytes[..8]);
        Some(BatchProof {
            segments: u64::from_le_bytes(segments) as usize,
            proof: bytes[8..].to_vec(),
        })
    }

    /// The serialized size of the certificate in bytes.
    pub fn size(&self) -> usize {
        8 + self.proof.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_batch_certificate_proves_and_verifies() {
        let message = b"module lattice batch entry point";
        let cert = prove_batch(message, 2);
        assert!(verify_batch(message, &cert));
    }

    #[test]
    fn a_certificate_over_a_different_message_is_rejected() {
        let cert = prove_batch(b"the message it was proven over", 2);
        assert!(!verify_batch(b"a different message entirely!!!!", &cert));
    }

    #[test]
    fn a_certificate_round_trips_through_bytes() {
        let message = b"round trip the batch certificate";
        let cert = prove_batch(message, 2);
        let bytes = cert.to_bytes();
        let restored = BatchProof::from_bytes(&bytes).expect("from_bytes");
        assert_eq!(restored.segments, cert.segments);
        assert!(verify_batch(message, &restored));
        assert_eq!(cert.size(), bytes.len());
    }

    #[test]
    fn a_wrong_segment_count_is_rejected() {
        let message = b"segment count must match the proof";
        let mut cert = prove_batch(message, 2);
        cert.segments = 4;
        assert!(!verify_batch(message, &cert));
    }

    #[test]
    fn a_short_body_decodes_to_none() {
        assert!(BatchProof::from_bytes(&[0u8; 4]).is_none());
    }
}
