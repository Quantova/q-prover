//! The encodings that bridge the field element pieces to the hash byte input.
//!
//! Two encodings feed the hashes of the verify relation. The commitment high bits,
//! four bits each, pack two to a byte to form the w1 encoding that the challenge
//! hash absorbs, w1Encode of FIPS 204. The matrix seed carries the two entry index
//! bytes appended to the public seed, the column and the row, that the matrix
//! expansion hashes.
//!
//! This module arithmetizes the high bit packing. Each row folds two four bit high
//! parts into one byte, range checked to a nibble each, so the byte the hash reads
//! is bound to the high parts the arithmetic recovers. The seed index encoding is a
//! direct byte, exposed as a helper and validated against the crypto reference
//! layout.

use crate::air::{Air, TraceTable};
use crate::field::Felt;

/// The bit width of a packed high part.
pub const NIBBLE_BITS: usize = 4;

const COL_LO: usize = 0;
const COL_HI: usize = 1;
const COL_BYTE: usize = 2;
const COL_LO_BITS: usize = 3;
const COL_HI_BITS: usize = COL_LO_BITS + NIBBLE_BITS;

/// The column width of the high bit packing piece.
pub const WIDTH: usize = COL_HI_BITS + NIBBLE_BITS;

/// The low nibble column relative to the piece base, the even high part.
pub const LO_COL: usize = COL_LO;

/// The high nibble column relative to the piece base, the odd high part.
pub const HI_COL: usize = COL_HI;

/// The packed byte column relative to the piece base.
pub const BYTE_COL: usize = COL_BYTE;

fn recompose(row: &[Felt], base: usize, bits: usize) -> Felt {
    let two = Felt::new(2);
    let mut acc = Felt::ZERO;
    let mut weight = Felt::ONE;
    for k in 0..bits {
        acc = acc.add(row[base + k].mul(weight));
        weight = weight.mul(two);
    }
    acc
}

/// Packs a sequence of four bit high parts into bytes, two to a byte low nibble
/// first, the w1 encoding restricted to the four bit width of the parameter set.
pub fn w1_encode(highs: &[u8]) -> Vec<u8> {
    assert!(
        highs.len() % 2 == 0,
        "the four bit packing takes byte pairs"
    );
    highs
        .chunks(2)
        .map(|pair| (pair[0] & 0x0f) | ((pair[1] & 0x0f) << 4))
        .collect()
}

/// The two index bytes appended to the public seed for a matrix entry, the column
/// and the row, as the matrix expansion of the verify relation encodes them.
pub fn seed_index_bytes(row: usize, col: usize) -> [u8; 2] {
    [col as u8, row as u8]
}

/// Adds the high bit packing constraints at the given column base, so the piece can
/// be placed inside a wider joined trace.
pub fn add_constraints(air: &mut Air, base: usize) {
    let sixteen = Felt::new(16);
    let lo = base + COL_LO;
    let hi = base + COL_HI;
    let byte = base + COL_BYTE;

    // Each nibble recomposes from its bits, which forces it below sixteen.
    air.add_single_row(1, move |row| {
        recompose(row, base + COL_LO_BITS, NIBBLE_BITS).sub(row[lo])
    });
    air.add_single_row(1, move |row| {
        recompose(row, base + COL_HI_BITS, NIBBLE_BITS).sub(row[hi])
    });

    // The byte is the low nibble in the low half and the high nibble in the high
    // half.
    air.add_single_row(1, move |row| {
        row[byte].sub(row[lo]).sub(row[hi].mul(sixteen))
    });

    // Every nibble bit is zero or one.
    for start in [COL_LO_BITS, COL_HI_BITS] {
        for k in 0..NIBBLE_BITS {
            let col = base + start + k;
            air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
        }
    }
}

/// Builds the high bit packing description of the given length. The length must be
/// a power of two.
pub fn encode_air(length: usize) -> Air {
    let mut air = Air::new(WIDTH, length);
    add_constraints(&mut air, 0);
    air
}

fn set_bits(trace: &mut TraceTable, col: usize, row: usize, value: u64, bits: usize) {
    for k in 0..bits {
        trace.set(col + k, row, Felt::new((value >> k) & 1));
    }
}

/// Fills one high bit packing row at the given column base over one nibble pair.
pub fn fill_row(trace: &mut TraceTable, base: usize, row: usize, lo: u8, hi: u8) {
    let lo = (lo & 0x0f) as u64;
    let hi = (hi & 0x0f) as u64;
    trace.set(base + COL_LO, row, Felt::new(lo));
    trace.set(base + COL_HI, row, Felt::new(hi));
    trace.set(base + COL_BYTE, row, Felt::new(lo + 16 * hi));
    set_bits(trace, base + COL_LO_BITS, row, lo, NIBBLE_BITS);
    set_bits(trace, base + COL_HI_BITS, row, hi, NIBBLE_BITS);
}

/// A filled high bit packing batch with its description and the packed bytes.
pub struct EncodeBatch {
    /// The description shared with the verifier.
    pub air: Air,
    /// The filled trace.
    pub trace: TraceTable,
    /// The packed bytes, the w1 encoding of the high parts.
    pub bytes: Vec<u8>,
}

/// Lays out a trace that packs a sequence of high parts into bytes, two to a row.
/// The high parts are padded with zeros to an even count and the trace is padded to
/// a power of two length.
pub fn encode_batch(highs: &[u8]) -> EncodeBatch {
    let mut padded = highs.to_vec();
    if padded.len() % 2 == 1 {
        padded.push(0);
    }
    let count = padded.len() / 2;
    let length = count.next_power_of_two().max(2);
    let mut trace = TraceTable::new(WIDTH, length);
    for row in 0..length {
        let (lo, hi) = if row < count {
            (padded[2 * row], padded[2 * row + 1])
        } else {
            (0, 0)
        };
        fill_row(&mut trace, 0, row, lo, hi);
    }
    EncodeBatch {
        air: encode_air(length),
        trace,
        bytes: w1_encode(&padded),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hashing::matrix_entry_seed;
    use crate::stark::{prove, verify, StarkParams};

    fn params() -> StarkParams {
        StarkParams {
            lde_blowup: 8,
            num_queries: 24,
        }
    }

    fn sample_highs() -> Vec<u8> {
        (0..64u8).map(|i| i.wrapping_mul(7) & 0x0f).collect()
    }

    #[test]
    fn the_packing_matches_the_reference_layout() {
        let highs = sample_highs();
        let bytes = w1_encode(&highs);
        assert_eq!(bytes.len(), highs.len() / 2);
        for (b, pair) in bytes.iter().zip(highs.chunks(2)) {
            assert_eq!(*b, pair[0] | (pair[1] << 4));
        }
    }

    #[test]
    fn the_seed_index_bytes_place_the_column_then_the_row() {
        let rho = [0u8; 32];
        let seed = matrix_entry_seed(&rho, 5, 4);
        let idx = seed_index_bytes(5, 4);
        assert_eq!(idx, [4, 5]);
        assert_eq!([seed[32], seed[33]], idx);
    }

    #[test]
    fn the_byte_column_holds_the_packed_bytes() {
        let batch = encode_batch(&sample_highs());
        for (row, b) in batch.bytes.iter().enumerate() {
            assert_eq!(batch.trace.get(BYTE_COL, row).to_u64(), *b as u64);
        }
    }

    #[test]
    fn the_arithmetic_holds_on_every_row() {
        let batch = encode_batch(&sample_highs());
        assert!(batch.air.is_satisfied(&batch.trace));
    }

    #[test]
    fn a_tampered_byte_is_rejected() {
        let batch = encode_batch(&sample_highs());
        let mut trace = batch.trace;
        trace.set(BYTE_COL, 1, trace.get(BYTE_COL, 1).add(Felt::ONE));
        assert!(!batch.air.is_satisfied(&trace));
    }

    #[test]
    fn an_out_of_range_nibble_is_rejected() {
        let batch = encode_batch(&sample_highs());
        let mut trace = batch.trace;
        // A nibble above fifteen keeps the byte identity only by leaving the range.
        trace.set(LO_COL, 2, Felt::new(16));
        trace.set(BYTE_COL, 2, trace.get(BYTE_COL, 2).add(Felt::new(16)));
        assert!(!batch.air.is_satisfied(&trace));
    }

    #[test]
    fn a_batch_proves_and_verifies() {
        let batch = encode_batch(&sample_highs());
        let proof = prove(&batch.air, &batch.trace, &params());
        assert!(verify(&encode_air(batch.trace.length()), &params(), &proof));
    }
}
