
use crate::air::{Air, TraceTable};
use crate::field::Felt;

pub const NIBBLE_BITS: usize = 4;

const COL_LO: usize = 0;
const COL_HI: usize = 1;
const COL_BYTE: usize = 2;
const COL_LO_BITS: usize = 3;
const COL_HI_BITS: usize = COL_LO_BITS + NIBBLE_BITS;

pub const WIDTH: usize = COL_HI_BITS + NIBBLE_BITS;

pub const LO_COL: usize = COL_LO;

pub const HI_COL: usize = COL_HI;

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

pub fn w1_encode(highs: &[u8]) -> Vec<u8> {
    assert!(
        highs.len() % 2 == 0,
        "the four bit packing takes byte pairs"
    );
    highs
        .chunks(2)
        .map(|pair| (pair[0] & 15) | ((pair[1] & 15) << 4))
        .collect()
}

pub fn seed_index_bytes(row: usize, col: usize) -> [u8; 2] {
    [col as u8, row as u8]
}

pub fn add_constraints(air: &mut Air, base: usize) {
    let sixteen = Felt::new(16);
    let lo = base + COL_LO;
    let hi = base + COL_HI;
    let byte = base + COL_BYTE;

    air.add_single_row(1, move |row| {
        recompose(row, base + COL_LO_BITS, NIBBLE_BITS).sub(row[lo])
    });
    air.add_single_row(1, move |row| {
        recompose(row, base + COL_HI_BITS, NIBBLE_BITS).sub(row[hi])
    });

    air.add_single_row(1, move |row| {
        row[byte].sub(row[lo]).sub(row[hi].mul(sixteen))
    });

    for start in [COL_LO_BITS, COL_HI_BITS] {
        for k in 0..NIBBLE_BITS {
            let col = base + start + k;
            air.add_single_row(2, move |row| row[col].mul(row[col].sub(Felt::ONE)));
        }
    }
}

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

pub fn fill_row(trace: &mut TraceTable, base: usize, row: usize, lo: u8, hi: u8) {
    let lo = (lo & 15) as u64;
    let hi = (hi & 15) as u64;
    trace.set(base + COL_LO, row, Felt::new(lo));
    trace.set(base + COL_HI, row, Felt::new(hi));
    trace.set(base + COL_BYTE, row, Felt::new(lo + 16 * hi));
    set_bits(trace, base + COL_LO_BITS, row, lo, NIBBLE_BITS);
    set_bits(trace, base + COL_HI_BITS, row, hi, NIBBLE_BITS);
}

pub struct EncodeBatch {
    pub air: Air,
    pub trace: TraceTable,
    pub bytes: Vec<u8>,
}

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
        (0..64u8).map(|i| i.wrapping_mul(7) & 15).collect()
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
