//! The constraint framework for the hash based proof.
//!
//! A computation is written as a table of field elements with a fixed column
//! count and a power of two row count. Constraints relate the cells of the
//! table. Transition constraints tie one row to the next, single row
//! constraints hold within a row, and boundary constraints pin one cell to a
//! fixed value.

use crate::field::Felt;

/// An execution trace laid out one column at a time.
pub struct TraceTable {
    width: usize,
    length: usize,
    columns: Vec<Vec<Felt>>,
}

impl TraceTable {
    /// Builds an all zero trace of the given shape. The length must be a power
    /// of two so that it matches a subgroup evaluation domain.
    pub fn new(width: usize, length: usize) -> Self {
        assert!(width >= 1, "a trace needs at least one column");
        assert!(length.is_power_of_two(), "length must be a power of two");
        TraceTable {
            width,
            length,
            columns: vec![vec![Felt::ZERO; length]; width],
        }
    }

    /// The number of columns.
    pub fn width(&self) -> usize {
        self.width
    }

    /// The number of rows.
    pub fn length(&self) -> usize {
        self.length
    }

    /// Writes a single cell.
    pub fn set(&mut self, column: usize, row: usize, value: Felt) {
        self.columns[column][row] = value;
    }

    /// Reads a single cell.
    pub fn get(&self, column: usize, row: usize) -> Felt {
        self.columns[column][row]
    }

    /// Borrows a whole column.
    pub fn column(&self, column: usize) -> &[Felt] {
        &self.columns[column]
    }

    /// Copies a whole row across the columns.
    pub fn row(&self, row: usize) -> Vec<Felt> {
        self.columns.iter().map(|c| c[row]).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cells_round_trip_through_the_table() {
        let mut trace = TraceTable::new(3, 8);
        assert_eq!(trace.width(), 3);
        assert_eq!(trace.length(), 8);
        for row in 0..8 {
            for col in 0..3 {
                trace.set(col, row, Felt::new((row * 3 + col) as u64));
            }
        }
        assert_eq!(trace.get(2, 5), Felt::new(17));
        assert_eq!(
            trace.row(5),
            vec![Felt::new(15), Felt::new(16), Felt::new(17)]
        );
        assert_eq!(trace.column(0)[7], Felt::new(21));
    }

    #[test]
    #[should_panic]
    fn a_non_power_of_two_length_is_refused() {
        let _ = TraceTable::new(2, 6);
    }
}
