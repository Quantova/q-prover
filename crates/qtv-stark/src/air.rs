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

/// A constraint that reads the current row and the following row. The closure
/// returns zero when the constraint holds. The degree records the algebraic
/// degree of the closure so the protocol can size the low degree extension. The
/// third argument carries the transcript challenges, empty for constraints that
/// do not depend on them.
pub struct Transition {
    /// The algebraic degree of the closure in the trace cells.
    pub degree: usize,
    /// When true the constraint is not enforced on the last row, which is the
    /// row whose next row wraps around the domain.
    pub exclude_last: bool,
    /// When true the closure reads the transcript challenges and cannot be
    /// evaluated by the challenge free reference check.
    pub uses_challenges: bool,
    /// The closure over the current row, the next row, and the challenges.
    pub rule: Box<dyn Fn(&[Felt], &[Felt], &[Felt]) -> Felt + Sync>,
}

/// A constraint that pins one cell to a fixed value.
pub struct Boundary {
    /// The column of the pinned cell.
    pub column: usize,
    /// The row of the pinned cell.
    pub row: usize,
    /// The value the cell must hold.
    pub value: Felt,
}

/// The algebraic description of a computation, made of a shape and its
/// constraints.
pub struct Air {
    width: usize,
    length: usize,
    transitions: Vec<Transition>,
    boundaries: Vec<Boundary>,
}

impl Air {
    /// Starts an empty description for a trace of the given shape.
    pub fn new(width: usize, length: usize) -> Self {
        assert!(length.is_power_of_two(), "length must be a power of two");
        Air {
            width,
            length,
            transitions: Vec::new(),
            boundaries: Vec::new(),
        }
    }

    /// The trace width the description expects.
    pub fn width(&self) -> usize {
        self.width
    }

    /// The trace length the description expects.
    pub fn length(&self) -> usize {
        self.length
    }

    /// The transition constraints.
    pub fn transitions(&self) -> &[Transition] {
        &self.transitions
    }

    /// The boundary constraints.
    pub fn boundaries(&self) -> &[Boundary] {
        &self.boundaries
    }

    /// Adds a constraint that relates the current row to the next row. It is not
    /// enforced on the last row, whose next row wraps around the domain.
    pub fn add_transition<F>(&mut self, degree: usize, rule: F)
    where
        F: Fn(&[Felt], &[Felt]) -> Felt + Sync + 'static,
    {
        self.transitions.push(Transition {
            degree,
            exclude_last: true,
            uses_challenges: false,
            rule: Box::new(move |current, next, _challenges| rule(current, next)),
        });
    }

    /// Adds a constraint that holds within every row on its own. The closure
    /// receives the current row twice so a single form can serve both kinds.
    pub fn add_single_row<F>(&mut self, degree: usize, rule: F)
    where
        F: Fn(&[Felt]) -> Felt + Sync + 'static,
    {
        self.transitions.push(Transition {
            degree,
            exclude_last: false,
            uses_challenges: false,
            rule: Box::new(move |current, _next, _challenges| rule(current)),
        });
    }

    /// Pins the cell at the column and row to the value.
    pub fn add_boundary(&mut self, column: usize, row: usize, value: Felt) {
        self.boundaries.push(Boundary { column, row, value });
    }

    /// The largest algebraic degree among the transition constraints, never
    /// below one.
    pub fn max_degree(&self) -> usize {
        self.transitions
            .iter()
            .map(|t| t.degree)
            .max()
            .unwrap_or(1)
            .max(1)
    }

    /// Checks the trace against every constraint directly, without a proof. This
    /// is the reference the proof protocol must agree with. Constraints that read
    /// the transcript challenges are skipped here; an air that carries them is
    /// checked through is_satisfied_with instead.
    pub fn is_satisfied(&self, trace: &TraceTable) -> bool {
        let n = self.length;
        for row in 0..n {
            let current = trace.row(row);
            let next = trace.row((row + 1) % n);
            for constraint in &self.transitions {
                if constraint.uses_challenges {
                    continue;
                }
                if constraint.exclude_last && row == n - 1 {
                    continue;
                }
                if (constraint.rule)(&current, &next, &[]) != Felt::ZERO {
                    return false;
                }
            }
        }
        for boundary in &self.boundaries {
            if trace.get(boundary.column, boundary.row) != boundary.value {
                return false;
            }
        }
        true
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

    fn squaring_air() -> (Air, TraceTable) {
        let length = 8;
        let mut air = Air::new(1, length);
        air.add_transition(2, |current, next| next[0].sub(current[0].mul(current[0])));
        air.add_boundary(0, 0, Felt::new(3));
        let mut trace = TraceTable::new(1, length);
        let mut value = Felt::new(3);
        for row in 0..length {
            trace.set(0, row, value);
            value = value.mul(value);
        }
        (air, trace)
    }

    #[test]
    fn a_correct_trace_satisfies_the_description() {
        let (air, trace) = squaring_air();
        assert_eq!(air.max_degree(), 2);
        assert!(air.is_satisfied(&trace));
    }

    #[test]
    fn a_broken_transition_is_caught() {
        let (air, mut trace) = squaring_air();
        trace.set(0, 4, trace.get(0, 4).add(Felt::ONE));
        assert!(!air.is_satisfied(&trace));
    }

    #[test]
    fn a_broken_boundary_is_caught() {
        let (air, mut trace) = squaring_air();
        trace.set(0, 0, Felt::new(4));
        assert!(!air.is_satisfied(&trace));
    }

    #[test]
    fn a_single_row_constraint_holds_on_every_row() {
        let length = 4;
        let mut air = Air::new(2, length);
        air.add_single_row(2, |row| row[1].sub(row[0].mul(row[0])));
        let mut trace = TraceTable::new(2, length);
        for row in 0..length {
            let base = Felt::new((row + 2) as u64);
            trace.set(0, row, base);
            trace.set(1, row, base.mul(base));
        }
        assert!(air.is_satisfied(&trace));
        trace.set(1, length - 1, Felt::ZERO);
        assert!(!air.is_satisfied(&trace));
    }
}
