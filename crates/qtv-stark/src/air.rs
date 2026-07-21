
use std::sync::Arc;

use crate::field::Felt;

pub struct TraceTable {
    width: usize,
    length: usize,
    columns: Vec<Vec<Felt>>,
}

impl TraceTable {
    pub fn new(width: usize, length: usize) -> Self {
        assert!(width >= 1, "a trace needs at least one column");
        assert!(length.is_power_of_two(), "length must be a power of two");
        TraceTable {
            width,
            length,
            columns: vec![vec![Felt::ZERO; length]; width],
        }
    }

    pub fn width(&self) -> usize {
        self.width
    }

    pub fn length(&self) -> usize {
        self.length
    }

    pub fn set(&mut self, column: usize, row: usize, value: Felt) {
        self.columns[column][row] = value;
    }

    pub fn get(&self, column: usize, row: usize) -> Felt {
        self.columns[column][row]
    }

    pub fn column(&self, column: usize) -> &[Felt] {
        &self.columns[column]
    }

    pub fn row(&self, row: usize) -> Vec<Felt> {
        self.columns.iter().map(|c| c[row]).collect()
    }
}

pub struct Transition {
    pub degree: usize,
    pub exclude_last: bool,
    pub uses_challenges: bool,
    pub rule: Box<dyn Fn(&[Felt], &[Felt], &[Felt]) -> Felt + Sync>,
}

pub struct Boundary {
    pub column: usize,
    pub row: usize,
    pub value: Felt,
}

type Factor = Arc<dyn Fn(&[Felt], &[Felt]) -> Felt + Send + Sync>;

struct Permutation {
    num_factor: Factor,
    den_factor: Factor,
}

pub struct Air {
    base_width: usize,
    aux_width: usize,
    length: usize,
    num_challenges: usize,
    transitions: Vec<Transition>,
    boundaries: Vec<Boundary>,
    permutations: Vec<Permutation>,
}

impl Air {
    pub fn new(width: usize, length: usize) -> Self {
        assert!(length.is_power_of_two(), "length must be a power of two");
        Air {
            base_width: width,
            aux_width: 0,
            length,
            num_challenges: 0,
            transitions: Vec::new(),
            boundaries: Vec::new(),
            permutations: Vec::new(),
        }
    }

    pub fn width(&self) -> usize {
        self.base_width + self.aux_width
    }

    pub fn base_width(&self) -> usize {
        self.base_width
    }

    pub fn aux_width(&self) -> usize {
        self.aux_width
    }

    pub fn num_challenges(&self) -> usize {
        self.num_challenges
    }

    pub fn length(&self) -> usize {
        self.length
    }

    pub fn transitions(&self) -> &[Transition] {
        &self.transitions
    }

    pub fn boundaries(&self) -> &[Boundary] {
        &self.boundaries
    }

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

    pub fn add_wrap_transition<F>(&mut self, degree: usize, rule: F)
    where
        F: Fn(&[Felt], &[Felt]) -> Felt + Sync + 'static,
    {
        self.transitions.push(Transition {
            degree,
            exclude_last: false,
            uses_challenges: false,
            rule: Box::new(move |current, next, _challenges| rule(current, next)),
        });
    }

    pub fn add_boundary(&mut self, column: usize, row: usize, value: Felt) {
        self.boundaries.push(Boundary { column, row, value });
    }

    pub fn add_challenge(&mut self) -> usize {
        let index = self.num_challenges;
        self.num_challenges += 1;
        index
    }

    pub fn add_permutation<N, D>(&mut self, degree: usize, num_factor: N, den_factor: D) -> usize
    where
        N: Fn(&[Felt], &[Felt]) -> Felt + Send + Sync + 'static,
        D: Fn(&[Felt], &[Felt]) -> Felt + Send + Sync + 'static,
    {
        let aux_col = self.base_width + self.aux_width;
        self.aux_width += 1;
        self.add_boundary(aux_col, 0, Felt::ONE);

        let num: Factor = Arc::new(num_factor);
        let den: Factor = Arc::new(den_factor);
        let num_rule = num.clone();
        let den_rule = den.clone();
        self.transitions.push(Transition {
            degree: degree + 1,
            exclude_last: false,
            uses_challenges: true,
            rule: Box::new(move |current, next, challenges| {
                let numerator = current[aux_col].mul(num_rule(current, challenges));
                let denominator = next[aux_col].mul(den_rule(current, challenges));
                denominator.sub(numerator)
            }),
        });
        self.permutations.push(Permutation {
            num_factor: num,
            den_factor: den,
        });
        aux_col
    }

    pub fn build_aux(&self, base: &TraceTable, challenges: &[Felt]) -> Vec<Vec<Felt>> {
        let n = self.length;
        let mut columns = Vec::with_capacity(self.permutations.len());
        for permutation in &self.permutations {
            let mut numerators = Vec::with_capacity(n);
            let mut denominators = Vec::with_capacity(n);
            for row in 0..n {
                let current = base.row(row);
                numerators.push((permutation.num_factor)(&current, challenges));
                denominators.push((permutation.den_factor)(&current, challenges));
            }
            let denominator_inv = crate::poly::batch_inverse(&denominators);
            let mut column = vec![Felt::ONE; n];
            let mut running = Felt::ONE;
            for row in 0..n - 1 {
                running = running.mul(numerators[row]).mul(denominator_inv[row]);
                column[row + 1] = running;
            }
            columns.push(column);
        }
        columns
    }

    pub fn assemble(&self, base: &TraceTable, challenges: &[Felt]) -> TraceTable {
        let aux = self.build_aux(base, challenges);
        let mut full = TraceTable::new(self.width().max(1), self.length);
        for column in 0..self.base_width {
            for row in 0..self.length {
                full.set(column, row, base.get(column, row));
            }
        }
        for (offset, column) in aux.iter().enumerate() {
            for row in 0..self.length {
                full.set(self.base_width + offset, row, column[row]);
            }
        }
        full
    }

    pub fn max_degree(&self) -> usize {
        self.transitions
            .iter()
            .map(|t| t.degree)
            .max()
            .unwrap_or(1)
            .max(1)
    }

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
            if boundary.column >= self.base_width {
                continue;
            }
            if trace.get(boundary.column, boundary.row) != boundary.value {
                return false;
            }
        }
        true
    }

    pub fn is_satisfied_with(&self, base: &TraceTable, challenges: &[Felt]) -> bool {
        assert_eq!(base.width(), self.base_width, "base trace width mismatch");
        assert_eq!(
            challenges.len(),
            self.num_challenges,
            "challenge count mismatch"
        );
        let trace = self.assemble(base, challenges);
        let n = self.length;
        for row in 0..n {
            let current = trace.row(row);
            let next = trace.row((row + 1) % n);
            for constraint in &self.transitions {
                if constraint.exclude_last && row == n - 1 {
                    continue;
                }
                if (constraint.rule)(&current, &next, challenges) != Felt::ZERO {
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

    fn permutation_air() -> Air {
        let mut air = Air::new(2, 8);
        let gamma = air.add_challenge();
        air.add_permutation(
            1,
            move |row, ch| ch[gamma].sub(row[0]),
            move |row, ch| ch[gamma].sub(row[1]),
        );
        air
    }

    #[test]
    fn a_reordering_is_a_permutation() {
        let air = permutation_air();
        let source = [3u64, 1, 4, 1, 5, 9, 2, 6];
        let shuffled = [6u64, 5, 4, 3, 2, 1, 1, 9];
        let mut base = TraceTable::new(2, 8);
        for row in 0..8 {
            base.set(0, row, Felt::new(source[row]));
            base.set(1, row, Felt::new(shuffled[row]));
        }
        let challenges = [Felt::new(20015998343868)];
        assert_eq!(air.num_challenges(), 1);
        assert_eq!(air.aux_width(), 1);
        assert!(air.is_satisfied_with(&base, &challenges));
    }

    #[test]
    fn a_mismatched_multiset_is_rejected() {
        let air = permutation_air();
        let source = [3u64, 1, 4, 1, 5, 9, 2, 6];
        let shuffled = [6u64, 5, 4, 3, 2, 1, 1, 6];
        let mut base = TraceTable::new(2, 8);
        for row in 0..8 {
            base.set(0, row, Felt::new(source[row]));
            base.set(1, row, Felt::new(shuffled[row]));
        }
        let challenges = [Felt::new(20015998343868)];
        assert!(!air.is_satisfied_with(&base, &challenges));
    }

    #[test]
    fn the_running_product_column_closes_to_one() {
        let air = permutation_air();
        let values = [7u64, 2, 7, 2, 7, 2, 7, 2];
        let mut base = TraceTable::new(2, 8);
        for row in 0..8 {
            base.set(0, row, Felt::new(values[row]));
            base.set(1, row, Felt::new(values[7 - row]));
        }
        let challenges = [Felt::new(173961102589770)];
        let aux = air.build_aux(&base, &challenges);
        assert_eq!(aux.len(), 1);
        assert_eq!(aux[0][0], Felt::ONE);
        assert!(air.is_satisfied_with(&base, &challenges));
    }
}
