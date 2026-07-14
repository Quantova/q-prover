//! The general proof protocol over the constraint framework.

use crate::air::{Air, TraceTable};
use crate::field::{root_of_unity, Felt, GENERATOR};
use crate::fri::{self, FriParams, FriProof, Transcript};
use crate::merkle::{hash_row, Digest, MerkleProof, MerkleTree};
use crate::poly;

/// The protocol parameters the prover and the verifier share.
pub struct StarkParams {
    /// The blow up factor of the low degree extension. A power of two of at
    pub lde_blowup: usize,
    /// The number of query openings that back the soundness argument.
    pub num_queries: usize,
}

/// One opened trace row, the cells of every column at one domain index, tied to
pub struct RowOpening {
    /// The index of the row in the extended domain.
    pub index: usize,
    /// The opened cell of each column.
    pub values: Vec<Felt>,
    /// The authentication path of the row leaf.
    pub path: MerkleProof,
}

/// The trace openings that back one query, the current and next rows at the two
pub struct QueryOpening {
    /// The four opened rows in the fixed order current, next, paired current,
    pub rows: Vec<RowOpening>,
}

/// A proof that a trace satisfies an algebraic description.
pub struct StarkProof {
    /// The Merkle root that commits every trace row.
    pub trace_root: Digest,
    /// The low degree proof over the composition.
    pub fri: FriProof,
    /// The trace openings that tie the composition to the constraints.
    pub openings: Vec<QueryOpening>,
}

struct Domain {
    n: usize,
    size: usize,
    log_size: u32,
    lde_blowup: usize,
    fri_blowup: usize,
    omega_n: Felt,
    omega_h: Felt,
    shift: Felt,
}

impl Domain {
    fn new(air: &Air, params: &StarkParams) -> Self {
        let n = air.length();
        let log_n = n.trailing_zeros();
        let lde_blowup = params.lde_blowup;
        assert!(
            lde_blowup.is_power_of_two() && lde_blowup >= 2,
            "blow up must be a power of two of at least two"
        );
        let log_size = log_n + lde_blowup.trailing_zeros();
        let factor = air.max_degree().next_power_of_two();
        let fri_blowup = lde_blowup / factor;
        assert!(
            fri_blowup >= 2,
            "the constraint degree is too high for the chosen blow up"
        );
        Domain {
            n,
            size: 1usize << log_size,
            log_size,
            lde_blowup,
            fri_blowup,
            omega_n: root_of_unity(log_size),
            omega_h: root_of_unity(log_n),
            shift: Felt::new(GENERATOR),
        }
    }

    fn fri_params(&self, num_queries: usize) -> FriParams {
        FriParams {
            log_domain_size: self.log_size,
            num_queries,
            blowup: self.fri_blowup,
        }
    }

    fn last_point(&self) -> Felt {
        self.omega_h.pow((self.n - 1) as u64)
    }

    // The transition denominator x to the n minus one at every coset point,
    // built with the blow up root so no per point exponentiation is needed.
    fn vanishing_over_coset(&self) -> Vec<Felt> {
        let zeta = root_of_unity(self.lde_blowup.trailing_zeros());
        let mut value = self.shift.pow(self.n as u64);
        let mut out = Vec::with_capacity(self.size);
        for _ in 0..self.size {
            out.push(value.sub(Felt::ONE));
            value = value.mul(zeta);
        }
        out
    }

    fn boundary_points(&self, air: &Air) -> Vec<Felt> {
        air.boundaries()
            .iter()
            .map(|b| self.omega_h.pow(b.row as u64))
            .collect()
    }
}

// Inverts x minus each boundary point at a single point, for the verifier which
// only touches a handful of points.
fn boundary_inverses(point: Felt, boundary_points: &[Felt]) -> Vec<Felt> {
    boundary_points
        .iter()
        .map(|boundary_point| point.sub(*boundary_point).inv())
        .collect()
}

// Evaluates the weighted composition at one point. The vanishing inverse is the
// inverse of the transition denominator x to the n minus one, and the boundary
// inverses are the inverses of x minus the boundary point, both supplied by the
// caller so they can be batched.
fn composition_value(
    air: &Air,
    weights: &[Felt],
    point: Felt,
    last_point: Felt,
    vanishing_inv: Felt,
    boundary_inv: &[Felt],
    current: &[Felt],
    next: &[Felt],
) -> Felt {
    let mut acc = Felt::ZERO;
    let mut index = 0;
    for constraint in air.transitions() {
        let value = (constraint.rule)(current, next);
        let quotient = if constraint.exclude_last {
            value.mul(point.sub(last_point)).mul(vanishing_inv)
        } else {
            value.mul(vanishing_inv)
        };
        acc = acc.add(weights[index].mul(quotient));
        index += 1;
    }
    for (boundary, inverse) in air.boundaries().iter().zip(boundary_inv) {
        let value = current[boundary.column].sub(boundary.value);
        acc = acc.add(weights[index].mul(value.mul(*inverse)));
        index += 1;
    }
    acc
}

/// Produces a proof that the trace satisfies the description.
pub fn prove(air: &Air, trace: &TraceTable, params: &StarkParams) -> StarkProof {
    assert_eq!(trace.width(), air.width(), "trace width mismatch");
    assert_eq!(trace.length(), air.length(), "trace length mismatch");
    let domain = Domain::new(air, params);

    let mut column_lde: Vec<Vec<Felt>> = Vec::with_capacity(air.width());
    for column in 0..air.width() {
        let coeffs = poly::interpolate(trace.column(column));
        let lde = poly::evaluate_coset(&coeffs, domain.log_size, domain.shift);
        column_lde.push(lde);
    }

    // Commit every extended row under a single leaf so one path opens a whole
    // row across the columns.
    let mut row = vec![Felt::ZERO; air.width()];
    let mut leaves: Vec<Digest> = Vec::with_capacity(domain.size);
    for i in 0..domain.size {
        for (column, cell) in column_lde.iter().zip(row.iter_mut()) {
            *cell = column[i];
        }
        leaves.push(hash_row(&row));
    }
    let tree = MerkleTree::commit(&leaves);
    let trace_root = tree.root();

    let mut transcript = Transcript::new();
    transcript.absorb_digest(&trace_root);
    let num_constraints = air.transitions().len() + air.boundaries().len();
    let weights: Vec<Felt> = (0..num_constraints)
        .map(|_| transcript.challenge_felt())
        .collect();

    let last_point = domain.last_point();
    let boundary_points = domain.boundary_points(air);

    // Precompute the constraint denominators over the coset and invert them all
    // with one field inversion each.
    let vanishing_inv = poly::batch_inverse(&domain.vanishing_over_coset());
    let mut boundary_inv_columns: Vec<Vec<Felt>> = Vec::with_capacity(boundary_points.len());
    for boundary_point in &boundary_points {
        let mut denominators = Vec::with_capacity(domain.size);
        let mut point = domain.shift;
        for _ in 0..domain.size {
            denominators.push(point.sub(*boundary_point));
            point = point.mul(domain.omega_n);
        }
        boundary_inv_columns.push(poly::batch_inverse(&denominators));
    }

    let mut composition = vec![Felt::ZERO; domain.size];
    let mut current = vec![Felt::ZERO; air.width()];
    let mut next = vec![Felt::ZERO; air.width()];
    let mut boundary_inv = vec![Felt::ZERO; boundary_points.len()];
    let mut point = domain.shift;
    for i in 0..domain.size {
        let shifted = (i + domain.lde_blowup) % domain.size;
        for (column, cell) in column_lde.iter().zip(current.iter_mut()) {
            *cell = column[i];
        }
        for (column, cell) in column_lde.iter().zip(next.iter_mut()) {
            *cell = column[shifted];
        }
        for (column, cell) in boundary_inv_columns.iter().zip(boundary_inv.iter_mut()) {
            *cell = column[i];
        }
        composition[i] = composition_value(
            air,
            &weights,
            point,
            last_point,
            vanishing_inv[i],
            &boundary_inv,
            &current,
            &next,
        );
        point = point.mul(domain.omega_n);
    }

    let fri_proof = fri::prove(&composition, &domain.fri_params(params.num_queries));

    let half = domain.size / 2;
    let mut openings = Vec::with_capacity(fri_proof.queries.len());
    for query in &fri_proof.queries {
        let p = query.position;
        let indices = [
            p,
            (p + domain.lde_blowup) % domain.size,
            p + half,
            (p + half + domain.lde_blowup) % domain.size,
        ];
        let mut rows = Vec::with_capacity(indices.len());
        for &index in &indices {
            let values: Vec<Felt> = column_lde.iter().map(|col| col[index]).collect();
            rows.push(RowOpening {
                index,
                values,
                path: tree.open(index),
            });
        }
        openings.push(QueryOpening { rows });
    }

    StarkProof {
        trace_root,
        fri: fri_proof,
        openings,
    }
}

/// Checks a proof against the description without the trace.
pub fn verify(air: &Air, params: &StarkParams, proof: &StarkProof) -> bool {
    let domain = Domain::new(air, params);
    let mut transcript = Transcript::new();
    transcript.absorb_digest(&proof.trace_root);
    let num_constraints = air.transitions().len() + air.boundaries().len();
    let weights: Vec<Felt> = (0..num_constraints)
        .map(|_| transcript.challenge_felt())
        .collect();

    if !fri::verify(&domain.fri_params(params.num_queries), &proof.fri) {
        return false;
    }
    if proof.openings.len() != proof.fri.queries.len() {
        return false;
    }

    let half = domain.size / 2;
    let last_point = domain.last_point();
    let boundary_points = domain.boundary_points(air);

    for (query, opening) in proof.fri.queries.iter().zip(&proof.openings) {
        let p = query.position;
        if p >= half {
            return false;
        }
        let expected = [
            p,
            (p + domain.lde_blowup) % domain.size,
            p + half,
            (p + half + domain.lde_blowup) % domain.size,
        ];
        if opening.rows.len() != expected.len() {
            return false;
        }
        for (row, &index) in opening.rows.iter().zip(expected.iter()) {
            if row.index != index || row.values.len() != air.width() || row.path.leaf_index != index
            {
                return false;
            }
            if !crate::merkle::verify(&proof.trace_root, &hash_row(&row.values), &row.path) {
                return false;
            }
        }

        let point_low = domain.shift.mul(domain.omega_n.pow(p as u64));
        let recomputed_low = composition_value(
            air,
            &weights,
            point_low,
            last_point,
            point_low.pow(domain.n as u64).sub(Felt::ONE).inv(),
            &boundary_inverses(point_low, &boundary_points),
            &opening.rows[0].values,
            &opening.rows[1].values,
        );
        if recomputed_low != query.layers[0].eval {
            return false;
        }

        let point_high = domain.shift.mul(domain.omega_n.pow((p + half) as u64));
        let recomputed_high = composition_value(
            air,
            &weights,
            point_high,
            last_point,
            point_high.pow(domain.n as u64).sub(Felt::ONE).inv(),
            &boundary_inverses(point_high, &boundary_points),
            &opening.rows[2].values,
            &opening.rows[3].values,
        );
        if recomputed_high != query.layers[0].sibling {
            return false;
        }
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn params() -> StarkParams {
        StarkParams {
            lde_blowup: 8,
            num_queries: 24,
        }
    }

    // A squaring chain, the running value squares from one row to the next.
    fn squaring(length: usize, seed: Felt) -> (Air, TraceTable) {
        let mut air = Air::new(1, length);
        air.add_transition(2, |current, next| next[0].sub(current[0].mul(current[0])));
        air.add_boundary(0, 0, seed);
        let mut trace = TraceTable::new(1, length);
        let mut value = seed;
        for row in 0..length {
            trace.set(0, row, value);
            value = value.mul(value);
        }
        (air, trace)
    }

    #[test]
    fn a_correct_trace_proves_and_verifies() {
        let (air, trace) = squaring(16, Felt::new(3));
        assert!(air.is_satisfied(&trace));
        let proof = prove(&air, &trace, &params());
        assert!(verify(&air, &params(), &proof));
    }

    #[test]
    fn a_trace_that_breaks_a_transition_is_rejected() {
        let (air, mut trace) = squaring(16, Felt::new(3));
        trace.set(0, 7, trace.get(0, 7).add(Felt::ONE));
        assert!(!air.is_satisfied(&trace));
        let proof = prove(&air, &trace, &params());
        assert!(!verify(&air, &params(), &proof));
    }

    #[test]
    fn a_trace_that_breaks_a_boundary_is_rejected() {
        let (air, _) = squaring(16, Felt::new(3));
        // A trace of the same shape whose seed is wrong.
        let (_, wrong) = squaring(16, Felt::new(5));
        assert!(!air.is_satisfied(&wrong));
        let proof = prove(&air, &wrong, &params());
        assert!(!verify(&air, &params(), &proof));
    }

    #[test]
    fn a_tampered_trace_opening_is_rejected() {
        let (air, trace) = squaring(16, Felt::new(3));
        let mut proof = prove(&air, &trace, &params());
        let cell = proof.openings[0].rows[0].values[0];
        proof.openings[0].rows[0].values[0] = cell.add(Felt::ONE);
        assert!(!verify(&air, &params(), &proof));
    }

    #[test]
    fn a_tampered_trace_root_is_rejected() {
        let (air, trace) = squaring(16, Felt::new(3));
        let mut proof = prove(&air, &trace, &params());
        proof.trace_root[0] ^= 1;
        assert!(!verify(&air, &params(), &proof));
    }

    #[test]
    fn a_verifier_with_a_different_boundary_rejects() {
        let (air, trace) = squaring(16, Felt::new(3));
        let proof = prove(&air, &trace, &params());
        let mut other = Air::new(1, 16);
        other.add_transition(2, |current, next| next[0].sub(current[0].mul(current[0])));
        other.add_boundary(0, 0, Felt::new(9));
        assert!(!verify(&other, &params(), &proof));
    }

    #[test]
    fn a_wider_trace_with_two_columns_round_trips() {
        let length = 32;
        let mut air = Air::new(2, length);
        // The first column runs a squaring chain, the second mirrors its square.
        air.add_transition(2, |current, next| next[0].sub(current[0].mul(current[0])));
        air.add_single_row(2, |row| row[1].sub(row[0].mul(row[0])));
        air.add_boundary(0, 0, Felt::new(2));
        let mut trace = TraceTable::new(2, length);
        let mut value = Felt::new(2);
        for row in 0..length {
            trace.set(0, row, value);
            trace.set(1, row, value.mul(value));
            value = value.mul(value);
        }
        assert!(air.is_satisfied(&trace));
        let proof = prove(&air, &trace, &params());
        assert!(verify(&air, &params(), &proof));
    }
}
