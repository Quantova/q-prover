//! The general proof protocol over the constraint framework.
//!
//! The prover interpolates each trace column, extends it onto a coset of a
//! larger domain, and commits the extension with the Merkle module. It draws
//! constraint weights from the SHA3 transcript, forms one composition over the
//! coset, and hands that composition to the FRI low degree test. Trace cells are
//! opened at the query positions with their Merkle paths. The coset never meets
//! the trace domain, so every constraint quotient is defined at every opened
//! point.

use crate::air::{Air, TraceTable};
use crate::field::{root_of_unity, Felt, GENERATOR};
use crate::fri::{self, FriParams, FriProof, Transcript};
use crate::merkle::{hash_leaf, Digest, MerkleProof, MerkleTree};
use crate::poly;

/// The protocol parameters the prover and the verifier share.
pub struct StarkParams {
    /// The blow up factor of the low degree extension. A power of two of at
    /// least two.
    pub lde_blowup: usize,
    /// The number of query openings that back the soundness argument.
    pub num_queries: usize,
}

/// One opened trace row, the cells of every column at one domain index.
pub struct RowOpening {
    /// The index of the row in the extended domain.
    pub index: usize,
    /// The opened cell of each column.
    pub values: Vec<Felt>,
    /// The authentication path of each opened cell.
    pub paths: Vec<MerkleProof>,
}

/// The trace openings that back one query, the current and next rows at the two
/// paired positions of the query.
pub struct QueryOpening {
    /// The four opened rows in the fixed order current, next, paired current,
    /// paired next.
    pub rows: Vec<RowOpening>,
}

/// A proof that a trace satisfies an algebraic description.
pub struct StarkProof {
    /// The Merkle root of every committed trace column.
    pub trace_roots: Vec<Digest>,
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

    fn boundary_points(&self, air: &Air) -> Vec<Felt> {
        air.boundaries()
            .iter()
            .map(|b| self.omega_h.pow(b.row as u64))
            .collect()
    }
}

fn composition_value(
    air: &Air,
    weights: &[Felt],
    point: Felt,
    n: usize,
    last_point: Felt,
    boundary_points: &[Felt],
    current: &[Felt],
    next: &[Felt],
) -> Felt {
    let vanishing_inv = point.pow(n as u64).sub(Felt::ONE).inv();
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
    for (boundary, boundary_point) in air.boundaries().iter().zip(boundary_points) {
        let value = current[boundary.column].sub(boundary.value);
        let quotient = value.mul(point.sub(*boundary_point).inv());
        acc = acc.add(weights[index].mul(quotient));
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
    let mut trees: Vec<MerkleTree> = Vec::with_capacity(air.width());
    let mut roots: Vec<Digest> = Vec::with_capacity(air.width());
    for column in 0..air.width() {
        let coeffs = poly::interpolate(trace.column(column));
        let lde = poly::evaluate_coset(&coeffs, domain.log_size, domain.shift);
        let leaves: Vec<Digest> = lde.iter().map(|v| hash_leaf(*v)).collect();
        let tree = MerkleTree::commit(&leaves);
        roots.push(tree.root());
        trees.push(tree);
        column_lde.push(lde);
    }

    let mut transcript = Transcript::new();
    for root in &roots {
        transcript.absorb_digest(root);
    }
    let num_constraints = air.transitions().len() + air.boundaries().len();
    let weights: Vec<Felt> = (0..num_constraints)
        .map(|_| transcript.challenge_felt())
        .collect();

    let last_point = domain.last_point();
    let boundary_points = domain.boundary_points(air);
    let mut composition = vec![Felt::ZERO; domain.size];
    let mut point = domain.shift;
    for i in 0..domain.size {
        let shifted = (i + domain.lde_blowup) % domain.size;
        let current: Vec<Felt> = column_lde.iter().map(|col| col[i]).collect();
        let next: Vec<Felt> = column_lde.iter().map(|col| col[shifted]).collect();
        composition[i] = composition_value(
            air,
            &weights,
            point,
            domain.n,
            last_point,
            &boundary_points,
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
            let paths: Vec<MerkleProof> = trees.iter().map(|t| t.open(index)).collect();
            rows.push(RowOpening {
                index,
                values,
                paths,
            });
        }
        openings.push(QueryOpening { rows });
    }

    StarkProof {
        trace_roots: roots,
        fri: fri_proof,
        openings,
    }
}
