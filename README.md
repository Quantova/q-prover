# q-prover

The hash based STARK proving system for Quantova. It proves statements about the chain, above all that a batch of module lattice signatures verify, and it produces a certificate a light client can check. Every proof rests on hashing alone. There is no pairing and no elliptic curve operation anywhere in this system.

Quantova is a sovereign post quantum Layer 1 with only NIST standardized schemes and no classical escape hatch anywhere. A proving system is where most chains reach for an elliptic curve. Quantova does not. The soundness here comes from a collision resistant hash and a low degree test over a prime field, so the proof stands on the same footing as the rest of the stack.

## What it is

`qtv-stark` is the backend. It carries a prime field, Merkle commitments over SHA-3, the FRI low degree test, and a constraint framework, and on top of those it arithmetizes the module lattice signature so that a proof can attest the signature relation without revealing or re running it.

### The proof backend

- Field and transforms. Arithmetic over the Goldilocks prime with a number theoretic transform for interpolation and evaluation.
- Commitments. A Merkle tree that commits an extended trace row under one leaf, so a single path opens a whole row.
- Low degree test. FRI folds an evaluation vector round by round against challenges drawn from a SHA-3 transcript, which makes the protocol non interactive.
- Constraints. The AIR framework writes a computation as a trace of field cells with transition, single row, and boundary constraints, and a permutation argument that lets a value written in one row be consumed in a distant row. The prover interpolates each column, extends it onto a coset, commits it, forms one composition, and hands that to FRI. The verifier replays the transcript, runs the low degree test, checks the openings against the committed roots, and recomputes the composition from the opened cells.

The backend is exercised by round trip tests that prove and verify a correct trace, and by negative tests that reject a broken transition, a broken boundary, a tampered opening, a tampered root, a mismatched verifier, and a broken permutation.

### The module lattice arithmetization

The signature verify relation of ML-DSA-65 from FIPS 204 is broken into gadgets, each with its own reject tests.

- The SHA-3 permutation, named Qudros here, is arithmetized round by round, matching the crypto crate sponge on known inputs.
- The transform domain modular multiplication over the signature modulus, the atomic step of the verify relation.
- The response infinity norm range check, which rejects a response outside the FIPS 204 band.
- The commitment high and low bit decomposition and the hint recovery on top of it.
- The rejection sampling of the matrix coefficients below the modulus, RejNTTPoly, and the challenge ball sampling of the sparse challenge.

### The certificate

The fused certificate joins the hashing and the signature arithmetic into one proof. A single flat trace carries a SHAKE256 sponge band next to the per coefficient arithmetic band, and gated equalities and permutation arguments bind them so a prover cannot feed the arithmetic a coefficient the hash did not produce. The chain from the hash output, to the matrix coefficient, to the matrix vector product, to the response the norm bounds, cannot be split. The `entry` module wraps this as `prove_batch` and `verify_batch` over a public message, and the certificate travels as bytes for a light client to check, the same wrapper consensus and the QONCORD tally ride on.

A second arithmetization proves not that a signature verifies but that it is the canonical one, the output of ML-DSA-65 signing with the per signature randomizer fixed at zero. That is what gives the sortition draw its grinding resistance, since a hedged signature would verify just as well but is not canonical.

## Performance shape

Verification is designed to be far cheaper than proving, the asymmetry the consensus and light client paths depend on. A benchmark harness lives beside the code and reproduces with `cargo bench` for anyone building locally.

## Maturity

This is an active, early implementation, version 0.1.0, a single crate that depends on Q-Crypto for the SHA-3 and SHAKE primitives. The backend and the individual arithmetization gadgets are in place and tested. The fused certificate binds the hashing to the arithmetic at a batch of 16 coefficients today, and the work in progress is scaling that band to the full per signature coefficient count and folding in the remaining sampling gadgets, which widens the trace but keeps the same shape and binding. It is a from scratch reference implementation and has not been through an independent security audit.

## Cryptography

The proof system rests on SHA-3 and SHAKE from FIPS 202 and a prime field low degree test, with no pairing and no elliptic curve. It arithmetizes ML-DSA-65 from FIPS 204. The stack cryptography is validated against the NIST vectors and is not audited, and the chain is at testnet.

## Governance and license

Governed by the crypto policy, POLICY-crypto, in the Quantova-Specs repository. Commits are authored by the owner only. Dual licensed under Apache 2.0 and MIT.
