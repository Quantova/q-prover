# q-prover

The hash based STARK proving system for Quantova. Every proof rests on hashing alone. There is no pairing and no elliptic curve operation anywhere in this system.

## What it is

`qtv-stark` is the backend. It carries a prime field, Merkle commitments over SHA-3, the FRI low degree test and a constraint framework.

- Field and transforms. Arithmetic over the Goldilocks prime with a number theoretic transform for interpolation and evaluation.
- Commitments. A Merkle tree that commits an extended trace row under one leaf, so a single path opens a whole row.
- Low degree test. FRI folds an evaluation vector round by round against challenges drawn from a SHA-3 transcript, which makes the protocol non interactive. The `prover` and `verifier` modules are thin wrappers that run this low degree test on its own.
- Constraints. The AIR framework writes a computation as a trace of field cells with transition, single row and boundary constraints, and a permutation argument that lets a value written in one row be consumed in a distant row. The prover interpolates each column, extends it onto a coset, commits it, forms one composition and hands that to FRI. The verifier replays the transcript, runs the low degree test, checks the openings against the committed roots and recomputes the composition from the opened cells.

## Statement binding and soundness

The transcript absorbs the full statement before any challenge is drawn. That is the trace length and widths, every boundary value, the public bytes, the evaluation domain, the blow up factors, the query count, whether the trace is masked, and the degree and shape of every transition and permutation constraint. A proof therefore cannot be replayed under other parameters or against a circuit of another shape, and a caller may add its own domain tag through `verify_with_domain`.

`verify`, `verify_with_domain` and `verify_zk` refuse any parameter set whose composition soundness falls below 128 bits, and any domain larger than the two adic subgroup of the field. A caller cannot lower the bar by passing weaker parameters.

## Gadgets

The repository holds standalone arithmetizations of pieces of the ML-DSA-65 verify relation from FIPS 204. Each is a self contained AIR with its own reject tests.

- The SHA-3 permutation, named Qudros here, arithmetized round by round and matched against the crypto crate sponge.
- Modular multiplication in the transform domain over the signature modulus.
- The response infinity norm range check.
- The commitment high and low bit decomposition and the hint recovery on top of it.
- The rejection sampling of matrix coefficients and the challenge ball sampling, with every sampled byte range checked.

These gadgets are building blocks. No module in this repository proves that a signature verifies, and no other part of the stack relies on one. An earlier batch certificate that claimed to do so was removed because it did not bind the signature relation.

## The zero knowledge VRF, kept and not used

The `zkvrf` module is a verifiable random function proven in zero knowledge. It hashes a secret key and a public input through a Rescue sponge and proves the output is right without revealing the key. It is complete and tested and meets the same 128 bit floor. Nothing in the chain, the oracle or consensus calls it. The chain selects its validators deterministically and needs no proof per block.

No key of any kind is stored in the repository. The key a caller passes in is used only for the length of one proof, and every state derived from it is wiped from memory once the proof is made.

## Build and test

```
cargo test --release
cargo bench
```

## Maturity

Version 0.1.0, a single crate that depends on Q-Crypto for the SHA-3 and SHAKE primitives. It is a from scratch reference implementation.

## Cryptography

The proof system rests on SHA-3 and SHAKE from FIPS 202 and a prime field low degree test, with no pairing and no elliptic curve. The stack cryptography is validated against the NIST vectors.

## Governance and license

Governed by the crypto policy, POLICY-crypto, in the Quantova-Specs repository. Dual licensed under Apache 2.0 and MIT.
