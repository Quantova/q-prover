# Contributing

This repository is part of the Quantova post quantum stack. Before you contribute, read the crypto policy and the handoff in the Quantova Specs repository. The crypto policy is the supreme law. If anything you are asked to do conflicts with it, stop and report.

## Cryptography

This proving system uses hash based STARKs and nothing else. There are no pairings, no KZG, no Groth16, and no elliptic curve operations, not even as a wrapper. The banned classical crates, including transitive and development dependencies, are enforced by cargo deny using the deny file in this repository. Performance never justifies a classical shortcut.

## Commits and pull requests

Author every commit as the repository owner only, with no other attribution anywhere. Keep the code clean with few comments and no filler. Work on a feature branch, open a pull request, and merge only when the checks are green. Every pull request names the specification section it implements.

## Claims discipline

Say sub second deterministic finality, one hundred thousand or more transactions per second through batch proofs and parallel execution, near trustless Bitcoin deposits, and trust minimized exits. Never say millisecond global finality, fully trustless bridge, or quantum proof.
