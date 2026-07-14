# Batch machine lattice verification results

These numbers come from the lattice benchmark in this directory. Run it with
cargo bench and it prints the same fields to standard output. The machine is an
Apple Silicon host and the build uses the release profile.

## What the batch proves

The machine lattice signature verifies through the number theoretic transform
and modular arithmetic over the signature modulus 8380417. The atomic step of
both the transform twiddle products and the pointwise products of the matrix
vector product is a modular multiplication over that modulus. The benchmark
builds the modular multiplication workload of the transform domain matrix vector
product for one signature. That matrix has six rows and five columns over a ring
of degree 256, so the batch holds 7680 coordinatewise modular multiplications,
padded to 8192 rows.

Each row proves that its residue equals the product of its two inputs modulo the
signature modulus. The row carries the quotient and two bit expansions. The
first expansion forces the residue below two to the twenty three. The second
expands the modulus minus one minus the residue, which together with the first
forces the residue into the canonical range zero to the modulus minus one. The
trace is 50 columns wide and carries 49 single row constraints.

## Measured timings

Proving time per proof is about 1.44 seconds.

Verification time per proof is about 4 milliseconds.

The serialized proof is about 406272 bytes.

The correct batch is accepted, and the lattice tests reject a batch whose
residue is wrong and a batch whose residue leaves the canonical range while
keeping the product identity.

## Scope reached

The modular multiplication relation is arithmetized in full, with the canonical
range enforced by the bit expansions. This is the core that the transform and
the pointwise products are built from, and the benchmark proves one signature
worth of that core over the matrix vector product.

The parts of the verification relation that remain are the wiring of the eight
transform layers into a single trace, which needs copy constraints across rows
that this framework does not yet carry, the modular addition and subtraction
reductions of the transform butterfly, the decomposition and hint checks, the
challenge expansion from the extendable output function, and range checks on the
transform inputs. These are additions on top of the modular arithmetic core
proven here, not changes to it.
