# Batch verify relation results

These numbers come from the verify benchmark in this directory. Run it with
cargo bench and it prints the same fields to standard output. The machine is an
Apple Silicon host and the build uses the release profile. The parameter set is
ML DSA 65, a six by five public matrix over a ring of degree 256, with signature
modulus 8380417.

## What is proven

The module lattice verify relation is arithmetized piece by piece. Each piece is
a standalone description with its own trace, proved and verified on its own. The
benchmark sizes each piece to the work one batch of signatures produces and sums
the cost.

Transform domain modular multiplication. Every twiddle product of the transform
and every pointwise product of the matrix vector product is one modular
multiplication over the signature modulus, with the residue forced into the
canonical range by a two sided bit expansion. One signature contributes rows
times columns times the ring degree such products, so a batch of four fills
about thirty thousand rows.

Full transform. The eight layer number theoretic transform is wired into one
trace by the permutation argument, proved end to end in the ntt benchmark. It is
the transform the matrix vector product runs on both sides.

Response infinity norm. Each response coefficient is checked to lie within the
bound gamma1 minus beta of zero, so a coefficient in the middle band is rejected.
The centered magnitude is bit expanded on both sides of the bound. One signature
contributes columns times the ring degree coefficients.

Commitment decomposition. Each commitment coefficient splits into a high part and
a centered low part, congruent to the high part times alpha plus the low part
modulo the signature modulus, with both ranges pinned by bit expansions and the
boundary representation pinned by an inverse witness. One signature contributes
rows times the ring degree coefficients.

Hint recovery. On top of the decomposition, the hint bit recovers the high bits
the verifier hashes, moving the high part up or down by one according to the sign
of the low part, wrapping around the sixteen high values. One signature
contributes rows times the ring degree coefficients.

## Measured timings for a batch of four signatures

modular multiplication  rows 32768  columns 50  prove 6.9 s   verify 5.6 ms  bytes 489312
response norm           rows  8192  columns 43  prove 1.4 s   verify 4.6 ms  bytes 400160
decomposition           rows  8192  columns 49  prove 1.5 s   verify 4.7 ms  bytes 411440
hint recovery           rows  8192  columns 95  prove 2.7 s   verify 5.1 ms  bytes 458544

Total proving time is about 12.5 seconds.

Total verification time is about 20 milliseconds.

Total proof size is about 1.76 megabytes.

Every piece accepts its honest batch, and the module tests reject a wrong
residue, a coefficient outside the norm bound, a non canonical decomposition, a
forged sign flag, and a forged recovered high part.

## Remaining gap

Two parts of the relation are not arithmetized in this run.

The matrix and challenge expansion from the extendable output function. The
public matrix is expanded from a seed and the challenge is sampled from its hash,
both through SHAKE. Arithmetizing SHAKE means arithmetizing the Keccak
permutation as trace constraints, a large self contained effort that does not
fit this run. It is the one hash based piece the relation still needs in circuit.

The wiring of the separate pieces into one trace. Each piece here is proved on
its own description. A single verify circuit would carry the modular
multiplications, the decomposition, the norm, and the hint recovery in one trace
and connect the transform outputs to the decomposition inputs with the same
permutation argument the transform already uses. The permutation argument that
makes that wiring possible is in place and proved; joining the pieces under it is
the next step. The per piece costs here bound the cost of the joined circuit,
since the joined trace is their union.
