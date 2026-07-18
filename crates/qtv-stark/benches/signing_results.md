# Signing derivation benchmark results

These numbers come from the signing benchmark in this directory. Run it with cargo
bench and it prints the same fields to standard output. The machine is an Apple
Silicon host and the build uses the release profile. Nothing is tuned.

## What the derivation proves

Option A closes the sortition grind by carrying a proof that the module lattice
signature is the canonical derandomized one, the output of the FIPS 204 signing
algorithm run with the per signature randomizer fixed at zero. That is a proof
over the signing computation, heavier than the verification relation, and it puts
the secret key in the witness. The per message seed of the signing loop is rho_pp
equal to SHAKE256 of K joined with the randomizer joined with mu. The seed
derivation is arithmetized on the sponge with the randomizer field of the absorbed
block pinned to the thirty two zero bytes, so a proof accepts only the derivation
whose randomizer is zero. That pin is the one thing that separates this from a
verification proof, and it is what a hedged and ground signature cannot present.

One accepted iteration of the rejection loop is arithmetized end to end at the
ML DSA 65 scale, reusing the transform, the hashing, the norm, and the
decomposition gadgets the prover already carries. The masking expansion squeezes
SHAKE256 into the five mask polynomials. The matrix product transforms the mask,
multiplies it pointwise by the public matrix, and transforms back, and the
commitment high bits are recovered by the decomposition. The challenge absorbs mu
joined with the packed high bits over several blocks and SampleInBall turns it into
the sparse challenge. The response is the mask plus the challenge times the secret,
another transform and pointwise product. The norm checks bound the response and the
low bits. Each piece is arithmetized on its own description and proved on its own,
the same piece by piece method the batch verify relation is measured with, and the
bench sizes each distinct piece to the work one iteration produces.

## Measured cost per piece

Each distinct piece is proved and verified once on the host at its real per
iteration size. The final two columns are how many times the piece runs inside one
signing iteration and how many times it runs once per draw outside the loop.

    piece                          rows   cols   prove      verify    bytes      per iter  per draw
    seed derivation rho_pp           32   2037   0.924 s    47.4 ms   2250352    0         1
    mask expansion stream           256   2037   9.075 s    53.5 ms   2339536    5         0
    transform degree 256           1024    159   0.960 s     8.4 ms    470736    23        0
    transform pointwise products  16384     50   3.086 s     4.5 ms    447296    1         0
    commitment high bits           2048     49   0.304 s     3.5 ms    337648    1         0
    challenge hash absorb           256   2043  11.258 s    68.1 ms   2345680    1         0
    high bit packing               1024     11   0.045 s     2.9 ms    259776    1         0
    challenge ball sampling          64     23   0.004 s     2.0 ms    162384    1         0
    response infinity norm         2048     43   0.261 s     3.5 ms    326368    1         0
    low bits r0                    2048     49   0.313 s     3.6 ms    337648    1         0
    low bits magnitude bound       2048     43   0.257 s     3.5 ms    326368    1         0

The hashing pieces dominate. The mask expansion runs five times per iteration at
about nine seconds each and the challenge absorb once at about eleven seconds, so
the SHAKE arithmetization on the qudros permutation is the weight of the whole
derivation. The transform runs twenty three times at about one second each.

## One signing derivation

Composing each piece by its per iteration count gives one accepted iteration, the
mask expansion, the matrix product, the challenge, the response, and the norm
checks arithmetized end to end.

    prove   82.98 s
    verify  552.8 ms
    bytes   27.07 MB

The seed derivation runs once per draw outside the loop, adding about 0.924 s of
prove, 47.4 ms of verify, and 2.25 MB.

## The rejection loop and the per draw cost

The signing loop of ML DSA 65 retries until the response and the low bits pass
their bounds. The expected number of iterations for this parameter set is about
5.1, so about 4.1 iterations are rejected before the accepted one. The full
derandomization proof must also show that each earlier attempt was correctly
rejected, otherwise a prover could claim a rejected attempt was the accepted
signature. A rejected iteration performs the same computation the accepted one
does, the mask expansion, the matrix product, the challenge, the response, and the
norm checks, and only the outcome of the bound differs, so its arithmetized cost is
one iteration cost. The rejected iterations therefore add about 82.98 s of prove
and 552.8 ms of verify each, and about 340.2 s of prove and 2266.5 ms of verify in
total for the average draw.

The full derandomization proof for one draw is the seed derivation once plus about
5.1 iterations.

    prove   424.11 s
    verify  2866.6 ms
    bytes   140.30 MB

## The two numbers the founder asked for

The lookahead depth is how many 150 ms slots of lead time a validator needs to
precompute this proof off the critical path, taken from the measured prove time.
One accepted iteration at about 82.98 s forces 554 slots. The full per draw proof
at about 424.11 s forces 2828 slots. Both are far past any lookahead whose
predictability window is acceptable. A committee fixed 2828 slots ahead is a
committee named more than seven minutes ahead at a 150 ms slot, a runway an
adversary can target, deny, or bribe against.

On the critical path the verify is not affordable. One accepted iteration verifies
in about 552.8 ms and the full per draw proof in about 2866.6 ms, both well over
the 150 ms slot. The verify does not fit the critical path as measured.

## What still stands apart

These are separate proofs whose costs sum. The arithmetic bands carry
representative reduced values while the hashing bands carry genuine SHAKE256
streams, so the sizes and the costs are the real per iteration work; the exact
secret values do not change the trace shape. Folding the pieces into one succinct
proof by the recursion layer is the step that would replace the summed verify with
a single small verify on the critical path, and that recursion is not built or
measured here. The accepted iteration covers the mask expansion, the matrix
product, the challenge, the response, and the norm checks. The hint construction
from the challenge times t0 that follows a passing iteration is outside this
measured scope; it adds another K pointwise products, K inverse transforms, and the
hint recovery over K N coefficients on top of the accepted iteration.
