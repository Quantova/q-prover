# Fused certificate benchmark results

These numbers come from the certificate benchmark in this directory. Run it with
cargo bench and it prints the same fields to standard output. The machine is an
Apple Silicon host and the build uses the release profile. The proving time is the
mean of three proofs, the verification time the mean of twenty.

## What the certificate proves

One flat trace carries two bands. The hashing band is a SHAKE256 sponge that
squeezes one word per segment, the matrix expansion of the verify relation. The
arithmetic band reduces each squeeze word into a coefficient below the signature
modulus and runs the commitment decomposition and the hint recovery over it, the
per coefficient certificate. A single proof covers the hashing and the arithmetic
together.

The bands cannot be split. On each squeeze row a gated equality pins the reduction
input to the sponge squeeze word, so the coefficient the arithmetic consumes is the
word the hash produced, and the permutation argument binds that reduced coefficient
to both the decomposition and the hint recovery. A prover cannot feed the
arithmetic a coefficient the hash did not produce.

## Parameters

The batch is sixteen hash derived coefficients, one squeeze word per SHAKE256
segment. The trace is 512 rows over 2241 base columns. The low degree extension
blows up by thirty two, which the degree eleven sponge transition needs, and the
schedule samples thirty two query positions.

## Measured timings

Proving time per certificate is about 29 seconds.

Verification time per certificate is about 73 milliseconds.

The serialized proof is about 2641648 bytes.

The certificate is accepted by the verifier over the same parameters. A proof
against a different squeeze output is rejected, a split coefficient breaks the
permutation binding, and a tampered reduction breaks the reduction relation.

## What still stands apart

- The batch is sixteen hash derived coefficients. Scaling to the full per
  signature coefficient count widens the arithmetic band but keeps the shape and
  the binding.
- The modular multiplication and the response norm bands consume the transform
  outputs and the response, which are not products of this hash. They join the
  arithmetic certificate in the batch module without a hash binding, since their
  inputs come from the transform and the signature rather than this expansion.
- The squeeze word reduces modulo the modulus here, a representative map from the
  hash output into the field. The faithful rejection sampling of the matrix
  expansion, RejNTTPoly, is arithmetized in the sample module with its own proof
  and reject tests, and binds to the arithmetic the same way.

## Sampling coverage

The remaining sampling steps of the verify relation are arithmetized with their own
proofs and reject tests, ready to bind into the certificate the same way:

- Matrix rejection sampling below the modulus, the sample module.
- Challenge ball position sampling into the sparse challenge, the challenge_ball
  module.
- The multi block absorb of the full challenge input, the sponge module.
- The commitment high bit packing and the seed index bytes, the encode module.
