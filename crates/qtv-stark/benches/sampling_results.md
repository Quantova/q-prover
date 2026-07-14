# Sampling arithmetization benchmark results

These numbers come from the sampling benchmark in this directory. Run it with cargo
bench and it prints the same fields to standard output. The machine is an Apple
Silicon host and the build uses the release profile. Each proving time is the mean
of five proofs, each verification time the mean of fifty. The blow up is eight and
the schedule samples thirty two query positions.

## What the samplers prove

These are the sampling steps that turn the hash streams of the verify relation into
its structured values, each arithmetized on its own trace and validated against the
crypto crate.

- Matrix rejection sampling, RejNTTPoly. Each row reads one three byte candidate,
  recomposes the twenty three bit integer, and carries an accept bit that a range
  witness pins to the comparison below the modulus. The accepted candidates in
  order are the ring the matrix expansion produces.
- Challenge ball position sampling, SampleInBall. Each row consumes one stream
  byte, compares it to the running target, and either accepts it as a placement and
  advances the target or rejects it, with the accept count forced to tau by the
  endpoint.
- Commitment high bit packing, w1Encode. Each row folds two four bit high parts
  into one byte, range checked to a nibble each, the encoding that feeds the
  challenge hash.

The multi block absorb of the full challenge input is the fourth sampling step. It
is arithmetized in the sponge module and measured next to the squeeze there.

## Measured timings

Matrix rejection sampling, 512 rows over 78 columns. Proving about 102
milliseconds, verification about 3.4 milliseconds, proof about 296608 bytes.

Challenge ball position sampling, 64 rows over 23 columns. Proving about 5
milliseconds, verification about 2.3 milliseconds, proof about 162384 bytes.

Commitment high bit packing, 128 rows over 11 columns. Proving about 5
milliseconds, verification about 2.3 milliseconds, proof about 170592 bytes.

Each proof is accepted by the verifier over the same parameters, and every module
carries a test that a wrong witness is rejected.
