# FRI low degree proof benchmark results

These numbers come from the backend benchmark in this directory. Run it with
cargo bench and it prints the same fields to standard output. The machine is an
Apple Silicon host and the build uses the release profile.

## Representative parameters

The evaluation domain holds 65536 field elements over the Goldilocks prime. The
degree bound is 8192, which fixes a blow up factor of 8. The schedule folds 13
times down to a constant final layer and samples 32 query positions.

## Measured timings

Proving time per proof is about 120 milliseconds.

Verification time per proof is about 3 milliseconds.

The serialized proof is about 273632 bytes.

Each proof is accepted by the verifier over the same parameters, and a vector
whose degree exceeds the bound is rejected. Verification stays near three
milliseconds and about forty times faster than proving, which is the asymmetry
the consensus design needs before it is frozen.
