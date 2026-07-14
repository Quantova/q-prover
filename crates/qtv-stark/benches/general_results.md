# General proof benchmark results

These numbers come from the general benchmark in this directory. Run it with
cargo bench and it prints the same fields to standard output. The machine is an
Apple Silicon host and the build uses the release profile.

## Worked example

The proof runs over the squaring chain worked example. The trace holds a single
column of 4096 rows over the Goldilocks prime. Each row squares the running
value from the row before, and the first and last values are pinned as public
boundaries. The low degree extension blows the trace up by eight, so the
composition is tested over 32768 points, and the query count is 32.

## Measured timings

Proving time per proof is about 187 milliseconds.

Verification time per proof is about 7 milliseconds.

The serialized proof is about 318176 bytes.

The correct trace is accepted, and the constraint tests in the stark module show
that a trace which breaks a transition or a boundary is rejected, as is a proof
whose openings or roots are tampered with. Verification stays far below proving,
which is the asymmetry the consensus certificate needs.
