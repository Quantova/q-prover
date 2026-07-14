# Full transform benchmark results

These numbers come from the ntt benchmark in this directory. Run it with cargo
bench and it prints the same fields to standard output. The machine is an Apple
Silicon host and the build uses the release profile.

## What the transform proves

The transform is a radix two decimation in time number theoretic transform over
the ring Z_q, where q is the signature modulus 8380417. The ring degree is 256,
so the transform has eight layers of 128 butterflies each, 1024 butterflies in
all, one per trace row. Each butterfly reads two inputs and a twiddle, forms the
twiddle product with a modular reduction over the signature modulus, and forms
the add output and the subtract output with their own modular reductions. Every
residue is forced into the canonical range zero to the modulus minus one by a
two sided bit expansion, the same range check the modular multiplication core
uses.

The wiring between the eight layers is carried by the permutation argument. Each
produced output and each consumed input is tagged with a wire identity that
encodes its layer and index. A running product column proves that the multiset
of internal produced cells equals the multiset of internal consumed cells under
two transcript challenges, one that folds a value with its identity and one that
runs the product. A value written at a layer index is therefore exactly the value
the downstream butterfly reads at the same layer index, though the two rows sit
far apart in the trace. The layer zero inputs and the layer eight outputs are the
public endpoints, pinned by boundaries, and a rotating one hot selector marks the
first and last layers so those endpoint cells are held out of the permutation.

The trace is 159 base columns wide with one auxiliary running product column.

## Measured timings

Proving time per proof is about 0.96 seconds.

Verification time per proof is about 8.5 milliseconds.

The serialized proof is about 470736 bytes.

The correct transform is accepted. The ntt tests show that the schedule matches a
direct discrete transform over the signature modulus, that a broken butterfly is
rejected, and that swapping two internal outputs, which keeps the local
arithmetic and the within row multiset but breaks the per identity wiring, is
rejected by the permutation argument.

## Scope reached

This proves a full transform end to end, the layer arithmetic and the inter
layer wiring together. It is the cyclic radix two form over the signature
modulus. The signature uses the negacyclic variant with a fixed twiddle schedule
built from a primitive five hundred and twelfth root of unity, which is the same
butterfly arithmetic under a different constant schedule, so the cost carries
over.
