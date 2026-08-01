# Trust boundary and claim map

## What is formalized

The repository contains kernel-checked modules for substantial parts of the crystalline-direction argument, including the RR-edge algebra, pair-gap analysis, finite selected-edge counting, and several charge-allocation lemmas. It also contains kernel-checked analytic modules for arbitrary-direction phase sectors, wedge splitting, dangerous-turn classification, and root-box reduction.

## What is externally certified

A finite six-variable local inequality is checked over twelve owner/neighbor side-count domains by a directed-rounding Boost verifier and independently replayed with 192-bit MPFR arithmetic. The generated Lean import checks the certificate tree and exact positive leaf metadata.

## What is not internal to Lean

Lean does not verify the implementation of Boost, MPFR, the host compiler, or the transcendental interval algorithms. The published polygonal isoperimetric theorem is also an external mathematical input.

## What remains open

The unrestricted honeycomb conjecture is not presently represented by one theorem whose hypotheses are instantiated from an actual normal convex tiling. The principal open interfaces are:

1. construct the finite selected-edge and role data from a geometric tiling without inserting the desired conclusion as a hypothesis;
2. prove the exact bridge from each real shared-edge configuration to the interval evaluator's coordinates and lower-bound expression;
3. derive the multiplicity and collision-role bounds globally from the selected-edge construction;
4. combine the local certificate, collision theorem, positive-charge banks, Euler terms, and boundary terms in one finite theorem;
5. pass from the finite model to a normal tiling of the plane with an explicit exhaustion argument.

## Status rule

A module can compile and still serve only as a conditional adapter. Claims in `STATUS.md` take precedence over filenames, comments, old reports, and generated artifacts.
