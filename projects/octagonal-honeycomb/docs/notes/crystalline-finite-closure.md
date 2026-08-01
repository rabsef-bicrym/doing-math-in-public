# Finite closure of the crystalline octagonal honeycomb argument

> Historical research note. The machine-status lines below reflect the local environment in which this note was generated and are not the project’s current authoritative status. See `../../STATUS.md` and the migrated Lean sources.

## Machine status

- Pentagon RR witness and RR/RR collision core: **not recorded**
- Combined finite closure module: **not recorded**
- Push attempt: **not recorded**

The status words above were generated from the local Lean invocations available when this note was written.

## The finite closure theorem

Let `D` be the dangerous quadrilateral and pentagonal cells remaining after all
cells incident to higher-valence vertices or straight subdivisions have been paid
from their local positive charge. For each `C in D`, choose an `RR` edge `e(C)`.

Then:

1. A dangerous quadrilateral has four `R` corners. A dangerous pentagon has three
   `R` corners and two `H` corners; three marked vertices on a 5-cycle include an
   adjacent pair. Thus every dangerous cell has an `RR` edge.

2. The chosen physical edges are distinct. If the same edge were `RR` on both
   sides, then at either trivalent endpoint the turn units would be `2 + 2 + t = 4`,
   forcing `t = 0`, a straight incidence. Those cells were removed before this
   stage.

3. Across a chosen edge, the other cell sees an `HH` edge. At each trivalent
   endpoint, the dangerous cell contributes turn `2`; the other two positive
   crystalline turns sum to `2`, hence are both `1`.

4. A cell receives at most eight selected incidences. Every received selected
   edge is a genuine `HH` side, not a collinear subdivision. The positive exterior
   turns of a convex crystalline polygon are positive integer multiples of 45
   degrees and sum to eight units, so it has at most eight genuine sides.

5. For every selected edge, the pair-gap theorem gives

       epsilon(C) + epsilon(C') > 101/1000.

   Summing over the `N = |D|` distinct selected edges and using the multiplicity
   bound gives

       (101/1000) N < 8 sum_C epsilon(C),

   hence

       sum_C epsilon(C) > (101/8000) N = 0.012625 N.

6. Every dangerous-cell debt is below `0.009`; the numerical values are

       Delta_4 = 0.008442376...,
       Delta_5 = 0.003238129....

   Therefore

       Delta_4 N_4 + Delta_5 N_5 < 0.009 N
                                 < sum_C epsilon(C).

Thus all remaining negative structural charge is paid by metric deformation
excess. Together with the already-positive high-valence, straight-subdivision,
and non-dangerous cases, the finite toroidal crystalline inequality follows.

The remaining steps from this finite theorem to the stated infinite-plane
restricted theorem are the normal-tiling exhaustion estimates: boundary cells
are `O(R)` while interior cells are `Theta(R^2)`.
