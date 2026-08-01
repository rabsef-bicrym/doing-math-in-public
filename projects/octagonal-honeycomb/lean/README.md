# Lean sources

`canonical/` is the integrated proof graph developed in the dedicated private proof repository. `standalone/` contains dependency-isolated analytic and combinatorial modules developed on temporary public CI branches.

The two trees are preserved separately during migration so provenance is clear. The next engineering task is to build a single clean project without hiding duplicate definitions or silently choosing one incompatible normalization.
