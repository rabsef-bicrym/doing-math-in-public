# Regular-octagon honeycomb problem

This project investigates the minimum average perimeter of unit-area convex tilings of the plane when perimeter is measured by the norm whose unit ball is a regular octagon.

The candidate optimum is the centrally symmetric hexagonal tiling with benchmark

\[
2\sqrt{4\sqrt2-2}.
\]

## Current status

The project contains a substantial crystalline-direction proof program and a noncrystalline extension program. Several analytic, combinatorial, and certified-computation components are machine checked. The unrestricted conjecture is **not currently represented here as a completed theorem**; see [`STATUS.md`](STATUS.md) for the exact boundary.

## Navigation

- [`STATUS.md`](STATUS.md): authoritative proof-state ledger.
- [`lean/canonical`](lean/canonical): integrated formalization originating in `rabsef-talwet`.
- [`lean/standalone`](lean/standalone): dependency-isolated analytic and ledger modules developed on temporary public CI branches.
- [`interval`](interval): Boost directed-rounding verifier, independent MPFR replay, and Lean certificate generator.
- [`docs`](docs): papers, research notes, diagrams, and audit reports.
- [`archive`](archive): provenance and superseded approaches.
- [`evidence`](evidence): hashes, compact build evidence, and instructions for regenerating larger artifacts.

## Reproducibility principle

Generated certificates and logs are useful evidence, but the source and the exact trust boundary are primary. Large CI artifacts should normally be regenerated rather than accumulated indefinitely in Git history.
