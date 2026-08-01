# Regular-octagon honeycomb problem

This project investigates the minimum average perimeter of unit-area convex tilings of the plane when perimeter is measured by the norm whose unit ball is a regular octagon.

The candidate optimum is the centrally symmetric hexagonal tiling with benchmark

\[
2\sqrt{4\sqrt2-2}.
\]

## Current status

The project contains a substantial crystalline-direction proof program and a noncrystalline extension program. Several analytic, combinatorial, formal, and certified-computation components are machine checked. The unrestricted conjecture is **not currently represented here as a completed theorem**.

Read [`STATUS.md`](STATUS.md) before drawing conclusions from individual filenames or old reports.

## Navigation

- [`STATUS.md`](STATUS.md): authoritative proof-state ledger and next obligations.
- [`TRUST_BOUNDARY.md`](TRUST_BOUNDARY.md): what Lean checks, what external computation checks, and what remains open.
- [`REPRODUCIBILITY.md`](REPRODUCIBILITY.md): clean-checkout commands and certificate workflow.
- [`HISTORY.md`](HISTORY.md): development history, failed approaches, and correction record.
- [`lean/canonical`](lean/canonical): integrated source snapshot originating in `rabsef-talwet`.
- [`lean/standalone`](lean/standalone): dependency-isolated analytic and ledger modules developed on temporary public CI branches.
- [`interval`](interval): active Boost directed-rounding verifier, independent MPFR replay, and Lean certificate generator.
- [`scripts`](scripts): symbolic checks, numerical exploration, figure generation, and source generators.
- [`docs`](docs): papers, research notes, diagrams, and audit reports.
- [`archive`](archive): superseded approaches, historical CI, and source provenance.
- [`evidence`](evidence): compact manifests, hashes, and selected status records.
- [`provenance`](provenance): source repositories, commits, and exported SHA-256 manifests.

## Reproducibility principle

Generated certificates and logs are useful evidence, but source code, exact statements, and the trust boundary are primary. Large CI artifacts should normally be regenerated rather than accumulated indefinitely in Git history.
