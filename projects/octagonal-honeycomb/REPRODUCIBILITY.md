# Reproducibility

## Lean environments

Two source graphs are retained.

### Canonical integrated snapshot

```bash
cd projects/octagonal-honeycomb/lean/canonical
lake update
lake exe cache get
lake build Project --wfail
```

This directory is an exact source migration from `rabsef-talwet`. The command above is the intended integrated build, but the project status file—not the existence of a `Project.lean` file—determines which end-to-end claims are presently justified.

### Standalone analytic and ledger modules

```bash
cd projects/octagonal-honeycomb/lean/standalone
lake update
lake exe cache get
lake build --wfail
```

These modules were developed in dependency-isolated public CI. They include angular-sector inequalities, dangerous-fan classification, root-box reduction, and finite charge-ledger components.

Both environments pin Lean 4.30.0 and Mathlib 4.30.0.

## Interval calculation

The active source is under `interval/`.

```bash
cd projects/octagonal-honeycomb/interval
g++ -O3 -std=c++20 -frounding-math interval_verifier_emit.cpp -o interval_verifier_emit
g++ -O3 -std=c++20 mpfr_recheck_fullx.cpp -lmpfr -lgmp -o mpfr_recheck_fullx
./interval_verifier_emit fast_certificate.octv1
./mpfr_recheck_fullx fast_certificate.octv1 mpfr_certificate.octv2
python3 build_lean_certificate.py \
  --input mpfr_certificate.octv2 \
  --output ../lean/NoncrystallineIntervalCertificate.lean \
  --manifest noncrystalline_interval_manifest.json \
  --summary NONCRYSTALLINE_INTERVAL_CERTIFICATE.md
```

The Boost program performs the fast directed-rounding branch-and-bound calculation. The MPFR program independently replays accepted boxes at 192-bit precision. The generated Lean module checks the finite partition structure and exact positivity metadata. Lean does not internally prove the soundness of Boost or MPFR transcendental enclosures.

## Exploratory scripts

Scripts under `scripts/` include symbolic checks, numerical optimization, diagram generation, and certificate generation. Their output is evidence or development assistance unless a formal theorem explicitly imports it.

## Trust boundary

The present program relies on:

- the published polygonal isoperimetric input used to convert tangent-fan area to perimeter;
- Lean 4.30.0 and Mathlib 4.30.0 for kernel-checked modules;
- Boost directed rounding and MPFR for the external interval certificate;
- the still-open geometric adapters connecting arbitrary planar tilings to the finite fan and selected-edge models.

A complete unrestricted theorem requires those geometric adapters and the global summation interface to be stated and checked end to end.
