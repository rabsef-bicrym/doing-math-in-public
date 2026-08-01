# Certified local interval calculation

This directory contains:

- a Boost interval verifier using directed floating-point rounding;
- an independent 192-bit MPFR replay implementation;
- a generator that imports the finite partition tree and positive leaf numerators into Lean.

The intended trust boundary is explicit: Lean checks the finite certificate structure and integer positivity, while transcendental enclosure soundness remains external and is checked independently by two implementations plus analytic monotonicity lemmas.
