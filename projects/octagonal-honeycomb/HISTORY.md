# Research history

This file records the development path so later readers can distinguish the current argument from discarded versions.

## Crystalline-direction program

The project began by restricting all edge directions to the eight directions selected by the regular-octagon norm. The key ingredients were an elementary RR-edge inequality, an HH-edge lower profile, a quantitative pair gap, and a finite selected-edge discharging argument. Large parts of this program were formalized in Lean.

## Arbitrary-direction extension

The unrestricted program introduced support-number matrices, a sharp conditioned-edge profile for an arbitrary fixed fan, phase-snapping area defects, and continuous charge banks. Numerical optimization suggested positive local margins.

## Important corrections

Several proposed lemmas were rejected during adversarial checking:

- an early continuous corner-credit formula double-counted charge near a perturbed pentagonal fan;
- an early interval implementation used endpoint minima without a sufficient monotonicity theorem;
- a generated Bernstein certificate contained a negative coefficient;
- an abstract finite ledger was at one point described too strongly, even though it assumed the geometric payment hypotheses it was meant to derive.

Corrected analytic sector bounds, endpoint monotonicity theorems, and a redesigned interval strategy were subsequently developed. The failed approaches remain archived or described in audit notes.

## Retraction of completeness language

A reconstructed bundle was previously labeled a “complete proof bundle.” That description was inaccurate. The bundle contained serious certified components, but not a complete unrestricted theorem. The repository now treats the unrestricted conjecture as open pending the explicit geometric-to-global interfaces listed in `STATUS.md` and `TRUST_BOUNDARY.md`.

## Migration

In 2026 the work was consolidated from private `rabsef-talwet` development, temporary public `cgol` CI branches, and retained local audit material into this dedicated project tree. Historical CI files are archived outside `.github/workflows` so they remain inspectable without generating notification storms.
