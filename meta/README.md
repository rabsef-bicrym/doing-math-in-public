# Repository conventions

Each mathematical project lives under `projects/<slug>` and owns its formal sources, computational certificates, notes, and audit record.

## Status vocabulary

- **Proved:** a complete mathematical argument is presently known.
- **Kernel-checked:** a stated formal theorem has compiled without proof holes under the pinned toolchain.
- **Externally certified:** a finite computation was checked by a specified external verifier; the verifier's soundness is part of the trust boundary.
- **Numerically supported:** computation suggests the claim but does not certify it.
- **Open:** a required implication or interface is not yet established.
- **Superseded:** retained for audit but not used by the current proof graph.

## Branches

Use `proof/<project>/<topic>` for active proof development and `experiment/<project>/<topic>` for numerical or exploratory work. Canonical snapshots belong on `master`.
