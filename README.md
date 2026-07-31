# Doing Math in Public

A long-lived workspace for serious mathematical research carried out with computational tools, formal proof assistants, and adversarial audit.

This repository is organized by project. Each project should be readable on its own and should distinguish clearly among:

- proved mathematics;
- kernel-checked formalization;
- externally certified computation;
- numerical evidence;
- open obligations and failed approaches.

Nothing in this repository should be described as a theorem merely because a related program ran or a nearby Lean module compiled.

## Projects

| Project | Status | Directory |
|---|---|---|
| Regular-octagon honeycomb problem | Active research program; crystalline theorem and substantial noncrystalline components | [`projects/octagonal-honeycomb`](projects/octagonal-honeycomb) |

## Repository layout

```text
projects/<project>/
  README.md          # problem statement, status, and navigation
  STATUS.md          # exact proof boundary and current obligations
  lean/              # formal sources and pinned toolchain
  interval/          # certified-computation sources and manifests
  scripts/           # generators, audit scripts, and exploratory checks
  docs/              # papers, notes, diagrams, and audits
  evidence/          # reproducibility records; usually hashes and small logs
  archive/           # superseded approaches retained for audit
```

Shared repository material belongs under [`meta`](meta). Future projects should be added as siblings under `projects/`, rather than mixed into an existing proof tree.

## Branch policy

The canonical, legible research record belongs on the trunk branch. Work-in-progress proof development may use branches named `proof/<project>/<topic>` and should be integrated only after its status and trust boundary are documented.

The repository was created by GitHub with `main` as its default branch. A matching `master` branch is maintained for the requested canonical-trunk naming; the owner may switch the repository default to `master` in GitHub settings.

## CI policy

Workflows are project-specific and quiet by design. Expensive proof and interval jobs should use manual dispatch by default. Automated runs, when useful, should be restricted by path filters and concurrency cancellation so one edit does not generate a storm of redundant notifications.

## Provenance

The initial octagonal-honeycomb material was consolidated from earlier scratch work in `rabsef-talwet`, temporary CI branches in `cgol`, and retained local proof/audit artifacts. The migration preserves source provenance and failed approaches rather than presenting a cleaned history as if it were the original development record.
