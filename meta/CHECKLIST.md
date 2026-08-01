# Mathematical release checklist

Before a claim moves onto a canonical trunk, record each item explicitly.

## Statement

- State the theorem with every hypothesis and normalization.
- Separate the mathematical theorem from any stronger informal motivation.
- State equality cases only when they are actually proved.

## Proof boundary

- Identify published inputs and cite their exact statements.
- Identify formalized lemmas and the toolchain under which they compile.
- Identify externally certified computations and their verifier trust boundary.
- Identify numerical evidence that is not used as proof.
- List every open interface or modeling assumption.

## Reproducibility

- Pin tool and dependency versions.
- Provide one command or workflow for each formal or computational check.
- Preserve source hashes and generated-certificate hashes.
- Rebuild from a clean checkout before describing a target as green.
- Reject `sorry`, `admit`, `sorryAx`, and undeclared axioms where applicable.

## Adversarial audit

- Search for circular hypotheses equivalent to the conclusion.
- Check domain exhaustion and all boundary cases.
- Check that charge, measure, or probability is not spent twice.
- Reimplement critical computations independently when practical.
- Retain failed certificates and explain why they failed.

## Novelty

- Search the current literature and compare exact statements, not themes.
- Distinguish a new theorem from a new proof, formalization, or computation.
- Record nearby results that could subsume the claim.
- Do not announce novelty until an external specialist has had a fair chance to object.
