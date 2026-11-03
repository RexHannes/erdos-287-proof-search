# Overnight cloud formalisation task: Erdős #287 Gold 4.1 local frontier

User requested two separate online proof-writing runs for #287 and Real 1B. This file is the concrete task for this repository only.

Read `REQUEST.md` and `INPUT_INVENTORY.md` completely. Preserve the pinned bank; do not restart it or confuse reported manuscript proofs with kernel-checked source.

## Priority order

1. Inventory the existing bank and record baseline `lake build` / relevant axiom results.
2. Define the literal finite selected set, sum of reciprocals, maximum, Boolean indicators and a precise Gap-two property.
3. Prove upper-half prime exclusion and correct internal forced-neighbor statements, including all min/max endpoint assumptions.
4. Attempt the four-value retained-cofactor and cleaning algebra only with exact source hypotheses and legitimate rational congruences. Mark missing manuscript conditions as NOT FORMALIZED, never as proved.
5. If possible, expose a faithful conditional Chen alternative with named analytic hypotheses. Keep prime supply, upper-sieve inputs and retained-residue compatibility open until actually proved.

## Implementation and checking

Create new completed Lean modules under `RequestProject/Erdos287/Gold41/`, with matching namespaces. Do not change old theorem statements or dependency versions. Keep all original statement / hypothesis comparisons in this task directory.

1. If necessary, `bash automation/lean-cloud/setup.sh` installs the existing pinned environment; no external AI API credentials are needed.
2. Run and record the historical baseline `lake build` result. Distinguish unrelated old failures from newly written mathematics.
3. Write actual definitions, lemmas and Lean proofs, fix errors, and continue until the highest-priority fully specified results are proved or a precise mathematical/input obstruction is established. Do not stop at an implementation plan.
4. Run `python3 automation/lean-cloud/audit_new.py` on every new module. It must return success and a nonempty theorem audit. Also include `#print axioms` for principal theorem names. Do not weaken or bypass the gate.
5. Record full actual theorem types and compare every domain, quantifier, hypothesis and conclusion with the original brief. Do not assume the desired conclusion as a hypothesis or advertise a generic tautological implication as the requested source theorem.
6. Copy useful build and axiom logs from `.lake/frontier-verification/` into this task's `results/` directory. Include final source and an `OPEN_FRONTIER.md` classifying each principal claim as KERNEL PROVED, CONDITIONAL ON NAMED HYPOTHESES, NOT FORMALIZED, or FALSE / REQUIRES REPAIR.
7. Keep unresolved code in Markdown. Do not add sorry/admit/custom axioms, native_decide, implemented_by, opaque oracles, or fabricated analytic providers.

## Completion

Produce a draft pull request containing actual checked source, logs, and the precise frontier ledger. Keep the overall research problem OPEN unless a complete unconditional proof was actually established and checked. Do not merge your PR or modify historical status claims. Work within the hosted task's time/usage limits; checkpoint useful completed results rather than idling or scheduling recurring jobs. Missing manuscripts must be reported, but should not block independent rigorous finite work.

## Autonomous continuation (user update, 4 November 2026)

Follow `AUTONOMOUS_FORMALISATION.md`. Plan and discover intermediate lemmas autonomously, search the existing bank/Mathlib, repair proofs from actual compiler diagnostics, and continue through independent valid results. Initial priority lists are guidance rather than an exhaustive lemma specification. Preserve the exact original target; separately record and justify repaired statements rather than silently weakening it. Maintain the dependency plan, proof/repair checkpoints and open-frontier ledger.

A pinned MerLean Heavy package can be prepared with `python3 automation/lean-cloud/prepare_merlean.py`; read and adapt its Heavy workflow to the actual host. Preparation is not model execution, plugin registration or proof certification. OpenProof and Lean-Prover are reviewed optional harnesses in `automation/lean-cloud/agents.lock.json`; Lean-Prover's 4.33 pin must not replace this bank's 4.28 pin.

The user authorized direct OpenAI API use if MerLean needs it. It requires a securely configured genuine API key; do not copy ChatGPT OAuth credentials or expose keys to unrelated code. Keep the existing host as the default. OpenRouter remains free-only, with explicit `:free` models and no paid or automatic fallback.
