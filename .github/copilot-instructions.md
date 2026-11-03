# Lean proof-writing instructions

Read `formalisation/overnight-2026-11-03/TASK.md`, `REQUEST.md` and `INPUT_INVENTORY.md` before the overnight task. These files distinguish supplied specifications from missing sources.

Preserve every existing theorem, import, and dependency pin. Inventory the real declarations; do not trust historical report labels as build evidence. Use the repository's pinned Lean/Mathlib, never `lake update` for setup. If tools are missing, run `bash automation/lean-cloud/setup.sh`; if the action has already prepared them, reuse the cache.

Retain the exact mathematical statement and all hypotheses. Complete actual Lean proofs and run their compiler; do not stop at a prose plan. No sorry, admit, custom axiom, native_decide, implemented_by, opaque oracle, fabricated theorem or assumed desired conclusion. Every new theorem must pass `python3 automation/lean-cloud/audit_new.py`. This imports all new frontier modules and rejects every transitive axiom outside propext, Classical.choice and Quot.sound. Do not weaken or edit the verification gate to obtain a pass.

Build the historical baseline with `lake build` and record its result separately. A missing manuscript, a genuinely open analytic estimate, a counterexample, or a legacy failure must be recorded precisely. Continue independent, fully specified local mathematics when possible. Keep unfinished attempts as Markdown rather than sorry-containing compiled modules. Conditional results must show all named hypotheses in their actual Lean types.

Deliver the work on the agent's task branch as a draft PR. Include source, original statements, compiler logs, principal theorem types and axiom output, and an OPEN_FRONTIER.md ledger. Do not merge the PR, publish a solution claim, or alter historical status documents. Do not introduce an external AI API or paid-provider fallback. Stop when the bounded task is complete or genuinely blocked; do not idle or repeatedly rebuild unchanged code to fill the night.
