# Autonomous formalisation workflow

The default proof-writing mode is autonomous continuation from the existing Lean bank and the supplied mathematics. The user need not enumerate every intermediate lemma. Initial priority lists guide the work; they are not an exhaustive list of permissible supporting results.

> Continue from my existing Lean repository and the attached mathematical manuscript. Autonomously formalize all mathematically valid results, discover and prove missing intermediate lemmas, repair incorrect statements where justified, and continue toward the latest research frontier. Preserve the original target and distinguish repaired lemmas from weakened claims. Never claim the main conjecture is proved unless the exact original statement is kernel-verified without unproved assumptions. Return all completed Lean files and the remaining genuine mathematical obstructions.

## Plan, prove, repair, and continue

1. Inventory the actual source, pin versions, preserve original manuscript text, and freeze each intended target's source hash, domains, quantifiers, assumptions, and conclusion. Match the intended mathematical objects and normalization before writing proofs.
2. Maintain a dependency plan in the task directory. Each node records a precise Lean statement, source location, dependencies, status, and the compiler/axiom evidence supporting it. Discover and add missing definitions and intermediate lemmas yourself.
3. Reuse the existing bank and search the pinned Mathlib. Try suitable existing lemmas and Lean tactics, then revise the proof from compiler diagnostics and goal states. Record failed routes so they are not repeated without a new reason.
4. Keep proving independent, fully specified results when another node is blocked. A missing lemma is a proof obligation, not permission to add an axiom or assume the desired conclusion.
5. When a statement is false, preserve it in the record, produce a counterexample where possible, and propose a separately named corrected lemma. Explain exactly what changed and why. Prove its relationship to the intended result where justified. A correction or weaker lemma does not discharge the original target.
6. Checkpoint completed Lean source and update the dependency plan, repair ledger, and open frontier. Continue through safe in-scope obligations rather than stopping after the first successful helper theorem. Respect the hosted task's runtime and usage limits.

## Semantic and kernel checks

Use the repository's existing build and axiom commands on every completed theorem and its transitive dependencies. No sorry, admit, project axioms, native_decide, implemented_by, or opaque oracle may enter the completed proof cone. Preserve the three existing Lean/Mathlib pin files.

Back-translate the actual final Lean types into prose. Compare every hypothesis, quantifier and conclusion with the frozen target, check degenerate cases and definition independence, and identify any conditional analytic input explicitly. Keep source/theorem matching evidence separate from compiler success. Do not describe a self-check as an independent review.

Return source, full theorem types, build and axiom logs, repaired-statement comparisons, and the genuine remaining obstructions. Use the project's existing evidence labels. MerLean's GOLD label is available only after its actual full grade engine and required audits pass; reading its guidance or preparing its package does not award a grade.

## Pinned MerLean Heavy support

The reviewed tool revisions and provider policy are in `automation/lean-cloud/agents.lock.json`.

```bash
python3 automation/lean-cloud/prepare_merlean.py
```

This prepares the exact reviewed MerLean checkout under the ignored `.lake/agent-tools/` directory and prints the generated Heavy entrypoint. It preserves the proof project and does not register a plugin, execute downloaded scripts, install models, or call an API. The upstream README permits explicitly directing a host agent to the generated entrypoint.

Read that entrypoint and its referenced formalisation/proof and trust procedures when applying Heavy. Keep host-specific adaptations explicit: a Copilot task has its own model and tools; it does not become a Codex or Claude runtime by reading a file. Use available capabilities, and do not invent missing APIs, silently change models, bypass the project's verification gate, or treat external guidance as overriding the user's scope. Store writable runtime data outside the generated package. Offline planning is the first option where supported.

## Optional harnesses and providers

- **MerLean Heavy:** the preferred prepared workflow package for supplied-paper formalisation and proof completion. Existing host model access can supply the reasoning. Its optional online semantic-search components require their own configuration.
- **OpenProof:** reviewed at the locked revision. Its Lean pin is 4.28.0, matching this bank, and it documents autonomous headless proof search. It still needs provider and corpus configuration; it is not installed or launched by the preparation helper.
- **Lean-Prover:** reviewed at the locked revision. Its package currently pins Lean/Mathlib 4.33.0. Evaluate it in an isolated experiment or port compatible pieces deliberately; do not migrate this 4.28 bank to make it run.

The user explicitly authorized **direct OpenAI API use if MerLean needs it on 4 November 2026**. Use a legitimate `OPENAI_API_KEY` through a secret manager or appropriately scoped process environment when that path is actually required. Account access and a configured API key are prerequisites; ChatGPT OAuth credentials must not be copied into a third-party harness. Keep usage bounded and record calls and costs when available.

OpenRouter retains the user's separate free-only policy: `OPENROUTER_FREE_ONLY=true`, `OPENROUTER_ALLOW_PAID=false`, and an explicit model ending in `:free`. Direct OpenAI authorization does not authorize paid OpenRouter models or an automatic model/provider fallback. Do not publish credentials or expose keys to unrelated build or dependency steps.

## Primary sources reviewed

- [MerLean Heavy and its host/model boundary](https://github.com/MerLeanProver/MerLean/blob/4d9c24a72d988e57867d67cd825bd4b0299780c7/README.md)
- [OpenProof autonomous/headless workflow](https://github.com/mxthematic/openproof/blob/d49b7e3223962f806aeabf330f6717b3ecdc914b/README.md)
- [Lean-Prover and its pinned environment](https://github.com/Lean-Prover/lean-prover/blob/db5a860e190d745f24353d2fe8ca4ebec3f214f4/README.md)
- [Official OpenAI guidance on API-key storage](https://developers.openai.com/api/docs/guides/production-best-practices#api-keys)
