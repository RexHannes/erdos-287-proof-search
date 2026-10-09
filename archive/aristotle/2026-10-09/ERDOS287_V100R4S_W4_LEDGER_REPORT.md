# Erdős #287 — V100R4S §§6–7: W₄ ratio ledger and conditional kernel chain

**Verdict: the exponent bookkeeping of V100R4S §§6.1–7 checks out and is now proved in Lean, but only conditionally. Erdős #287 is still open. `Tail287Statement` is not proved.**

The source is `PROOFS/actual_atom_proof_FCHS.md` (V100R4S), together with the landing guide `GUIDANCE/V100R4S_EXACT_SOURCE_LANDING.md`, both embedded in `05_ERDOS287_PROOFS_AUDIT_PROMPT_REVISED.md`.

## New files

All three files are in `RequestProject/Erdos287/SourceChain/`.

| File | Contents |
|---|---|
| `W4RatioLedger.lean` | `V100Range` (hypotheses (1.1)–(1.3), `Q ≤ N`, `N,Q,R,S ≥ 1`, `x > 1`) and the ratio lemmas (6.3), §6.2 and (6.6a–d) |
| `W4SourceBound.lean` | The three narrow W₄ right-hand sides evaluated at the source scales, and the uniform W₄ bound in the shape of (6.8) |
| `V100Kernel71.lean` | (4.9) + (6.8) ⟹ (7.1) ⟹ (1.8) ⟹ (1.9), plus the end-to-end conditional chain |

`SourceChain.lean` and `SourceChain/RepairAudit.lean` now import these files, and `RepairAudit.lean` prints the axioms of the new theorems. No existing declaration was changed or renamed.

**Checks:**
- `lake build RequestProject.Erdos287.SourceChain RequestProject.Erdos287.SourceChain.RepairAudit` succeeds.
- The new files contain no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` or `implemented_by`.
- Every new theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Per-equation table

Status key:
- **kernel-proved**: proved in Lean with no analytic hypothesis.
- **conditional**: proved in Lean, but the analytic input is an explicit hypothesis.
- **author-derived, unreviewed**: taken from the supplied proof, not checked here.

| V100R4S | Lean theorem (all hypotheses are in the signature) | Status |
|---|---|---|
| (6.3) diagonal ratio: `N²R²S/x ≤ x^{-8ε}` | `diag_ratio` | kernel-proved from (1.1) |
| §6.2 Ramanujan ratio: `N²QR³S³/x² ≤ x^{-64ε/3}` | `ram_ratio` | kernel-proved from (1.1), (1.3) and `Q ≤ N` |
| (6.6a) `NRS²/x ≤ x^{-40ε/3}` | `ratio_6_6a` | kernel-proved |
| (6.6b) `≤ x^{-25ε/2}` | `ratio_6_6b` | kernel-proved from (1.2) |
| (6.6c) `≤ x^{-16ε}` | `ratio_6_6c` | kernel-proved from (1.3) and `Q ≤ N` |
| (6.6d) `≤ x^{-25ε/2}` | `ratio_6_6d` | kernel-proved from (1.3) |
| Landing §3: `H₀/S ≤ x^{-8ε}` | `H0_div_S_ratio` | kernel-proved |
| §6.3 `H`-scaling (`H ≤ ΛH₀` costs at most `Λ^{3/2}`) | `bracket_H_le`, `pascadiInner_H_scale` | kernel-proved |
| (6.5) evaluated at the source scales | `spec_mono_1` … `spec_mono_6`, `spec_source_bound` | algebra kernel-proved; (6.5) itself is the hypothesis `W4SpecEstimate` |
| (6.2) and (6.4) evaluated at the source scales | `diag_source_bound`, `ram_source_bound` | algebra kernel-proved; the estimates themselves are the hypotheses `W4DiagEstimate` and `W4RamEstimate` |
| (6.8) `𝒲₄ ≪ Λ² T^{7/64} N²R²S³ x^{-6ε}` | `W4_uniform_bound`, `W4_uniform_bound_6eps` | conditional on the three narrow estimates and the split `𝒲₄ ≤ W_d+W_r+W_s` |
| (7.1) `f^{199/128}` budget | `kernel_7_1` | conditional on (4.9) and (6.8) |
| (1.8) | `kernel_1_8` | conditional on (4.9) and (6.8), with `Λ_c ≤ x^{ε/4}` and `ρ₀ ≤ ε/100` |
| (1.9) | `kernel_1_9`, `kernel_1_9_of_narrow` | conditional on (4.9) and the three narrow W₄ estimates |
| (4.9) first Cauchy / colour restoration | hypothesis `h49` | author-derived, unreviewed; not formalized |
| (6.2), (6.4), (6.5) narrow W₄ estimates (Pascadi Lemma 4.1/4.2-type) | `W4DiagEstimate`, `W4RamEstimate`, `W4SpecEstimate` | **missing**: these are the first specific unproved analytic inequalities |
| §8 degenerate cells (`H₀ < 1`, `S`, `R` or `Q` bounded) | — | not addressed |

## Findings

1. **No counterexample in §6.** Every saving claimed in (6.3), §6.2 and (6.7) holds exactly as stated under (1.1)–(1.3) and `Q ≤ N`. The four ratios (6.6a–d) are exactly what you get by expanding (6.5) at `F = N/Q`, `C = NRS`, `B₀ = NR`, `H = H₀`. For (6.6b), this includes relaxing the factor `Q^{-3θ/2}`.
2. **The corrected FCHS term is retained.** I did not replace `FCHS` by `FHS`, and I did not assume `H ≤ S` separately. The FCHS term gives two extra monomials, `spec_mono_3` and `spec_mono_6`. Both are bounded directly by `c³N²R²S³x^{-8ε}`, so the term does not change the final exponent.
3. **Constants.** The source scales may carry a fixed constant `c ≥ 1` (`F ≤ cN/Q`, `C ≤ cNRS`, `B₀ ≤ cNR`). The W₄ constant is then `8c³`, and the kernel constant is `D·A^{1+7/128}·√(8c³)·C_A`.
4. **Hypotheses the source states that Lean does not need.** Only `N ≥ 1` is used, not `N ≥ x^ε`. Likewise `H ≥ 1` and `H ≤ S` are not used. In the source, however, the narrow estimate (6.5) is only claimed for `H ≥ 1`, `H ≤ S`, so the cells with small `H` still need §8.

## First specific unproved analytic inequality

The first open item is **V100R4S (6.5)**, i.e. `W4SpecEstimate Ws Λ_p T F C B₀ S H` with the corrected `FCHS` term. It is meant to come from Pascadi Lemma 4.1 with `T` kept explicit, using Propositions 3.4 and 3.8 (arXiv:2505.00653v2).

Two more analytic inputs are open alongside it:
- the diagonal estimate (6.2) and the Ramanujan estimate (6.4);
- the source-to-W₄ inequality (4.9), including the colour restoration (2.4).

Everything downstream of these, up to (1.9), is now proved in Lean.
