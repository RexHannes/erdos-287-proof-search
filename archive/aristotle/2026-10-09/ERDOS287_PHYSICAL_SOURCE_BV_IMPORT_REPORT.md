# Erdős #287 — physical source, BV/SW import and one-sided seven-block layer

**Erdős #287 remains open. `Tail287` is not proved unconditionally.** Everything below is
append-only. Existing modules are unchanged, apart from new import lines in the aggregator
`RequestProject/Erdos287/SourceChain.lean`.

## 1. Files

| File | Content |
|---|---|
| `RequestProject/Erdos287/SourceChain/OAIImport/Defs.lean` | Verbatim transcription of the external `SiegelWalfisz` and `BombieriVinogradov` statements (`openai/math`, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`) |
| `RequestProject/Erdos287/SourceChain/OAIImport/Dictionary.lean` | Exact dictionary to `progSum`/`progErr`; project-form maximal BV; tiny-modulus SW; AP-form SW for `q ≤ (log x)^B` |
| `RequestProject/Erdos287/SourceChain/OAIImport/BVTransfer.lean` | **`ordinaryBVProvider_of_OAI`**: external ψ-endpoint BV ⟹ prime-counting `OrdinaryBVProvider` |
| `RequestProject/Erdos287/SourceChain/OneSidedSevenBlock.lean` | One-sided seven-block consumer, revised framework, revised tail boundary |
| `RequestProject/Erdos287/SourceChain/OneSidedTail.lean` | `Tail287_of_MinimalAnalyticProviders_oneSided` (conditional) |
| `RequestProject/Erdos287/SourceChain/AxiomAuditPhysical.lean` | Build-time axiom audit (577 source-chain theorems, standard axioms only) |
| `external/oai_primegaps_crosscheck/` | Native-environment harness (`run.sh`), the generated cross-check file and its outputs |

## 2. External BV/SW audit (Priority 2)

* **Pinned versions:** repository commit `adc7f124…`, toolchain `leanprover/lean4:v4.34.1`,
  Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. This project uses Lean/Mathlib
  `v4.28.0`, so the external `.olean` files cannot be imported. The statements are
  transcribed instead. The only textual change is `NNReal.mk a h` → `⟨a, h⟩`.
* **Native build:** the external `PrimeGaps` subtree (only Mathlib dependencies, about 22.5k
  lines) built successfully. It contains no `sorry`, `axiom`, `native_decide`,
  `implemented_by` or `unsafe` tokens. `leanchecker OAI.NumberTheory.PrimeGaps.Main` exited
  with code 0.
* **Type audit:** in the native environment, `crosscheck_SW : OAISiegelWalfisz ↔
  OAI.LargePrimeGaps.SiegelWalfisz := Iff.rfl` and the matching BV statement both compile.
* **Axioms:** `OAI.LargePrimeGaps.siegelWalfisz` and `OAI.LargePrimeGaps.bombieriVinogradov`
  depend only on `[propext, Classical.choice, Quot.sound]` (`crosscheck_output.txt`).
* **Content differences (recorded, not assumed away):**
  * The external SW is the primitive-character form.
  * The external BV is the *endpoint* form (no inner `max_{y ≤ x}`), with ψ weights, main term
    `x/φ(q)` and an eventual threshold `x ≥ x₀`.
  * The project's `OrdinaryBVProvider` uses prime counts, main term `π(x)/φ(Q)` and all
    `x ≥ 2`. **The missing implication is proved** (`ordinaryBVProvider_of_OAI`).
* **Not covered:**
  * The external results are ordinary BV/SW for `Λ`. They are not divisor-weighted BDH and not
    beyond-half distribution.
  * `BaseSWProvider` concerns the physical source sequences `α_j`, which are not defined (see
    §4). `apSW_of_OAIBV` supplies exactly the `α = Λ` case.

## 3. One-sided seven-block layer

* `one_sided_moment_ineq`: `𝔼P ≥ μ−δ`, `𝔼Q ≤ ν+δ`, `1+δ ≤ μ` and
  `4ν+4δ < (μ−δ)²−2(μ−δ)` together give `2(𝔼P+2𝔼Q) < (𝔼P)²`.
* The frozen `μ = 999999`, `ν = 1700001700000/7` satisfy the margin with `δ = 1`.
* `OneSidedSevenBlockDictionary` (first-moment lower bound, pair-moment upper bound, model
  errors `e₁, e₂`). `oneSided_of_twoSided` shows the old dictionary implies it.
* `tail_of_remainder_littleO_oneSided`: revised framework with `e₁, e₂ → 0`, plus
  `R_Σ^P = o(𝒩_X I)`, gives `Tail287Statement`.
* The actual values `μ_lower`, `ν_upper` and the `S₀` normalisation come from the manuscript,
  which I could not read. The generic theorem is stated for arbitrary constants satisfying the
  margin.

## 4. Physical source (Priority 1, 3, 4): blocked on unreadable source

The physical specification was sent as a reply of about 58,000 characters, but only its first
~2,500 characters could be read (up to "…revised seven-block tail framework using the corrected
dic…"). No specification file, V97/V99/V100R2/V100R4/actual-atom/upstream-audit report or
`manuscript.pdf` exists in the repository. Following the instruction not to substitute
arbitrary sequences, nothing physical was invented. Each missing formula, and the first
theorem it blocks:

| Missing formula | First blocked object |
|---|---|
| Pair-packet index `Ξ`, `Γ_ξ`, `f_ξ`, `c_ξ`, `b_{ξ,d}` | `physicalTailSource : TailSourceFamily` (fields `Xi, Γ, f, c, b, compat`) |
| Coefficient sequence `α_n` from the Heath–Brown decomposition | `TensorSource.α`, and hence `BaseSWProvider` from `apSW_of_OAIBV` |
| Low-sieve weights `λ_low^±` (construction, levels, supports) | `TensorSource.D`, `lX`, and `UpperSieveWellFactorable` |
| Type-II coefficients `c_{ξ,l,r}` | `physicalOrderingBCells` (`FABData`), `OrderingBPoissonReduction` |
| Smooth Poisson profile `Ψ` | Poisson step of `OrderingBPoissonReduction` |
| High-prime box indexing/ownership | identification of the scalar weight (`ScalarWeight`) with the source |
| `μ_lower`, `ν_upper`, `S₀`-normalised Maynard weights | construction of `OneSidedSevenBlockTailFramework` |

**Inspected declarations** (`ResearchBankV14/EdgeOnlyCompilerInterface.lean`):

* `prescribedShape_gcdClique` gives, for any box shape and any `T₀`, shifts `b` in the
  prescribed boxes and arbitrarily large `A` with `gcd(A+b_u, A+b_v) = |b_u−b_v|` for **all**
  pairs `u ≠ v`.
* `edgeOnly_compiler` is its direct restriction to the adjacent pairs of an arbitrary graph.
* Neither mentions weights, moments or `R_Σ^P`, so neither supplies the seven-block framework
  by itself.

## 5. Answers

1. **Concrete objects constructed:**
   * the transcribed external statements and their exact project-notation dictionary;
   * a proved adapter from the external BV statement to the project's `OrdinaryBVProvider`;
   * the one-sided seven-block consumer and the revised framework/tail boundary.

   The physical source, cells, scale and seven-block framework were **not** constructed (§4).
2. **Providers removed:**
   * `OrdinaryBVProvider` (Research Bank V15) now follows from the externally proved,
     audited BV statement.
   * In the source chain, the two-sided `SevenBlockMainTermDictionary` requirement is replaced
     by the weaker one-sided requirement.
   * No argument of `Tail287_of_MinimalAnalyticProviders` disappears, because they all
     concern the undefined physical source.
3. **External import audit:** passed (type `Iff.rfl`, standard axioms, `leanchecker` exit 0),
   with the version caveat in §2.
4. **First remaining blocker:** the definition of the physical pair-packet source (`Ξ`,
   `Γ_ξ`, `f_ξ`, `c_ξ`, `b_{ξ,d}`, `α_n`), needed for `physicalTailSource`.
5. **Zero-hypothesis `Tail287`:** no. The conditional theorems are preserved, and no
   unconditional theorem was produced.

## 6. Checks

* `lake build RequestProject.Erdos287.SourceChain` succeeds. The new files contain no
  `sorry`, and `#sc_assert_all_std_axioms` reports all 577 theorems use standard axioms only.
* `leanchecker` exits with code 0 on each new module.
* All six source-chain negative controls were re-run and each was rejected as expected:
  * sorry → `sorryAx` detected;
  * `native_decide` → `Lean.ofReduceBool` detected;
  * the four DAG/ledger controls each fail.
