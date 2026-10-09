import Mathlib

/-!
# Erdős #287 — source chain: transcription of the external Siegel–Walfisz / Bombieri–Vinogradov
statements of `openai/math`

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

External source (pinned):

* repository `https://github.com/openai/math`, commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`;
* files `lean/OAI/NumberTheory/PrimeGaps/{CharacterErrors,OrthantIntegrals,MangoldtBounds,
  ConductorBounds,Main}.lean`;
* toolchain `leanprover/lean4:v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

This project is pinned to Lean `v4.28.0` / Mathlib `v4.28.0`, so the external modules
**cannot be imported** here (incompatible `.olean` format and Mathlib API).  The statements
are therefore transcribed *verbatim* below.  The transcription is certified in the native
environment by `external/oai_primegaps_crosscheck/CrossCheck.lean`, which compiles this very
text against the external development and proves each transcribed proposition `Iff.rfl`-equal
to the original.  The only textual change is that the external `NNReal.mk a h` (in v4.34.1
`NNReal` is a structure) is written as the anonymous constructor `⟨a, h⟩`, which elaborates to
the same term in both Mathlib versions (`OAI.LargePrimeGaps.SiegelWalfisz`, `OAI.LargePrimeGaps.BombieriVinogradov`).

The external theorems `OAI.LargePrimeGaps.siegelWalfisz : SiegelWalfisz` and
`OAI.LargePrimeGaps.bombieriVinogradov : BombieriVinogradov` therefore enter this project
only as **explicit hypotheses** of type `OAISiegelWalfisz` / `OAIBombieriVinogradov`; no axiom
is introduced.

Note on content (recorded, not assumed away):

* `OAISiegelWalfisz` is the *primitive-character* form, for conductors `d ≤ (log x)^B`;
* `OAIBombieriVinogradov` is the **endpoint** form: for each `x` it controls
  `∑_{q ≤ x^{1/2}(log x)^{-b}} max_{(c,q)=1} |ψ(x;q,c) - x/φ(q)|` at that single `x`
  (no inner `max_{y ≤ x}`), with von Mangoldt weights, the main term `x/φ(q)` and an
  eventual threshold `x ≥ x₀`.
-/

open scoped Classical

namespace Erdos287.SourceChain.OAIImport

/-- Transcription of `OAI.LargePrimeGaps.primeCharacterPrefix`:
`∑_{0 < n ≤ ⌊x⌋} χ(n) Λ(n)`. -/
noncomputable def primeCharacterPrefix (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)

/-- Transcription of `OAI.LargePrimeGaps.primeCharacterError`:
`ψ(x,χ) - [χ = 1] x`. -/
noncomputable def primeCharacterError (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  primeCharacterPrefix x χ-if χ=1 then (x:ℂ) else 0

/-- Transcription of `OAI.LargePrimeGaps.residueSlice`. -/
noncomputable def residueSlice (f : ℕ → ℝ) (L U q c : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc L U).filter (fun n => n % q = c), f n

/-- Transcription of `OAI.LargePrimeGaps.residuePrefix`: `∑_{0<n≤Y, n % q = c} f(n)`. -/
noncomputable def residuePrefix (f : ℕ → ℝ) (Y q c : ℕ) : ℝ :=
  residueSlice f 0 Y q c

/-- Transcription of `OAI.LargePrimeGaps.endpointError`:
`max_{c < q, (c,q)=1} |ψ(⌊x⌋; q, c) - x/φ(q)|`. -/
noncomputable def endpointError (x : ℝ) (q : ℕ) : NNReal :=
  (Finset.range q).sup fun c => if Nat.Coprime c q then
    ⟨|residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c - x/q.totient|,
      abs_nonneg _⟩ else 0

/-- Transcription of `OAI.LargePrimeGaps.SiegelWalfisz` (primitive-character form). -/
def OAISiegelWalfisz : Prop :=
  ∀ A B : ℝ, 0 < A → 0 < B → ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → ∀ d : ℕ, 0 < d → (d:ℝ) ≤ (Real.log x)^B →
      ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
        ‖primeCharacterError x χ‖ ≤ M*x*(Real.log x)^(-A)

/-- Transcription of `OAI.LargePrimeGaps.BombieriVinogradov` (endpoint, `ψ`-weighted form). -/
def OAIBombieriVinogradov : Prop :=
  ∀ A : ℝ, 0 < A → ∃ b : ℝ, 0 < b ∧ ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x →
      (∑ q ∈ Finset.Icc 1 ⌊x^(1/2:ℝ) * (Real.log x)^(-b)⌋₊,
        (endpointError x q : ℝ)) ≤ M*x*(Real.log x)^(-A)

end Erdos287.SourceChain.OAIImport
