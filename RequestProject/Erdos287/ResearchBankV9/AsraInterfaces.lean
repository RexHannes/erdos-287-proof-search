import RequestProject.Erdos287.ResearchBankV9.AsraCRT
import RequestProject.Erdos287.ResearchBankV9.AsraPrimeSlot
import RequestProject.Erdos287.ResearchBankV9.AsraZeroMode
import RequestProject.Erdos287.ResearchBankV9.AsraClearing

/-!
# Erdős #287 — Research Bank V9 §4H–4I: open ASRA interfaces and the assembly theorem

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

**Epochs.**  The historical epoch "ASRA = FULL WRITTEN CANDIDATE / pending hostile referee" is
recorded as **HISTORICAL / SUPERSEDED (certification rollback)** in the ledger.  The current
corrected state is: ASRA partially repaired; full nonzero-frequency transfer **OPEN**; full
signed sieve-main-term evaluation **OPEN**; effective finite splice **BLOCKED**.

**Data.**  `ASRAData` packages, for one fixed pair configuration, the preserved arithmetic
structure (base modulus and residue, root-index set, extracted common factor, level `θ`,
coefficient norm) together with the real-valued pieces of the pair sum as functions of the scale
`X`: the main term, the small-overlap zero mode, the large-overlap tail and the nonzero
frequencies, and the target pair coefficient `κ`.

**Open interfaces (never inhabited here).**
* `ASRA_NonzeroFrequencyTransfer D` — the full root-coloured nonzero-frequency Type-I/II transfer
  for the data `D` (with its base progression, root index, common factor, level and norms), in
  the form `|nonzeroFreq X| = o(scale X)`;
* `ASRA_SignedSieveMainTerm D` — the complete signed upper-sieve main-term evaluation producing
  the pair coefficient `κ`: `mainPair X ≤ (κ + o(1)) scale X`.

Both are genuine hypotheses: `nonzeroFrequencyTransfer_not_automatic` and
`signedSieveMainTerm_not_automatic` exhibit data for which they fail.

**Assembly** (`asra_of_components`): CRT/collision/prime-slot decomposition identity +
large-overlap input + ratio-BV zero-mode input + the two open interfaces ⟹ `ASRA D`.
`pairCoefficient_below_gate_of_asra`: `ASRA D` + the explicitly supplied exponent inequality
`κ < 145/39` ⟹ the pair sum is eventually below the graph gate.  ASRA itself is never inhabited.
-/

namespace Erdos287
namespace ResearchBankV9
namespace AsraInterfaces

/-- The data of one ASRA pair configuration. -/
structure ASRAData where
  /-- Base modulus of the transformed progression (preserved). -/
  B : ℕ
  /-- Base residue (preserved). -/
  p₀ : ℤ
  /-- Root-colour index set (preserved). -/
  rootIndex : Finset ℕ
  /-- Extracted common factor (preserved). -/
  commonFactor : ℕ
  /-- The intended exponent level `θ`. -/
  θ : ℝ
  /-- The coefficient norm required by the transfer. -/
  coeffNorm : ℝ → ℝ
  /-- The main size scale (e.g. `X / (log X)²`). -/
  scale : ℝ → ℝ
  /-- The full pair sum. -/
  pairSum : ℝ → ℝ
  /-- The signed main term. -/
  mainPair : ℝ → ℝ
  /-- The small-overlap zero-mode contribution. -/
  zeroSmall : ℝ → ℝ
  /-- The large-overlap tail. -/
  largeTail : ℝ → ℝ
  /-- The nonzero-frequency contribution. -/
  nonzeroFreq : ℝ → ℝ
  /-- The target pair coefficient. -/
  κ : ℝ

/-- `f = o(scale)` eventually, in the elementary `ε`–`X₀` form. -/
def LittleO (f scale : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, ∀ X ≥ X₀, |f X| ≤ ε * scale X

/-- **OPEN interface: the full root-coloured nonzero-frequency transfer.**  Never inhabited. -/
structure ASRA_NonzeroFrequencyTransfer (D : ASRAData) : Prop where
  /-- The nonzero-frequency part is negligible relative to the main scale. -/
  transfer : LittleO D.nonzeroFreq D.scale

/-- **OPEN interface: the complete signed sieve main-term evaluation.**  Never inhabited. -/
structure ASRA_SignedSieveMainTerm (D : ASRAData) : Prop where
  /-- The signed main term produces the pair coefficient `κ`. -/
  mainTerm : ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, ∀ X ≥ X₀, D.mainPair X ≤ (D.κ + ε) * D.scale X

/-- **External interface: large-overlap input** (Shiu/divisor-moment consequence). -/
structure ExternalLargeOverlapInput (D : ASRAData) : Prop where
  /-- The large shared-gcd tail is negligible. -/
  tail : LittleO D.largeTail D.scale

/-- **External interface: ratio-form BV input** (Zheng-type consequence for the zero mode). -/
structure ExternalRatioBVInput (D : ASRAData) : Prop where
  /-- The small-overlap zero mode is negligible. -/
  zeroMode : LittleO D.zeroSmall D.scale

/-- The exact decomposition identity furnished by the CRT normalization, the collision zero and
the prime-slot truncation (finite algebra, §4A–4D). -/
def DecompositionIdentity (D : ASRAData) : Prop :=
  ∃ X₀ : ℝ, ∀ X ≥ X₀, D.pairSum X = D.mainPair X + D.zeroSmall X + D.largeTail X + D.nonzeroFreq X

/-- **ASRA** for the data `D`: the pair sum is at most `(κ + o(1)) scale`. -/
def ASRA (D : ASRAData) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, ∀ X ≥ X₀, D.pairSum X ≤ (D.κ + ε) * D.scale X

/-- **ASRA assembly theorem** (all analytic premises visible in the type). -/
theorem asra_of_components (D : ASRAData) (hdec : DecompositionIdentity D)
    (hLarge : ExternalLargeOverlapInput D) (hZero : ExternalRatioBVInput D)
    (hNF : ASRA_NonzeroFrequencyTransfer D) (hMT : ASRA_SignedSieveMainTerm D) : ASRA D := by
  intro ε hε
  obtain ⟨X₁, h₁⟩ := hdec
  obtain ⟨X₂, h₂⟩ := hLarge.tail (ε / 4) (by linarith)
  obtain ⟨X₃, h₃⟩ := hZero.zeroMode (ε / 4) (by linarith)
  obtain ⟨X₄, h₄⟩ := hNF.transfer (ε / 4) (by linarith)
  obtain ⟨X₅, h₅⟩ := hMT.mainTerm (ε / 4) (by linarith)
  refine ⟨max X₁ (max X₂ (max X₃ (max X₄ X₅))), fun X hX => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hX
  rw [h₁ X hX.1]
  have a := h₂ X hX.2.1
  have b := h₃ X hX.2.2.1
  have c := h₄ X hX.2.2.2.1
  have d := h₅ X hX.2.2.2.2
  have a' := le_abs_self (D.largeTail X)
  have b' := le_abs_self (D.zeroSmall X)
  have c' := le_abs_self (D.nonzeroFreq X)
  nlinarith

/-- **ASRA ⟹ pair coefficient below the graph gate**, *only* given the explicitly supplied
exponent inequality `κ < 145/39` and a positive scale. -/
theorem pairCoefficient_below_gate_of_asra (D : ASRAData) (hA : ASRA D)
    (hexp : D.κ < 145 / 39) (hscale : ∀ X, 0 < D.scale X) :
    ∃ X₀ : ℝ, ∀ X ≥ X₀, D.pairSum X < (145 / 39) * D.scale X := by
  obtain ⟨X₀, h⟩ := hA ((145 / 39 - D.κ) / 2) (by linarith)
  refine ⟨X₀, fun X hX => lt_of_le_of_lt (h X hX) ?_⟩
  have := hscale X
  nlinarith

/-! ## The open interfaces are genuine hypotheses -/

/-- Data for which every piece equals the scale `1`. -/
def trivialData : ASRAData :=
  ⟨1, 0, ∅, 1, 0, fun _ => 0, fun _ => 1, fun _ => 4, fun _ => 1, fun _ => 1, fun _ => 1,
    fun _ => 1, 0⟩

/-- `ASRA_NonzeroFrequencyTransfer` is not automatic. -/
theorem nonzeroFrequencyTransfer_not_automatic : ¬ ASRA_NonzeroFrequencyTransfer trivialData := by
  rintro ⟨h⟩
  obtain ⟨X₀, hX⟩ := h (1 / 2) (by norm_num)
  have := hX X₀ le_rfl
  simp [trivialData] at this
  norm_num at this

/-- `ASRA_SignedSieveMainTerm` is not automatic. -/
theorem signedSieveMainTerm_not_automatic : ¬ ASRA_SignedSieveMainTerm trivialData := by
  rintro ⟨h⟩
  obtain ⟨X₀, hX⟩ := h (1 / 2) (by norm_num)
  have := hX X₀ le_rfl
  simp [trivialData] at this
  norm_num at this

/-- **Firewall**: the assembly implication does not inhabit its premises — ASRA can fail. -/
theorem asra_not_automatic : ¬ ASRA trivialData := by
  intro h
  obtain ⟨X₀, hX⟩ := h (1 / 2) (by norm_num)
  have := hX X₀ le_rfl
  simp [trivialData] at this
  norm_num at this

end AsraInterfaces
end ResearchBankV9
end Erdos287
