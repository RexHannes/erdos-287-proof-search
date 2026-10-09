import RequestProject.Erdos287.W3Publication

/-!
# Erdős #287 — current tail consolidation: the seven-block consumer

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.  Deterministic consumer only.**

Reuses (through the frozen W3 public interface, i.e. `Erdos287.PostV87V90R`):
the moment Cauchy consumer `exists_occupancy_of_moment`, the cyclic contact graph
`ContactCycle`, `alpha_contactCycle`, and the affine-compiler / row-rigidity consumer
`occupancy_contact_false` (adjacent omissions ⟹ contradiction with an exact #287 word).

Kernel-proved:

* `mu7`, `nu7` — `μ = 999999`, `ν = 1700001700000/7`;
* `seven_block_margin` — `μ²/2 - μ - 2ν = 199965200021/14 > 0`;
* `Gamma72`, `alpha_Gamma72` — `α(Γ_{7,2}) = 2` for `Γ_{7,2} = ContactCycle 7 2`;
* `seven_block_moment_ineq` — for `|𝔼P - μ| ≤ ε`, `|𝔼Q - ν| ≤ ε`, `0 ≤ ε ≤ 1`:
  `2(𝔼P + 2𝔼Q) < (𝔼P)²`;
* `seven_block_three_occupied` — hence a parameter of positive weight with **at least three
  occupied blocks**;
* `SevenBlockMainTermDictionary` — the (paper-level) main-term evaluation: the normalised
  moments are `μ`, `ν` up to `|R_Σ^P| / (𝒩_X I)`;
* `seven_block_of_remainder` — `|R_Σ^P| ≤ 𝒩_X I` (true eventually when
  `R_Σ^P = o(𝒩_X I)`) ⟹ three occupied blocks;
* `seven_block_contact_false` — with window control on the support, three occupied blocks of a
  `7`-block affine compiler for the graph `Γ_{7,2}` contradict an exact word (adjacent
  omissions via the trusted affine compiler + row rigidity).
-/

open scoped BigOperators
open Finset

namespace Erdos287.CurrentTail

open Erdos287 Erdos287.PostV71V87 Erdos287.PostV87V90R

/-- `μ = 999999`. -/
noncomputable def mu7 : ℝ := 999999

/-- `ν = 1700001700000/7`. -/
noncomputable def nu7 : ℝ := 1700001700000 / 7

/-- **Kernel check:** `μ²/2 - μ - 2ν = 199965200021/14`. -/
theorem seven_block_margin_eq : mu7 ^ 2 / 2 - mu7 - 2 * nu7 = 199965200021 / 14 := by
  unfold mu7 nu7; norm_num

theorem seven_block_margin : 0 < mu7 ^ 2 / 2 - mu7 - 2 * nu7 := by
  rw [seven_block_margin_eq]; norm_num

/-- The same identity over `ℚ` (exact rational arithmetic, no floating point). -/
theorem seven_block_margin_rat :
    ((999999 : ℚ) ^ 2 / 2 - 999999 - 2 * (1700001700000 / 7)) = 199965200021 / 14 := by
  norm_num

/-- `Γ_{7,2}`: the cyclic contact graph on seven blocks with useful distance `≥ 2`. -/
abbrev Gamma72 : SimpleGraph (ZMod 7) := ContactCycle 7 2

/-- **`α(Γ_{7,2}) = 2`.** -/
theorem alpha_Gamma72 : alpha Gamma72 = 2 :=
  alpha_contactCycle (r := 7) (m := 2) (by norm_num) (by norm_num)

/-- **Seven-block moment inequality** with an `ε ≤ 1` perturbation of `(μ, ν)`. -/
theorem seven_block_moment_ineq {P Q ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hP : |P - mu7| ≤ ε) (hQ : |Q - nu7| ≤ ε) :
    2 * (P + 2 * Q) < P ^ 2 := by
  have hP' := abs_le.1 hP
  have hQ' := abs_le.1 hQ
  have hm := seven_block_margin
  unfold mu7 nu7 at *
  nlinarith [hP'.1, hP'.2, hQ'.1, hQ'.2]

/-- **Three occupied blocks.**  If the normalised first and second moments of the block counts
are within `ε ≤ 1` of `(μ, ν)`, some parameter of positive weight has `Z ≥ 3`. -/
theorem seven_block_three_occupied {ι : Type*} [Fintype ι] (F : FiniteWeights)
    (Y : ℕ → ι → ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hP : |F.E (fun t => (Pcount Y t : ℝ)) - mu7| ≤ ε)
    (hQ : |F.E (fun t => (Qcount Y t : ℝ)) - nu7| ≤ ε) :
    ∃ t ∈ F.T, 0 < F.w t ∧ 3 ≤ Zcount Y t := by
  have h := seven_block_moment_ineq hε0 hε1 hP hQ
  exact exists_occupancy_of_moment F Y 2 (by push_cast; linarith)

/-- **Main-term dictionary (paper-level input, named).**  The normalised moments equal
`(μ, ν)` up to the source remainder `R_Σ^P` divided by the normalisation `𝒩_X I > 0`.
This records the Euler/main-term evaluation; it is *not* an analytic estimate of `R_Σ^P`. -/
structure SevenBlockMainTermDictionary {ι : Type*} [Fintype ι] (F : FiniteWeights)
    (Y : ℕ → ι → ℕ) (R NI : ℝ) : Prop where
  NI_pos : 0 < NI
  first : |F.E (fun t => (Pcount Y t : ℝ)) - mu7| ≤ |R| / NI
  second : |F.E (fun t => (Qcount Y t : ℝ)) - nu7| ≤ |R| / NI

/-- **`R_Σ^P` small ⟹ at least three occupied blocks.** -/
theorem seven_block_of_remainder {ι : Type*} [Fintype ι] {F : FiniteWeights}
    {Y : ℕ → ι → ℕ} {R NI : ℝ} (D : SevenBlockMainTermDictionary F Y R NI)
    (hR : |R| ≤ NI) : ∃ t ∈ F.T, 0 < F.w t ∧ 3 ≤ Zcount Y t := by
  have h1 : |R| / NI ≤ 1 := by rw [div_le_one D.NI_pos]; exact hR
  exact seven_block_three_occupied F Y (div_nonneg (abs_nonneg _) D.NI_pos.le) h1 D.first
    D.second

/-- **`R_Σ^P = o(𝒩_X I)` ⟹ eventually three occupied blocks** (for a family indexed by `X`). -/
theorem seven_block_of_littleO {ι : Type*} [Fintype ι] (F : ℕ → FiniteWeights)
    (Y : ℕ → ℕ → ι → ℕ) (R NI : ℕ → ℝ)
    (D : ∀ X, SevenBlockMainTermDictionary (F X) (Y X) (R X) (NI X))
    (hlo : ∀ ε > 0, ∃ X0, ∀ X ≥ X0, |R X| ≤ ε * NI X) :
    ∃ X0, ∀ X ≥ X0, ∃ t ∈ (F X).T, 0 < (F X).w t ∧ 3 ≤ Zcount (Y X) t := by
  obtain ⟨X0, hX0⟩ := hlo 1 one_pos
  exact ⟨X0, fun X hX => seven_block_of_remainder (D X) (by simpa using hX0 X hX)⟩

/-- **Seven-block contact consumer.**  For a `7`-block affine compiler for `Γ_{7,2}`
(`ContactCycle 7 2`) with window control on the support, moments within `ε ≤ 1` of `(μ, ν)`
contradict an exact #287 word (via adjacent omissions, row rigidity and `α(Γ_{7,2}) = 2`). -/
theorem seven_block_contact_false (W : ExactWord) {K : ℕ} (C : AffineContactCompiler 7 2 K)
    {H : ℕ} (F : FiniteWeights) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hP : |F.E (fun t => (Pcount (blockCount C) t : ℝ)) - mu7| ≤ ε)
    (hQ : |F.E (fun t => (Qcount (blockCount C) t : ℝ)) - nu7| ≤ ε)
    (hctrl : ∀ t ∈ F.T, 0 < F.w t → WindowControl C W.a W.M H t) : False := by
  obtain ⟨t, ht, hw, hZ⟩ := seven_block_three_occupied F (blockCount C) hε0 hε1 hP hQ
  rw [Zcount_blockCount] at hZ
  exact occupancy_contact_false W C (by norm_num) (by norm_num) (hctrl t ht hw) hZ

/-- The remainder form of the contact consumer. -/
theorem seven_block_contact_false_of_remainder (W : ExactWord) {K : ℕ}
    (C : AffineContactCompiler 7 2 K) {H : ℕ} (F : FiniteWeights) {R NI : ℝ}
    (D : SevenBlockMainTermDictionary F (blockCount C) R NI) (hR : |R| ≤ NI)
    (hctrl : ∀ t ∈ F.T, 0 < F.w t → WindowControl C W.a W.M H t) : False := by
  obtain ⟨t, ht, hw, hZ⟩ := seven_block_of_remainder D hR
  rw [Zcount_blockCount] at hZ
  exact occupancy_contact_false W C (by norm_num) (by norm_num) (hctrl t ht hw) hZ

end Erdos287.CurrentTail
