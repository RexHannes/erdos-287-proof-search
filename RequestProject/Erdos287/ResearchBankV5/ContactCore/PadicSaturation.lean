import Mathlib.Tactic
import RequestProject.Erdos287.ResearchBankV5.ContactCore.ProperPowerRow

/-!
# Contact-core route — `p`-adic layer saturation (local kernel bank)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The digit-by-digit proof of (PADIC-SAT) needs, at each valuation layer, the finite additive fact

> the subset sums of any `ℓ - 1` nonzero residues cover `𝔽_ℓ`.

This is `subsetSums_eq_univ` below, proved from scratch (no Cauchy–Davenport is needed: the
`|S| ≥ min(ℓ, k+1)` growth argument suffices, with the observation that a subset-sum set closed
under translation by a nonzero residue is all of `𝔽_ℓ`).

`padicLayer_hits_target` is the layer-local selection statement actually consumed by the
proper-power row analysis: with at least `ℓ - 1` available nonzero unit residues in a layer, every
target residue at that layer is realizable by a subset of the available cofactors.

The **global** statement (PADIC-SAT) — that a required-selected set `P` with
`|C_v \ P| ≥ ℓ - 1` at every layer extends to a complete legal row state — is recorded as the
`Prop` `PadicSaturationStatement`; it is *not* inhabited in this layer.  Only its layer-local
ingredient is kernel-proved here.
-/

namespace Erdos287
namespace ResearchBankV5
namespace ContactCore

open Finset

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- All subset sums of a list of residues. -/
def subsetSums (p : ℕ) : List (ZMod p) → Finset (ZMod p)
  | [] => {0}
  | a :: t => (subsetSums p t) ∪ (subsetSums p t).image (fun s => s + a)

theorem subsetSums_nonempty (L : List (ZMod p)) : (subsetSums p L).Nonempty := by
  induction L with
  | nil => exact ⟨0, by simp [subsetSums]⟩
  | cons a t ih => obtain ⟨x, hx⟩ := ih; exact ⟨x, by simp [subsetSums, hx]⟩

/-- A nonempty subset-sum set closed under translation by a nonzero residue is everything. -/
theorem subsetSums_univ_of_closed {L : List (ZMod p)} {a : ZMod p} (ha : a ≠ 0)
    (hcl : ∀ s ∈ subsetSums p L, s + a ∈ subsetSums p L) : subsetSums p L = Finset.univ := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  obtain ⟨x, hx⟩ := subsetSums_nonempty (p := p) L
  have hstep : ∀ k : ℕ, x + (k : ZMod p) * a ∈ subsetSums p L := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ n ih =>
        have h1 := hcl _ ih
        have he : x + (n : ZMod p) * a + a = x + ((n + 1 : ℕ) : ZMod p) * a := by
          push_cast; ring
        rwa [he] at h1
  refine Finset.eq_univ_iff_forall.2 fun y => ?_
  have h2 := hstep ((y - x) * a⁻¹).val
  have hcast : ((((y - x) * a⁻¹).val : ℕ) : ZMod p) = (y - x) * a⁻¹ := by
    simp [ZMod.natCast_val, ZMod.cast_id]
  rw [hcast] at h2
  have hfix : x + (y - x) * a⁻¹ * a = y := by
    rw [mul_assoc, inv_mul_cancel₀ ha, mul_one]; ring
  rwa [hfix] at h2

/-- **Growth lemma.**  The subset sums of `k` nonzero residues form a set of size at least
`min p (k+1)`. -/
theorem subsetSums_card_ge (L : List (ZMod p)) (h0 : ∀ a ∈ L, a ≠ 0) :
    min p (L.length + 1) ≤ (subsetSums p L).card := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  induction L with
  | nil =>
      have hcard : (subsetSums p ([] : List (ZMod p))).card = 1 := by simp [subsetSums]
      have hp : 1 ≤ p := (Fact.out : Nat.Prime p).pos
      simp only [List.length_nil, hcard]
      omega
  | cons a t ih =>
      have ha : a ≠ 0 := h0 a (by simp)
      have iht := ih (fun b hb => h0 b (by simp [hb]))
      by_cases hcl : ∀ s ∈ subsetSums p t, s + a ∈ subsetSums p t
      · have huniv : subsetSums p t = Finset.univ := subsetSums_univ_of_closed ha hcl
        have hall : subsetSums p (a :: t) = Finset.univ := by
          show (subsetSums p t) ∪ (subsetSums p t).image (fun s => s + a) = Finset.univ
          rw [huniv]; simp
        rw [hall, Finset.card_univ, ZMod.card]
        exact min_le_left _ _
      · push_neg at hcl
        obtain ⟨s, hs, hsa⟩ := hcl
        have hmem : s + a ∈ subsetSums p (a :: t) := by
          show s + a ∈ (subsetSums p t) ∪ (subsetSums p t).image (fun x => x + a)
          exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨s, hs, rfl⟩)
        have hsubset : subsetSums p t ⊆ subsetSums p (a :: t) := by
          intro x hx
          show x ∈ (subsetSums p t) ∪ (subsetSums p t).image (fun y => y + a)
          exact Finset.mem_union_left _ hx
        have hssub : subsetSums p t ⊂ subsetSums p (a :: t) :=
          (Finset.ssubset_iff_of_subset hsubset).2 ⟨s + a, hmem, hsa⟩
        have hcard := Finset.card_lt_card hssub
        simp only [List.length_cons]
        omega

/-- **Finite additive lemma.**  Subset sums of any `p - 1` nonzero residues cover `ZMod p`. -/
theorem subsetSums_eq_univ (L : List (ZMod p)) (h0 : ∀ a ∈ L, a ≠ 0) (hlen : p - 1 ≤ L.length) :
    subsetSums p L = Finset.univ := by
  have hge := subsetSums_card_ge L h0
  have hp : 1 ≤ p := (Fact.out : Nat.Prime p).pos
  have hcard : p ≤ (subsetSums p L).card := by omega
  exact Finset.eq_univ_of_card _ (by
    have hle : (subsetSums p L).card ≤ Fintype.card (ZMod p) := Finset.card_le_univ _
    rw [ZMod.card] at hle ⊢
    omega)

/-- **Layer-local selection (the digit step of PADIC-SAT).**  If a valuation layer offers at least
`ℓ - 1` available cofactors with nonzero reduced unit residues, then *every* target residue at
that layer is attained by a subset of the available cofactors. -/
theorem padicLayer_hits_target (L : List (ZMod p)) (h0 : ∀ a ∈ L, a ≠ 0)
    (hlen : p - 1 ≤ L.length) (target : ZMod p) : target ∈ subsetSums p L := by
  rw [subsetSums_eq_univ L h0 hlen]
  exact Finset.mem_univ target

/-! ## The global statement (not inhabited here) -/

/-- **(PADIC-SAT), global form.**  For a base `ℓ`, cofactor interval `[A, N]` and required-selected
set `P`, if every valuation layer leaves at least `ℓ - 1` free cofactors, then `P` extends to a
complete legal row state (i.e. a selection satisfying `PPRow`).

This `Prop` is **not** inhabited in this layer: only its layer-local digit step
(`padicLayer_hits_target`) is kernel-proved here.  It is carried as an explicit hypothesis by any
consumer. -/
def PadicSaturationStatement (ℓ A N : ℕ) (P : Finset ℕ) : Prop :=
  (∀ v : ℕ,
      ℓ - 1 ≤ (((Finset.Icc A N).filter
        (fun c => ℓ ^ v ∣ c ∧ ¬ ℓ ^ (v + 1) ∣ c)) \ P).card) →
    ∃ ε : ℕ → ℤ, (∀ c ∈ P, ε c = 1) ∧ (∀ c, ε c = 0 ∨ ε c = 1) ∧ PPRow ℓ A N ε

/-- **Obstruction dichotomy input.**  If a valuation layer obstructs the extension, it must be
almost entirely required-selected: `|P ∩ C_v| ≥ n_v - (ℓ - 2)`.  Combined with
`heavy_layer_majority` and `sparse_layer_bound` this is the heavy/sparse split
`PP obstruction = charged heavy layer ⊍ O(ℓ) sparse tail`. -/
def LayerObstruction (ℓ A N : ℕ) (P : Finset ℕ) (v : ℕ) : Prop :=
  exactLayerCount A N ℓ v - (ℓ - 2) ≤
    (((Finset.Icc A N).filter (fun c => ℓ ^ v ∣ c ∧ ¬ ℓ ^ (v + 1) ∣ c)) ∩ P).card

/-- **Heavy branch of the dichotomy.**  An obstructing *heavy* layer is charged: the
required-selected set occupies a strict majority of it. -/
theorem heavy_obstruction_charged {ℓ A N : ℕ} {P : Finset ℕ} {v : ℕ} (hℓ : 2 ≤ ℓ)
    (hheavy : 2 * ℓ ≤ exactLayerCount A N ℓ v) (hobs : LayerObstruction ℓ A N P v) :
    exactLayerCount A N ℓ v <
      2 * (((Finset.Icc A N).filter (fun c => ℓ ^ v ∣ c ∧ ¬ ℓ ^ (v + 1) ∣ c)) ∩ P).card :=
  heavy_layer_majority _ _ ℓ hℓ hheavy hobs

/-- **Sparse branch of the dichotomy.**  A non-heavy layer carries at most `6ℓ` multiples of
`ℓ^v` in total, so the whole `p`-adic tail below it is `O(ℓ)`. -/
theorem sparse_obstruction_small {ℓ A N v : ℕ} (hℓ : 2 ≤ ℓ)
    (hsparse : exactLayerCount A N ℓ v < 2 * ℓ) : layerCount A N ℓ v ≤ 6 * ℓ :=
  sparse_layer_bound A N ℓ v hℓ hsparse

/-! ## Finite regressions -/

/-- Finite regression for the additive lemma at `ℓ = 5`: the four nonzero residues `1,1,1,1`
already give the subset sums `{0,1,2,3,4} = 𝔽₅`. -/
theorem subsetSums_regression_five :
    subsetSums 5 [1, 1, 1, 1] = Finset.univ := by decide

/-- Finite regression at `ℓ = 3` with mixed residues. -/
theorem subsetSums_regression_three :
    subsetSums 3 [2, 1] = Finset.univ := by decide

/-- Finite regression: three nonzero residues are **not** always enough at `ℓ = 5` when one
removes one of them — the bound `ℓ - 1` is sharp for the list `[1,1,1]`. -/
theorem subsetSums_regression_sharp :
    subsetSums 5 [1, 1, 1] ≠ Finset.univ := by decide

end ContactCore
end ResearchBankV5
end Erdos287
