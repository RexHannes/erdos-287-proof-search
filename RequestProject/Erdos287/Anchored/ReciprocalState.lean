import RequestProject.Erdos287.Anchored.Core

/-!
# Anchored finite reciprocal state

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Let `C` be a finite set of positive cofactors, `P ⊆ C` the *mandatory selected* cofactors and
`N ⊆ C` the *mandatory omitted* cofactors, with `P ∩ N = ∅`.  The permitted reciprocal-value
set is

`𝒱_C(P,N) = { ∑_{c ∈ E} 1/c : P ⊆ E ⊆ C \ N }`,

computed in exact rational arithmetic.  The empty subset (value `0`) is represented
explicitly and is *never* encoded by a numerator product.

The local feasibility predicate `AnchoredFeasible p C P N` says that some allowed subset has
`p`-adic valuation at least `1`, with the zero value treated separately.

The file proves the exact reduced-numerator criterion

`v ≠ 0 → (1 ≤ v_p(v) ↔ p ∣ num v)`

for **every** prime `p` (no largeness assumption of any kind).
-/

open scoped BigOperators

namespace Erdos287
namespace Anchored

/-! ## A.4  The anchored state -/

/-- An *anchor* on the cofactor set `C`: mandatory selections `P`, mandatory omissions `N`,
disjoint. -/
structure Anchor (C : Finset ℕ) (P N : Finset ℕ) : Prop where
  /-- the mandatory selections lie in `C` -/
  sel_sub : P ⊆ C
  /-- the mandatory omissions lie in `C` -/
  omit_sub : N ⊆ C
  /-- and they are disjoint -/
  disj : Disjoint P N

/-- The subsets of `C` allowed by the anchor `(P, N)`. -/
def allowed (C P N : Finset ℕ) : Finset (Finset ℕ) :=
  (C \ N).powerset.filter (fun E => P ⊆ E)

@[simp] theorem mem_allowed {C P N E : Finset ℕ} :
    E ∈ allowed C P N ↔ P ⊆ E ∧ E ⊆ C ∧ Disjoint E N := by
  classical
  simp only [allowed, Finset.mem_filter, Finset.mem_powerset, Finset.subset_sdiff]
  tauto

theorem allowed_nonempty {C P N : Finset ℕ} (h : Anchor C P N) :
    (allowed C P N).Nonempty :=
  ⟨P, mem_allowed.2 ⟨Finset.Subset.refl P, h.sel_sub, h.disj⟩⟩

/-- The permitted reciprocal-value set `𝒱_C(P,N)`, in exact rational arithmetic. -/
def valueSet (C P N : Finset ℕ) : Finset ℚ := (allowed C P N).image recipSum

@[simp] theorem mem_valueSet {C P N : Finset ℕ} {v : ℚ} :
    v ∈ valueSet C P N ↔ ∃ E ∈ allowed C P N, recipSum E = v := by
  simp [valueSet]

theorem valueSet_nonneg {C P N : Finset ℕ} {v : ℚ} (hv : v ∈ valueSet C P N) : 0 ≤ v := by
  obtain ⟨E, _, hE⟩ := mem_valueSet.1 hv
  exact hE ▸ recipSum_nonneg E

/-- The *zero state* is allowed exactly when nothing is mandatorily selected (given positive
cofactors).  The zero value is thus represented explicitly, never through a numerator. -/
theorem zero_mem_valueSet_iff {C P N : Finset ℕ} (hC : ∀ c ∈ C, 0 < c) :
    (0 : ℚ) ∈ valueSet C P N ↔ P = ∅ := by
  constructor
  · rintro hv
    obtain ⟨E, hE, hE0⟩ := mem_valueSet.1 hv
    rw [mem_allowed] at hE
    by_contra hP
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 hP
    have haE : a ∈ E := hE.1 ha
    have : 0 < recipSum E :=
      recipSum_pos ⟨a, haE⟩ (fun c hc => hC c (hE.2.1 hc))
    rw [hE0] at this
    exact lt_irrefl _ this
  · intro hP
    refine mem_valueSet.2 ⟨∅, mem_allowed.2 ⟨by simp [hP], by simp, by simp⟩, ?_⟩
    simp

/-! ## A.5  The exact reduced-numerator criterion -/

/-- **`one_le_padicValRat_iff_dvd_num`.**  `KERNEL-PROVED`.  For a nonzero rational `v` in
lowest terms and *any* prime `p`:  `v_p(v) ≥ 1 ↔ p ∣ num v`.  No largeness hypothesis on `p`
is used. -/
theorem one_le_padicValRat_iff_dvd_num (p : ℕ) [hp : Fact p.Prime] {v : ℚ} (hv : v ≠ 0) :
    1 ≤ padicValRat p v ↔ (p : ℤ) ∣ v.num := by
  have hnum : v.num ≠ 0 := Rat.num_ne_zero.mpr hv
  constructor
  · intro h
    by_contra hnd
    have h0 : padicValInt p v.num = 0 := padicValInt.eq_zero_of_not_dvd hnd
    have hval : padicValRat p v = -(padicValNat p v.den : ℤ) := by
      simp [padicValRat, h0]
    omega
  · intro h
    have habs : p ∣ v.num.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h
      simpa using this
    have hd : ¬ p ∣ v.den := by
      intro hdvd
      have hcop := v.reduced
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left habs hcop) hdvd
      exact hp.out.one_lt.ne' this
    have h0 : padicValNat p v.den = 0 := padicValNat.eq_zero_of_not_dvd hd
    have h1 : 1 ≤ padicValInt p v.num :=
      one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hnum) habs
    simp only [padicValRat, h0]
    omega

/-! ## A.6  Local feasibility -/

/-- **`AnchoredFeasible p C P N`.**  Some anchor-allowed subset has positive `p`-adic
valuation of its reciprocal sum, the zero value being treated separately and explicitly. -/
def AnchoredFeasible (p : ℕ) (C P N : Finset ℕ) : Prop :=
  ∃ E ∈ allowed C P N, recipSum E = 0 ∨ 1 ≤ padicValRat p (recipSum E)

/-- Reformulation of local feasibility purely in terms of numerators. -/
theorem anchoredFeasible_iff_num (p : ℕ) [Fact p.Prime] (C P N : Finset ℕ) :
    AnchoredFeasible p C P N ↔
      ∃ E ∈ allowed C P N, recipSum E = 0 ∨ (p : ℤ) ∣ (recipSum E).num := by
  unfold AnchoredFeasible
  constructor
  · rintro ⟨E, hE, h⟩
    refine ⟨E, hE, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · by_cases h0 : recipSum E = 0
      · exact Or.inl h0
      · exact Or.inr ((one_le_padicValRat_iff_dvd_num p h0).1 h)
  · rintro ⟨E, hE, h⟩
    refine ⟨E, hE, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · by_cases h0 : recipSum E = 0
      · exact Or.inl h0
      · exact Or.inr ((one_le_padicValRat_iff_dvd_num p h0).2 h)

end Anchored
end Erdos287
