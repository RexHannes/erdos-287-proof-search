import Mathlib

/-!
# Erdős #287 — Research Bank V10 §K: the repaired three-way HB support selection

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Exact combinatorics of the Heath-Brown support selection.  A support box is a list of at most
eight factors `(t_i, smooth_i)`, with exponents `t_i ≥ 0`, `∑ t_i = 1`, and every **Möbius**
(non-smooth) factor constrained to `t_i ≤ 1/4`.  Let `μ` be the largest smooth exponent (`0` if
there is none), and call `ν` a *partial-product exponent* if it is the exponent sum of a sub-list
of factors.

`hb_selection` **proves** (it is not assumed) the trichotomy

* **I.**   `μ ≥ 4/13`;
* **II.**  some partial-product exponent `ν ∈ [1/8, 1/4]`;
* **III.** `7/24 < μ < 4/13` and some partial-product exponent `ν` with
  `1 − 3μ ≤ ν < 1/8` and `ν > 1/13`.

The proof: if `I` and `II` fail, the factors with `t < 1/8` have total `< 1/8` (otherwise a greedy
prefix lands in `[1/8, 1/4)`), all other factors have `t > 1/4`, hence are smooth with `t ≤ μ`;
counting gives exactly three of them, and `ν := ` total of the small factors gives `III`.

**Classification limitation.**  The smooth / Möbius label of each factor is part of the input data
(`HBFactor.2`); it is exactly the minimal classification the proof needs, and it is recorded here
as a data field, not recovered from any formal Heath-Brown identity.

Counterfixtures: dropping the Möbius bound (`mobius_bound_needed`) or `∑ t_i = 1`
(`sum_one_needed`) breaks the trichotomy.
-/

namespace Erdos287
namespace ResearchBankV10
namespace HBSelection

/-- A factor: exponent and smoothness flag (`true` = smooth, `false` = Möbius). -/
abbrev HBFactor := ℚ × Bool

/-- The largest smooth exponent (`0` if there is none). -/
def maxSmooth (l : List HBFactor) : ℚ :=
  ((l.filter (fun x => x.2)).map (fun x => x.1)).foldr max 0

/-- Partial-product exponent: the exponent sum of a sub-list of factors. -/
def IsPartialProduct (l : List HBFactor) (ν : ℚ) : Prop :=
  ∃ s : List HBFactor, s.Sublist l ∧ (s.map (fun x => x.1)).sum = ν

/-- Case I. -/
def CaseI (l : List HBFactor) : Prop := 4 / 13 ≤ maxSmooth l

/-- Case II. -/
def CaseII (l : List HBFactor) : Prop := ∃ ν, IsPartialProduct l ν ∧ 1 / 8 ≤ ν ∧ ν ≤ 1 / 4

/-- Case III. -/
def CaseIII (l : List HBFactor) : Prop :=
  7 / 24 < maxSmooth l ∧ maxSmooth l < 4 / 13 ∧
    ∃ ν, IsPartialProduct l ν ∧ 1 - 3 * maxSmooth l ≤ ν ∧ ν < 1 / 8 ∧ 1 / 13 < ν

/-- The HB support data: at most eight factors, nonnegative, summing to `1`, Möbius factors
`≤ 1/4`. -/
structure HBData where
  factors : List HBFactor
  length_le : factors.length ≤ 8
  nonneg : ∀ x ∈ factors, 0 ≤ x.1
  sum_one : (factors.map (fun x => x.1)).sum = 1
  mobius_le : ∀ x ∈ factors, x.2 = false → x.1 ≤ 1 / 4

/-! ## Auxiliary list lemmas -/

theorem le_foldr_max (l : List ℚ) : ∀ x ∈ l, x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro x hx
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih x hx).trans (le_max_right _ _)

theorem le_maxSmooth {l : List HBFactor} {x : HBFactor} (hx : x ∈ l) (hs : x.2 = true) :
    x.1 ≤ maxSmooth l :=
  le_foldr_max _ _ (List.mem_map.2 ⟨x, List.mem_filter.2 ⟨hx, by simpa using hs⟩, rfl⟩)

/-- Greedy prefix: values in `[0, δ)` with total `≥ a ≥ 0` have a prefix sum in `[a, a + δ)`. -/
theorem greedy_prefix {δ : ℚ} (hδ : 0 < δ) :
    ∀ (l : List HBFactor) (a : ℚ), 0 ≤ a → (∀ x ∈ l, 0 ≤ x.1 ∧ x.1 < δ) →
      a ≤ (l.map (fun x => x.1)).sum →
      ∃ s : List HBFactor, s.Sublist l ∧ a ≤ (s.map (fun x => x.1)).sum ∧
        (s.map (fun x => x.1)).sum < a + δ := by
  intro l
  induction l with
  | nil =>
    intro a ha _ hsum
    simp only [List.map_nil, List.sum_nil] at hsum
    exact ⟨[], List.Sublist.slnil, by simpa using hsum, by simp; linarith⟩
  | cons y l ih =>
    intro a ha hl hsum
    have hy := hl y List.mem_cons_self
    by_cases hya : a ≤ y.1
    · exact ⟨[y], List.singleton_sublist.2 List.mem_cons_self, by simpa using hya,
        by simp; linarith [hy.2]⟩
    · push_neg at hya
      obtain ⟨s, hs, h1, h2⟩ := ih (a - y.1) (by linarith) (fun x hx => hl x (List.mem_cons_of_mem _ hx))
        (by simp only [List.map_cons, List.sum_cons] at hsum; linarith)
      exact ⟨y :: s, hs.cons₂ y, by simp; linarith, by simp; linarith⟩

theorem sum_filter_add (l : List HBFactor) (p : HBFactor → Bool) :
    ((l.filter p).map (fun x => x.1)).sum + ((l.filter (fun x => !p x)).map (fun x => x.1)).sum =
      (l.map (fun x => x.1)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a <;> simp [h] <;> linarith

theorem sum_le_length_mul {l : List HBFactor} {b : ℚ} (h : ∀ x ∈ l, x.1 ≤ b) :
    (l.map (fun x => x.1)).sum ≤ l.length * b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha := h a List.mem_cons_self
    push_cast; linarith

theorem length_mul_lt_sum {l : List HBFactor} {b : ℚ} (h : ∀ x ∈ l, b < x.1) (hl : l ≠ []) :
    l.length * b < (l.map (fun x => x.1)).sum := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have ha := h a List.mem_cons_self
    by_cases hl' : l = []
    · subst hl'; simp; linarith
    · have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) hl'
      push_cast; linarith

/-! ## The trichotomy -/

/-- **The repaired three-way HB selection** (no length bound needed). -/
theorem hb_selection_list (l : List HBFactor) (hnn : ∀ x ∈ l, 0 ≤ x.1)
    (hsum : (l.map (fun x => x.1)).sum = 1) (hmob : ∀ x ∈ l, x.2 = false → x.1 ≤ 1 / 4) :
    CaseI l ∨ CaseII l ∨ CaseIII l := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hI, hII, hIII⟩ := hcon
  unfold CaseI at hI; push_neg at hI
  set μ := maxSmooth l
  set small := l.filter (fun x => decide (x.1 < 1 / 8))
  set big := l.filter (fun x => !decide (x.1 < 1 / 8))
  have hsmall_sub : small.Sublist l := List.filter_sublist
  have hbig_sub : big.Sublist l := List.filter_sublist
  set S := (small.map (fun x => x.1)).sum
  have hsplit : S + (big.map (fun x => x.1)).sum = 1 := by
    rw [← hsum]; exact sum_filter_add l _
  -- (a) the small factors have total < 1/8
  have hS : S < 1 / 8 := by
    by_contra hS; push_neg at hS
    obtain ⟨s, hs, h1, h2⟩ := greedy_prefix (δ := 1 / 8) (by norm_num) small (1 / 8) (by norm_num)
      (fun x hx => by
        have := List.mem_filter.1 hx
        exact ⟨hnn x this.1, by simpa using this.2⟩) hS
    exact hII ⟨_, ⟨s, hs.trans hsmall_sub, rfl⟩, h1, by linarith⟩
  have hS0 : 0 ≤ S := List.sum_nonneg (fun x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact hnn y (hsmall_sub.subset hy))
  -- (b) every big factor has exponent > 1/4, is smooth, and is ≤ μ
  have hbig : ∀ x ∈ big, 1 / 4 < x.1 ∧ x.2 = true ∧ x.1 ≤ μ := by
    intro x hx
    have hxl : x ∈ l := hbig_sub.subset hx
    have hx8 : 1 / 8 ≤ x.1 := by
      have := (List.mem_filter.1 hx).2; simp at this; linarith
    have hx4 : 1 / 4 < x.1 := by
      by_contra h; push_neg at h
      exact hII ⟨x.1, ⟨[x], List.singleton_sublist.2 hxl, by simp⟩, hx8, h⟩
    have hsm : x.2 = true := by
      by_contra h
      have := hmob x hxl (by simpa using h)
      linarith
    exact ⟨hx4, hsm, le_maxSmooth hxl hsm⟩
  -- (c) counting: exactly three big factors
  have hB : (big.map (fun x => x.1)).sum = 1 - S := by linarith
  have hne : big ≠ [] := by
    intro h; rw [h] at hB; simp at hB; linarith
  have hup := sum_le_length_mul (fun x hx => (hbig x hx).2.2)
  have hlo := length_mul_lt_sum (fun x hx => (hbig x hx).1) hne
  rw [hB] at hup hlo
  have hμ0 : 0 ≤ μ := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil big hne
    have := hbig x hx; linarith
  have hlen4 : (big.length : ℚ) < 4 := by linarith
  have hlen3 : (3 : ℚ) ≤ big.length := by
    by_contra h; push_neg at h
    have h2 : (big.length : ℚ) ≤ 2 := by
      have : big.length < 3 := by exact_mod_cast h
      exact_mod_cast (show big.length ≤ 2 by omega)
    nlinarith
  have hlen : (big.length : ℚ) = 3 := by
    have h1 : big.length < 4 := by exact_mod_cast hlen4
    have h2 : 3 ≤ big.length := by exact_mod_cast hlen3
    have : big.length = 3 := by omega
    exact_mod_cast this
  rw [hlen] at hup
  apply hIII
  refine ⟨by linarith, hI, S, ⟨small, hsmall_sub, rfl⟩, by linarith, hS, by linarith⟩

/-- **The repaired three-way HB selection** for HB support data. -/
theorem hb_selection (D : HBData) : CaseI D.factors ∨ CaseII D.factors ∨ CaseIII D.factors :=
  hb_selection_list D.factors D.nonneg D.sum_one D.mobius_le

/-! ## Counterfixtures for dropped hypotheses -/

theorem no_case_of_singleton_one :
    ¬ (CaseI [((1 : ℚ), false)] ∨ CaseII [((1 : ℚ), false)] ∨ CaseIII [((1 : ℚ), false)]) := by
  have hμ : maxSmooth [((1 : ℚ), false)] = 0 := by simp [maxSmooth]
  have hpp : ∀ ν, IsPartialProduct [((1 : ℚ), false)] ν → ν = 0 ∨ ν = 1 := by
    rintro ν ⟨s, hs, rfl⟩
    rcases List.sublist_singleton.1 hs with rfl | rfl <;> simp
  rintro (h | ⟨ν, hν, h1, h2⟩ | ⟨h1, -⟩)
  · unfold CaseI at h; rw [hμ] at h; norm_num at h
  · rcases hpp ν hν with rfl | rfl <;> linarith
  · rw [hμ] at h1; norm_num at h1

/-- **Dropping the Möbius bound breaks the trichotomy**: one Möbius factor of exponent `1`. -/
theorem mobius_bound_needed :
    ∃ l : List HBFactor, (∀ x ∈ l, 0 ≤ x.1) ∧ (l.map (fun x => x.1)).sum = 1 ∧
      ¬ (CaseI l ∨ CaseII l ∨ CaseIII l) :=
  ⟨[(1, false)], by simp, by simp, no_case_of_singleton_one⟩

/-- **Dropping `∑ t_i = 1` breaks the trichotomy**: the empty support. -/
theorem sum_one_needed :
    ∃ l : List HBFactor, (∀ x ∈ l, 0 ≤ x.1) ∧ (∀ x ∈ l, x.2 = false → x.1 ≤ 1 / 4) ∧
      ¬ (CaseI l ∨ CaseII l ∨ CaseIII l) := by
  refine ⟨[], by simp, by simp, ?_⟩
  have hμ : maxSmooth [] = 0 := rfl
  rintro (h | ⟨ν, ⟨s, hs, rfl⟩, h1, h2⟩ | ⟨h1, -⟩)
  · unfold CaseI at h; rw [hμ] at h; norm_num at h
  · rw [List.sublist_nil.1 hs] at h1; norm_num at h1
  · rw [hμ] at h1; norm_num at h1

end HBSelection
end ResearchBankV10
end Erdos287
