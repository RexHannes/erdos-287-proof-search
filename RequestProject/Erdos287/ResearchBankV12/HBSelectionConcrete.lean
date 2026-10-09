import RequestProject.Erdos287.ResearchBankV12.ConcreteParameters

/-!
# Erdős #287 — Research Bank V12 §8: the concrete three-way HB selection

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For at most eight factor exponents `t_i ≥ 0` with `∑ t_i = 1` (V10 `HBData`), the selection
trichotomy is **proved** (V10 `hb_selection`, re-used here, not assumed):

* **Case I**: `μ ≥ 4/13` (`μ` = largest smooth exponent);
* **Case II**: some partial product `ν` with `1/8 ≤ ν ≤ 1/4`;
* **Case III**: `7/24 < μ < 4/13` and some partial product `ν` with `1 − 3μ ≤ ν`, `ν < 1/8`,
  `1/13 < ν`.

**Minimum classification hypothesis.**  The only non-numerical input is the smooth/Möbius label
of each factor together with the bound "Möbius factors have exponent `≤ 1/4`" (field
`HBData.mobius_le`).  It cannot be dropped: `mobius_label_is_minimal` re-exports the V10
counterfixtures showing that without it (or without `∑ t_i = 1`) the trichotomy fails.  The length
bound `≤ 8` is *not* needed (`selection_without_length_bound`).

Each case is realized by explicit factor data (`caseI_fixture`, `caseII_fixture`,
`caseIII_fixture`); the Case III fixture is in neither Case I nor Case II
(`caseIII_fixture_only`), so Case III is genuinely required.
-/

namespace Erdos287
namespace ResearchBankV12
namespace HBSelectionConcrete

open ResearchBankV10.HBSelection

/-- A Case-II witness. -/
def CaseIIWitness (l : List HBFactor) (ν : ℚ) : Prop :=
  IsPartialProduct l ν ∧ 1 / 8 ≤ ν ∧ ν ≤ 1 / 4

/-- A Case-III witness. -/
def CaseIIIWitness (l : List HBFactor) (ν : ℚ) : Prop :=
  7 / 24 < maxSmooth l ∧ maxSmooth l < 4 / 13 ∧
    IsPartialProduct l ν ∧ 1 - 3 * maxSmooth l ≤ ν ∧ ν < 1 / 8 ∧ 1 / 13 < ν

/-- **The concrete repaired selection theorem** (proved from the finite factor data). -/
theorem concrete_selection (D : HBData) :
    CaseI D.factors ∨ (∃ ν, CaseIIWitness D.factors ν) ∨ (∃ ν, CaseIIIWitness D.factors ν) := by
  rcases hb_selection D with h | ⟨ν, h1, h2, h3⟩ | ⟨h1, h2, ν, h3, h4, h5, h6⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨ν, h1, h2, h3⟩)
  · exact Or.inr (Or.inr ⟨ν, h1, h2, h3, h4, h5, h6⟩)

/-- The length bound is not needed. -/
theorem selection_without_length_bound (l : List HBFactor) (hnn : ∀ x ∈ l, 0 ≤ x.1)
    (hsum : (l.map (fun x => x.1)).sum = 1) (hmob : ∀ x ∈ l, x.2 = false → x.1 ≤ 1 / 4) :
    CaseI l ∨ CaseII l ∨ CaseIII l :=
  hb_selection_list l hnn hsum hmob

/-- **The Möbius-label bound is the minimal classification hypothesis**: dropping it, or dropping
`∑ t_i = 1`, breaks the trichotomy. -/
theorem mobius_label_is_minimal :
    (∃ l : List HBFactor, (∀ x ∈ l, 0 ≤ x.1) ∧ (l.map (fun x => x.1)).sum = 1 ∧
      ¬ (CaseI l ∨ CaseII l ∨ CaseIII l)) ∧
    (∃ l : List HBFactor, (∀ x ∈ l, 0 ≤ x.1) ∧ (∀ x ∈ l, x.2 = false → x.1 ≤ 1 / 4) ∧
      ¬ (CaseI l ∨ CaseII l ∨ CaseIII l)) :=
  ⟨mobius_bound_needed, sum_one_needed⟩

/-! ## Fixtures -/

/-- Partial products are exactly the sums of sublists. -/
theorem isPartialProduct_iff (l : List HBFactor) (ν : ℚ) :
    IsPartialProduct l ν ↔ ν ∈ l.sublists.map (fun s => (s.map (fun x => x.1)).sum) := by
  unfold IsPartialProduct
  simp only [List.mem_map, List.mem_sublists]

def caseIList : List HBFactor := [(1 / 2, true), (1 / 2, true)]
def caseIIList : List HBFactor := [(1 / 5, false), (4 / 5, true)]
def caseIIIList : List HBFactor := [(3 / 10, true), (3 / 10, true), (3 / 10, true), (1 / 10, false)]

theorem caseI_fixture : CaseI caseIList := by
  norm_num [CaseI, maxSmooth, caseIList]

theorem caseII_fixture : CaseIIWitness caseIIList (1 / 5) := by
  refine ⟨⟨[(1 / 5, false)], by simp [caseIIList], by norm_num⟩, by norm_num, by norm_num⟩

theorem maxSmooth_caseIII : maxSmooth caseIIIList = 3 / 10 := by
  norm_num [maxSmooth, caseIIIList]

theorem caseIII_fixture : CaseIIIWitness caseIIIList (1 / 10) := by
  refine ⟨?_, ?_, ⟨[(1 / 10, false)], by simp [caseIIIList], by norm_num⟩, ?_, by norm_num,
    by norm_num⟩ <;> rw [maxSmooth_caseIII] <;> norm_num

/-- The Case III fixture is in neither Case I nor Case II. -/
theorem caseIII_fixture_only : ¬ CaseI caseIIIList ∧ ¬ CaseII caseIIIList := by
  constructor
  · unfold CaseI; rw [maxSmooth_caseIII]; norm_num
  · rintro ⟨ν, hν, h1, h2⟩
    rw [isPartialProduct_iff] at hν
    simp [caseIIIList, List.sublists] at hν
    rcases hν with h | h | h | h | h | h | h | h | h | h | h | h <;>
      (subst h; first | (norm_num at h1; done) | norm_num at h2)

end HBSelectionConcrete
end ResearchBankV12
end Erdos287
