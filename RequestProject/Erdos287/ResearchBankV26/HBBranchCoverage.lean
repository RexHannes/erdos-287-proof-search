import RequestProject.Erdos287.ResearchBankV26.DyadicSourceMap
import RequestProject.Erdos287.ResearchBankV26.RoughSWAdapter

/-!
# Erdős #287 — Research Bank V26 §4.6: Heath-Brown branch coverage

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Each HB term has at most six variables; a dyadic box assigns to each variable a length exponent
`e_i ≥ 0` with `Σ e_i = 1` (normalised by `log x`).

**LEAN BANK.**
* `greedy_subset_sum` — if every step is `≤ c` and the target window `[L, U]` has length
  `≥ c`, a sub-sum lands in the window;
* **`branch_trichotomy`** — for `0 < α ≤ 2/5`, every length vector is
  TYPE II (some sub-product has length in `[α, 1−α]`), ONE-LARGE (a single variable
  `> 1−α`) or TWO-LARGE (two variables with total `> 1−α`);
* `trichotomy_fails_beyond` (regression) — at `α = 12/25 > 2/5` five equal variables `1/5`
  are in none of the three classes, so the threshold matters;
* `BranchRecord` — the actual branch record (source coefficient, selected Type-II variables,
  complementary variables, roughness, one-bounded / `L²` status, length, dyadic box, provider);
* `classify` / `classify_spec` — every box receives a record whose provider condition HOLDS;
* **`source_level_coverage`** — every source term of the HB sum is counted exactly once, in
  exactly one branch:  `Σ_m F(m) = Σ_{kind} Σ_{boxes b of this kind} Σ_{m ∈ b} F(m)`.
-/

namespace Erdos287
namespace ResearchBankV26
namespace HBBranchCoverage

open Finset

/-- **Greedy sub-sum lemma** (LEAN BANK). -/
theorem greedy_subset_sum {ι : Type*} [DecidableEq ι] (e : ι → ℝ) {c L U base : ℝ}
    (hLU : L + c ≤ U) (hbase : base ≤ U) :
    ∀ s : Finset ι, (∀ i ∈ s, 0 ≤ e i ∧ e i ≤ c) → L ≤ base + ∑ i ∈ s, e i →
      ∃ t ⊆ s, L ≤ base + ∑ i ∈ t, e i ∧ base + ∑ i ∈ t, e i ≤ U := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _ h; exact ⟨∅, subset_refl _, by simpa using h, by simpa using hbase⟩
  | insert i s hi ih =>
    intro he htot
    by_cases hs : L ≤ base + ∑ j ∈ s, e j
    · obtain ⟨t, ht, h1, h2⟩ := ih (fun j hj => he j (mem_insert_of_mem hj)) hs
      exact ⟨t, ht.trans (subset_insert _ _), h1, h2⟩
    · push_neg at hs
      refine ⟨insert i s, subset_refl _, htot, ?_⟩
      rw [sum_insert hi]
      have := (he i (mem_insert_self _ _)).2
      linarith

/-- Type II: a sub-product of length in `[α, 1−α]`. -/
def TypeII {ι : Type*} (s : Finset ι) (e : ι → ℝ) (α : ℝ) : Prop :=
  ∃ t ⊆ s, α ≤ ∑ i ∈ t, e i ∧ ∑ i ∈ t, e i ≤ 1 - α

/-- One-large: a single variable of length `> 1−α`. -/
def OneLarge {ι : Type*} (s : Finset ι) (e : ι → ℝ) (α : ℝ) : Prop := ∃ i ∈ s, 1 - α < e i

/-- Two-large: two distinct variables with total length `> 1−α`. -/
def TwoLarge {ι : Type*} (s : Finset ι) (e : ι → ℝ) (α : ℝ) : Prop :=
  ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ 1 - α < e i + e j

/-- **Structural trichotomy** (LEAN BANK). -/
theorem branch_trichotomy {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι → ℝ)
    (he : ∀ i ∈ s, 0 ≤ e i) (hsum : ∑ i ∈ s, e i = 1) {α : ℝ} (hα : 0 < α) (hα' : α ≤ 2 / 5) :
    TypeII s e α ∨ OneLarge s e α ∨ TwoLarge s e α := by
  by_contra hno
  push_neg at hno
  obtain ⟨h2, h1, h3⟩ := hno
  -- every single variable is < α
  have hsmall : ∀ i ∈ s, e i < α := by
    intro i hi
    by_contra hge; push_neg at hge
    have hle : e i ≤ 1 - α := by
      by_contra hgt; push_neg at hgt
      exact h1 ⟨i, hi, hgt⟩
    exact h2 ⟨{i}, by simpa using hi, by simpa using hge, by simpa using hle⟩
  have hne : s.Nonempty := by
    by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h; rw [h] at hsum; simp at hsum
  obtain ⟨a, ha, hamax⟩ := Finset.exists_max_image s e hne
  have hs' : (s.erase a).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have : ∑ i ∈ s, e i = e a := by
      rw [← Finset.add_sum_erase s e ha, h, Finset.sum_empty, add_zero]
    have := hsmall a ha
    linarith
  obtain ⟨b, hb, hbmax⟩ := Finset.exists_max_image (s.erase a) e hs'
  have hba : b ≠ a := Finset.ne_of_mem_erase hb
  have hbs : b ∈ s := Finset.mem_of_mem_erase hb
  -- the pair `a, b`
  have hpair : e a + e b < α := by
    by_contra hge; push_neg at hge
    have hle : e a + e b ≤ 1 - α := by
      by_contra hgt; push_neg at hgt
      exact h3 ⟨a, ha, b, hbs, hba.symm, hgt⟩
    exact h2 ⟨{a, b}, by
      intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption,
      by rw [sum_pair hba.symm]; exact hge, by rw [sum_pair hba.symm]; exact hle⟩
  have hab : e b ≤ e a := hamax b hbs
  by_cases hm2 : e b ≤ 1 - 2 * α
  · -- greedy on the remaining variables starting from `e a + e b`
    set r := (s.erase a).erase b
    have hr : ∀ i ∈ r, 0 ≤ e i ∧ e i ≤ e b := fun i hi =>
      ⟨he i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)),
        hbmax i (Finset.mem_of_mem_erase hi)⟩
    have htot : e a + e b + ∑ i ∈ r, e i = 1 := by
      rw [← hsum, ← Finset.add_sum_erase s e ha, ← Finset.add_sum_erase (s.erase a) e hb]; ring
    obtain ⟨t, ht, hL, hU⟩ := greedy_subset_sum e (c := e b) (L := α) (U := 1 - α)
      (base := e a + e b) (by linarith) (by linarith) r hr (by linarith)
    have hat : a ∉ t := fun h => by
      have := ht h; simp [r] at this
    have hbt : b ∉ t := fun h => by
      have := ht h; simp [r] at this
    refine h2 ⟨insert a (insert b t), ?_, ?_, ?_⟩
    · intro x hx
      simp only [mem_insert] at hx
      rcases hx with rfl | rfl | hx
      · exact ha
      · exact hbs
      · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (ht hx))
    · rw [sum_insert (by simp [hat, hba.symm]), sum_insert hbt, ← add_assoc]; exact hL
    · rw [sum_insert (by simp [hat, hba.symm]), sum_insert hbt, ← add_assoc]; exact hU
  · push_neg at hm2
    linarith

/-- **Regression: the trichotomy fails beyond `2/5`** — five variables of length `1/5` at
`α = 12/25`: no sub-sum in `[12/25, 13/25]`, no single `> 13/25`, no pair `> 13/25`. -/
theorem trichotomy_fails_beyond :
    ¬ (TypeII (Finset.univ : Finset (Fin 5)) (fun _ => (1 : ℝ) / 5) (12 / 25) ∨
      OneLarge (Finset.univ : Finset (Fin 5)) (fun _ => (1 : ℝ) / 5) (12 / 25) ∨
      TwoLarge (Finset.univ : Finset (Fin 5)) (fun _ => (1 : ℝ) / 5) (12 / 25)) := by
  rintro (⟨t, -, h1, h2⟩ | ⟨i, -, hi⟩ | ⟨i, -, j, -, -, hij⟩)
  · rw [Finset.sum_const, nsmul_eq_mul] at h1 h2
    have hc : t.card ≤ 5 := by simpa using Finset.card_le_univ t
    interval_cases h : t.card <;> first | (norm_num at h1; done) | norm_num at h2
  · norm_num at hi
  · norm_num at hij

/-! ## Branch records and coverage -/

/-- Branch kinds (the provider used). -/
inductive BranchKind
  | typeII
  | oneLarge
  | twoLarge
  deriving DecidableEq, Repr

/-- Source coefficient kinds of the HB variables. -/
inductive SourceKind
  | roughMu
  | roughOne
  | roughLog
  | singleton
  deriving DecidableEq, Repr

/-- Size status of a coefficient. -/
inductive SizeStatus
  | oneBounded
  | l2DivisorBounded
  deriving DecidableEq, Repr

/-- **An actual branch record.** -/
structure BranchRecord where
  source : Fin 6 → SourceKind
  selected : Finset (Fin 6)
  complementary : Finset (Fin 6)
  roughness : ℕ
  selectedStatus : SizeStatus
  complementaryStatus : SizeStatus
  length : ℝ
  box : Fin 6 → ℕ
  provider : BranchKind

/-- The condition a record must satisfy for its provider. -/
def RecordValid (e : Fin 6 → ℝ) (α : ℝ) (r : BranchRecord) : Prop :=
  r.complementary = Finset.univ \ r.selected ∧ r.length = ∑ i ∈ r.selected, e i ∧
    match r.provider with
    | BranchKind.typeII => α ≤ r.length ∧ r.length ≤ 1 - α
    | BranchKind.oneLarge => ∃ i, r.selected = {i} ∧ 1 - α < e i
    | BranchKind.twoLarge => ∃ i j, i ≠ j ∧ r.selected = {i, j} ∧ 1 - α < e i + e j

open Classical in
/-- **Classification of a box** (noncomputable choice from the trichotomy). -/
noncomputable def classify (src : Fin 6 → SourceKind) (z : ℕ) (box : Fin 6 → ℕ)
    (e : Fin 6 → ℝ) (α : ℝ) : BranchRecord :=
  if h2 : TypeII Finset.univ e α then
    { source := src, selected := h2.choose, complementary := Finset.univ \ h2.choose,
      roughness := z, selectedStatus := SizeStatus.oneBounded,
      complementaryStatus := SizeStatus.l2DivisorBounded,
      length := ∑ i ∈ h2.choose, e i, box := box, provider := BranchKind.typeII }
  else if h1 : OneLarge Finset.univ e α then
    { source := src, selected := {h1.choose}, complementary := Finset.univ \ {h1.choose},
      roughness := z, selectedStatus := SizeStatus.oneBounded,
      complementaryStatus := SizeStatus.l2DivisorBounded,
      length := ∑ i ∈ {h1.choose}, e i, box := box, provider := BranchKind.oneLarge }
  else if h3 : TwoLarge Finset.univ e α then
    { source := src, selected := {h3.choose, h3.choose_spec.2.choose},
      complementary := Finset.univ \ {h3.choose, h3.choose_spec.2.choose},
      roughness := z, selectedStatus := SizeStatus.oneBounded,
      complementaryStatus := SizeStatus.l2DivisorBounded,
      length := ∑ i ∈ {h3.choose, h3.choose_spec.2.choose}, e i, box := box,
      provider := BranchKind.twoLarge }
  else
    { source := src, selected := ∅, complementary := Finset.univ, roughness := z,
      selectedStatus := SizeStatus.oneBounded, complementaryStatus := SizeStatus.oneBounded,
      length := 0, box := box, provider := BranchKind.typeII }

/-- **Every box receives a VALID record** (LEAN BANK), for `0 < α ≤ 2/5`. -/
theorem classify_spec (src : Fin 6 → SourceKind) (z : ℕ) (box : Fin 6 → ℕ) (e : Fin 6 → ℝ)
    (he : ∀ i, 0 ≤ e i) (hsum : ∑ i, e i = 1) {α : ℝ} (hα : 0 < α) (hα' : α ≤ 2 / 5) :
    RecordValid e α (classify src z box e α) ∧ (classify src z box e α).box = box ∧
      (classify src z box e α).source = src := by
  classical
  have htri := branch_trichotomy Finset.univ e (fun i _ => he i) hsum hα hα'
  unfold classify
  split_ifs with h2 h1 h3
  · exact ⟨⟨rfl, rfl, h2.choose_spec.2⟩, rfl, rfl⟩
  · exact ⟨⟨rfl, rfl, h1.choose, rfl, by simpa using h1.choose_spec.2⟩, rfl, rfl⟩
  · exact ⟨⟨rfl, rfl, h3.choose, h3.choose_spec.2.choose,
      h3.choose_spec.2.choose_spec.2.1, rfl, h3.choose_spec.2.choose_spec.2.2⟩, rfl, rfl⟩
  · exfalso; rcases htri with h | h | h
    · exact h2 h
    · exact h1 h
    · exact h3 h

/-- **Source-level coverage** (LEAN BANK): for any finite set of HB variable tuples, any source
coefficient `F`, and any assignment `kindOf` of branch kinds to dyadic boxes, every source term is
counted exactly once, in exactly one branch. -/
theorem source_level_coverage (S : Finset (Fin 6 → ℕ)) (F : (Fin 6 → ℕ) → ℝ)
    (kindOf : (Fin 6 → ℕ) → BranchKind) :
    ∑ m ∈ S, F m = ∑ κ ∈ (S.image DyadicSourceMap.dyadicBox).image kindOf,
      ∑ b ∈ (S.image DyadicSourceMap.dyadicBox).filter (fun b => kindOf b = κ),
        ∑ m ∈ S.filter (fun m => DyadicSourceMap.dyadicBox m = b), F m := by
  rw [DyadicSourceMap.source_sum_by_boxes]
  exact (Finset.sum_fiberwise_of_maps_to (fun b hb => Finset.mem_image_of_mem _ hb) _).symm

end HBBranchCoverage
end ResearchBankV26
end Erdos287
