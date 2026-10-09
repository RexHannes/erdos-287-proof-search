import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V8 §2I: the GOOD-M counting interface

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Exact bookkeeping:

  `U_X = [X, 2X] ∩ ℤ`,  `E_X` = preprocessing REJECT set,  `C_X = U_X \ E_X`.

For a family `F` of residual UNSAT certificates with valid-source sets `J_F`:

* `entrySat_count_eq` — **if** the family is *complete* (every non-ENTRY-SAT source of `C_X` is
  caught by some certificate) and *sound* (a caught source is not ENTRY-SAT), then
  `#ENTRY-SAT sources = |C_X| − |C_X ∩ ⋃_F J_F|`;
* `exists_good_source_of_first_moment` — the first-moment criterion, **only as an implication**:
  `∑_F |C_X ∩ J_F| < |C_X|` together with completeness gives a good (ENTRY-SAT) source.

Neither `|C_X| > 0` nor completeness of any certificate family is inhabited here
(`completeness_not_automatic` shows completeness is a genuine hypothesis).
-/

open scoped BigOperators

namespace Erdos287
namespace ResearchBankV8
namespace GoodM

/-- `U_X = [X, 2X]`. -/
def U (X : ℕ) : Finset ℕ := Finset.Icc X (2 * X)

/-- `C_X = U_X \ E_X`. -/
def Cset (X : ℕ) (E : Finset ℕ) : Finset ℕ := U X \ E

/-- Completeness of a certificate family on `C_X`: every non-ENTRY-SAT source is caught. -/
def Complete (X : ℕ) (E : Finset ℕ) (entrySat : ℕ → Prop) {ι : Type*} (F : Finset ι)
    (J : ι → Finset ℕ) : Prop :=
  ∀ M ∈ Cset X E, ¬ entrySat M → ∃ f ∈ F, M ∈ J f

/-- Soundness of a certificate family: a caught source is not ENTRY-SAT. -/
def Sound (X : ℕ) (E : Finset ℕ) (entrySat : ℕ → Prop) {ι : Type*} (F : Finset ι)
    (J : ι → Finset ℕ) : Prop :=
  ∀ M ∈ Cset X E, ∀ f ∈ F, M ∈ J f → ¬ entrySat M

/-- **Exact ENTRY-SAT count**, given a complete and sound certificate family. -/
theorem entrySat_count_eq (X : ℕ) (E : Finset ℕ) (entrySat : ℕ → Prop) [DecidablePred entrySat]
    {ι : Type*} [DecidableEq ι] (F : Finset ι) (J : ι → Finset ℕ)
    (hcomp : Complete X E entrySat F J) (hsound : Sound X E entrySat F J) :
    ((Cset X E).filter entrySat).card =
      (Cset X E).card - (Cset X E ∩ F.biUnion J).card := by
  have : (Cset X E).filter entrySat = Cset X E \ (Cset X E ∩ F.biUnion J) := by
    ext M
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hM, hs⟩
      refine ⟨hM, fun ⟨_, f, hf, hJ⟩ => hsound M hM f hf hJ hs⟩
    · rintro ⟨hM, hn⟩
      refine ⟨hM, ?_⟩
      by_contra hs
      obtain ⟨f, hf, hJ⟩ := hcomp M hM hs
      exact hn ⟨hM, f, hf, hJ⟩
  rw [this, Finset.card_sdiff_of_subset Finset.inter_subset_left]

/-- `|C_X ∩ ⋃_F J_F| ≤ ∑_F |C_X ∩ J_F|` (union bound). -/
theorem inter_biUnion_card_le {ι : Type*} [DecidableEq ι] (C : Finset ℕ) (F : Finset ι)
    (J : ι → Finset ℕ) : (C ∩ F.biUnion J).card ≤ ∑ f ∈ F, (C ∩ J f).card := by
  rw [Finset.inter_biUnion]
  exact Finset.card_biUnion_le

/-- **First-moment criterion (implication only).** -/
theorem exists_good_source_of_first_moment (X : ℕ) (E : Finset ℕ) (entrySat : ℕ → Prop)
    {ι : Type*} [DecidableEq ι] (F : Finset ι) (J : ι → Finset ℕ)
    (hcomp : Complete X E entrySat F J)
    (hmoment : ∑ f ∈ F, (Cset X E ∩ J f).card < (Cset X E).card) :
    ∃ M ∈ Cset X E, entrySat M := by
  have hlt : (Cset X E ∩ F.biUnion J).card < (Cset X E).card :=
    lt_of_le_of_lt (inter_biUnion_card_le _ F J) hmoment
  obtain ⟨M, hM, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨M, hM, ?_⟩
  by_contra hs
  obtain ⟨f, hf, hJ⟩ := hcomp M hM hs
  exact hnot (Finset.mem_inter.2 ⟨hM, Finset.mem_biUnion.2 ⟨f, hf, hJ⟩⟩)

/-- The first-moment inequality forces `|C_X| > 0` — it is *not* supplied for free. -/
theorem card_pos_of_first_moment (X : ℕ) (E : Finset ℕ) {ι : Type*} (F : Finset ι)
    (J : ι → Finset ℕ) (hmoment : ∑ f ∈ F, (Cset X E ∩ J f).card < (Cset X E).card) :
    0 < (Cset X E).card := lt_of_le_of_lt (Nat.zero_le _) hmoment

/-- **Completeness is a genuine hypothesis**: the empty certificate family is not complete when
some surviving source fails ENTRY-SAT, and the first-moment inequality alone (without
completeness) does not produce an ENTRY-SAT source. -/
theorem completeness_not_automatic :
    ¬ Complete 1 ∅ (fun _ => False) (∅ : Finset ℕ) (fun _ => ∅) ∧
    (∑ f ∈ (∅ : Finset ℕ), (Cset 1 ∅ ∩ (fun _ => (∅ : Finset ℕ)) f).card < (Cset 1 ∅).card) ∧
    ¬ ∃ M ∈ Cset 1 ∅, (fun _ => False) M := by
  refine ⟨?_, by decide, by simp⟩
  intro h
  obtain ⟨f, hf, -⟩ := h 1 (by decide) id
  simp at hf

end GoodM
end ResearchBankV8
end Erdos287
