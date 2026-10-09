import RequestProject.Erdos287.ResearchBankV22.RoundedRoughSieve

/-!
# Erdős #287 — Research Bank V22 §4: first-forbidden-prefix positivity

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Kernel-proved finite combinatorics (LEAN BANK), for ANY prefix condition `cond`:

* `FirstFail cond B` — `B` is a **first failed prefix**: its last (= smallest) atom `m` sits at
  index `|B|`, the previous prefix `B \ {m}` is admissible, `|B \ {m}|` is even (so the index
  `|B|` is ODD — `firstFail_odd`), and `cond (B \ {m}) m` fails (`firstFail_not_adm`);
* `adm_insert_min` — adding a new smallest atom `m` to `A` keeps all earlier conditions and adds
  exactly one condition at `m`;
* **`dsum_ellW_classification`** — for nonempty `D` with smallest atom `m`,

      ∑_{A ⊆ D} μ(A) 1_{Adm A} = #{A ⊆ D \ {m} : FirstFail (A ∪ {m})}.

  Reading: every non-admissible `A ⊆ D` is classified by its first failed prefix `B`; that
  prefix has odd index, so the omitted correction `-μ(B) = +1` is nonnegative; the remaining
  Möbius tail over the atoms of `D` below `min B` is `∑_{C ⊆ T} μ(C) = 1_{T = ∅} ∈ {0,1}`
  (`mobius_tail`), so only the prefixes ending at the smallest atom of `D` survive, each
  contributing `+1`;
* **`dsum_ellW_ge`** — `∑_{A ⊆ D} ℓ(A) ≥ 1_{D = ∅}`, hence `≥ 0` (`dsum_ellW_nonneg`);
* **`dsum_ellRd_ge`** — for the rounded rough sieve:
  `S_{ℓ_rd}(n) ≥ 1(no rough prime divides n)` and `S_{ℓ_rd}(n) ≥ 0`;
* `ellW_support_prod_le` — support bound: an admissible `A` has `∏_{p∈A} w(p) ≤ X`
  (for `w ≥ 1` monotone), i.e. `ℓ_rd` has level `X = x^{vartheta0}`.
-/

namespace Erdos287
namespace ResearchBankV22
namespace FirstForbiddenPrefix

open Finset RoundedRoughSieve

variable {γ : Type*} [LinearOrder γ]

/-- `B` is a first failed prefix (its smallest atom `m` is at odd index `|B|` and fails). -/
def FirstFail (cond : Finset γ → γ → Prop) (B : Finset γ) : Prop :=
  ∃ m ∈ B, (∀ q ∈ B, m ≤ q) ∧ Adm cond (B.erase m) ∧ Even (B.erase m).card ∧
    ¬ cond (B.erase m) m

/-- **The first failed prefix has odd index.** -/
theorem firstFail_odd {cond : Finset γ → γ → Prop} {B : Finset γ} (h : FirstFail cond B) :
    Odd B.card := by
  obtain ⟨m, hm, -, -, he, -⟩ := h
  rw [← Finset.card_erase_add_one hm]
  exact he.add_one

theorem above_eq_erase_of_min {B : Finset γ} {m : γ} (hmin : ∀ q ∈ B, m ≤ q) :
    above B m = B.erase m := by
  ext q
  simp only [above, mem_filter, mem_erase]
  constructor
  · rintro ⟨hq, hlt⟩; exact ⟨ne_of_gt hlt, hq⟩
  · rintro ⟨hne, hq⟩; exact ⟨hq, lt_of_le_of_ne (hmin q hq) (Ne.symm hne)⟩

/-- A first failed prefix is not admissible. -/
theorem firstFail_not_adm {cond : Finset γ → γ → Prop} {B : Finset γ} (h : FirstFail cond B) :
    ¬ Adm cond B := by
  obtain ⟨m, hm, hmin, -, he, hc⟩ := h
  intro hadm
  have := hadm m hm
  rw [above_eq_erase_of_min hmin] at this
  exact hc (this he)

/-- **Adding a new smallest atom** adds exactly one condition. -/
theorem adm_insert_min (cond : Finset γ → γ → Prop) {A : Finset γ} {m : γ}
    (hlt : ∀ q ∈ A, m < q) :
    Adm cond (insert m A) ↔ Adm cond A ∧ (Even A.card → cond A m) := by
  have hmA : m ∉ A := fun h => lt_irrefl m (hlt m h)
  have h1 : above (insert m A) m = A := by
    ext q; simp only [above, mem_filter, mem_insert]
    constructor
    · rintro ⟨rfl | hq, hq'⟩
      · exact absurd hq' (lt_irrefl _)
      · exact hq
    · intro hq; exact ⟨Or.inr hq, hlt q hq⟩
  have h2 : ∀ q ∈ A, above (insert m A) q = above A q := by
    intro q hq; ext r; simp only [above, mem_filter, mem_insert]
    constructor
    · rintro ⟨rfl | hr, hr'⟩
      · exact absurd (hlt q hq) (not_lt.2 hr'.le)
      · exact ⟨hr, hr'⟩
    · rintro ⟨hr, hr'⟩; exact ⟨Or.inr hr, hr'⟩
  constructor
  · intro h
    refine ⟨fun q hq he => ?_, fun he => ?_⟩
    · have := h q (mem_insert_of_mem hq); rw [h2 q hq] at this; exact this he
    · have := h m (mem_insert_self m A); rw [h1] at this; exact this he
  · rintro ⟨hA, hm⟩ q hq
    rcases mem_insert.1 hq with rfl | hq
    · rw [h1]; exact hm
    · rw [h2 q hq]; exact hA q hq

/-- `FirstFail (A ∪ {m})` for a new smallest atom `m`. -/
theorem firstFail_insert_iff (cond : Finset γ → γ → Prop) {A : Finset γ} {m : γ}
    (hlt : ∀ q ∈ A, m < q) :
    FirstFail cond (insert m A) ↔ Adm cond A ∧ Even A.card ∧ ¬ cond A m := by
  have hmA : m ∉ A := fun h => lt_irrefl m (hlt m h)
  constructor
  · rintro ⟨m', hm', hmin, hadm, he, hc⟩
    have hmm : m' = m := by
      apply le_antisymm (hmin m (mem_insert_self m A))
      rcases mem_insert.1 hm' with h | h
      · exact h.ge
      · exact (hlt m' h).le
    subst hmm
    rw [erase_insert hmA] at hadm he hc
    exact ⟨hadm, he, hc⟩
  · rintro ⟨hadm, he, hc⟩
    refine ⟨m, mem_insert_self m A, fun q hq => ?_, ?_, ?_, ?_⟩
    · rcases mem_insert.1 hq with rfl | h
      · exact le_rfl
      · exact (hlt q h).le
    all_goals rw [erase_insert hmA]
    exacts [hadm, he, hc]

/-- **Möbius tail**: `∑_{C ⊆ T} μ(C) = 1_{T=∅}`, which is `0` or `1`. -/
theorem mobius_tail {α : Type*} [DecidableEq α] (T : Finset α) :
    ∑ C ∈ T.powerset, (-1 : ℝ) ^ C.card = if T = ∅ then 1 else 0 := by
  have := Finset.sum_powerset_neg_one_pow_card (x := T)
  split_ifs at this ⊢ <;> exact_mod_cast this

theorem mobius_tail_zero_or_one {α : Type*} [DecidableEq α] (T : Finset α) :
    ∑ C ∈ T.powerset, (-1 : ℝ) ^ C.card = 0 ∨ ∑ C ∈ T.powerset, (-1 : ℝ) ^ C.card = 1 := by
  rw [mobius_tail]; split_ifs <;> simp

open Classical in
/-- **First-forbidden-prefix classification** of the divisor sum of `ℓ = μ · 1_Adm`. -/
theorem dsum_ellW_classification (cond : Finset γ → γ → Prop) (D : Finset γ) (hD : D.Nonempty) :
    dsum (ellW cond) D =
      (((D.erase (D.min' hD)).powerset.filter
        fun A => FirstFail cond (insert (D.min' hD) A)).card : ℝ) := by
  set m := D.min' hD with hm
  have hmD : m ∈ D := min'_mem D hD
  have hlt : ∀ A ∈ (D.erase m).powerset, ∀ q ∈ A, m < q := by
    intro A hA q hq
    have hq' := mem_powerset.1 hA hq
    exact lt_of_le_of_ne (min'_le D q (mem_of_mem_erase hq')) (Ne.symm (ne_of_mem_erase hq'))
  unfold dsum
  conv_lhs => rw [← insert_erase hmD]
  rw [sum_powerset_insert (notMem_erase m D), ← sum_add_distrib, card_filter]
  push_cast
  refine sum_congr rfl fun A hA => ?_
  have hmA : m ∉ A := fun h => lt_irrefl m (hlt A hA m h)
  rw [firstFail_insert_iff cond (hlt A hA)]
  unfold ellW
  rw [card_insert_of_notMem hmA]
  simp only [adm_insert_min cond (hlt A hA)]
  rcases Nat.even_or_odd A.card with he | ho
  · by_cases hadm : Adm cond A <;> by_cases hc : cond A m <;>
      simp [hadm, he, hc, pow_succ, Even.neg_one_pow he]
  · have hne : ¬ Even A.card := Nat.not_even_iff_odd.2 ho
    by_cases hadm : Adm cond A <;> simp [hadm, hne, pow_succ, Odd.neg_one_pow ho]

/-- **Positivity of the rough sieve**: `∑_{A ⊆ D} ℓ(A) ≥ 1_{D = ∅}`. -/
theorem dsum_ellW_ge (cond : Finset γ → γ → Prop) (D : Finset γ) :
    (if D = ∅ then 1 else 0) ≤ dsum (ellW cond) D := by
  rcases D.eq_empty_or_nonempty with rfl | hD
  · simp [dsum, ellW_empty]
  · rw [if_neg hD.ne_empty, dsum_ellW_classification cond D hD]
    exact Nat.cast_nonneg _

theorem dsum_ellW_nonneg (cond : Finset γ → γ → Prop) (D : Finset γ) :
    0 ≤ dsum (ellW cond) D :=
  le_trans (by split_ifs <;> norm_num) (dsum_ellW_ge cond D)

/-- **Rounded rough sieve positivity**: `S_{ℓ_rd}(D) ≥ 1(no rough atom in D)`. -/
theorem dsum_ellRd_ge (U : Finset γ) (w : γ → ℝ) (X : ℝ) (D : Finset γ) :
    (if D ∩ U = ∅ then 1 else 0) ≤ dsum (ellRd U w X) D := by
  rw [dsum_inter (ellRd_supported U w X)]
  have : dsum (ellRd U w X) (D ∩ U) = dsum (ellW (roundedCond w X)) (D ∩ U) := by
    unfold dsum
    refine sum_congr rfl fun A hA => ?_
    have : A ⊆ U := (mem_powerset.1 hA).trans inter_subset_right
    simp [ellRd, this]
  rw [this]
  exact dsum_ellW_ge _ _

theorem dsum_ellRd_nonneg (U : Finset γ) (w : γ → ℝ) (X : ℝ) (D : Finset γ) :
    0 ≤ dsum (ellRd U w X) D :=
  le_trans (by split_ifs <;> norm_num) (dsum_ellRd_ge U w X D)

/-- **Support/level bound**: an admissible modulus has `∏_{p∈A} w(p) ≤ X`. -/
theorem ellW_support_prod_le {w : γ → ℝ} {X : ℝ} (hX : 1 ≤ X) {A : Finset γ}
    (hw1 : ∀ p ∈ A, 1 ≤ w p) (hmono : ∀ p ∈ A, ∀ q ∈ A, p ≤ q → w p ≤ w q)
    (hA : Adm (roundedCond w X) A) : ∏ p ∈ A, w p ≤ X := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simpa using hX
  set m := A.min' hne
  have hmA : m ∈ A := min'_mem A hne
  have hmin : ∀ q ∈ A, m ≤ q := fun q hq => min'_le A q hq
  have hc := hA m hmA
  rw [above_eq_erase_of_min hmin] at hc
  have hwm : 1 ≤ w m := hw1 m hmA
  rw [← mul_prod_erase A w hmA]
  have hP : ∀ B ⊆ A, 1 ≤ ∏ q ∈ B, w q := fun B hB => by
    have := prod_le_prod (s := B) (f := fun _ => (1 : ℝ)) (g := w) (fun _ _ => zero_le_one)
      (fun q hq => hw1 q (hB hq))
    simpa using this
  rcases Nat.even_or_odd (A.erase m).card with he | ho
  · have h3 := hc he
    unfold roundedCond at h3
    have hP1 := hP _ (erase_subset m A)
    nlinarith [pow_le_pow_right₀ hwm (show 1 ≤ 3 by norm_num), pow_one (w m)]
  · have hne' : (A.erase m).Nonempty := by
      rw [← card_pos]; exact ho.pos
    set m2 := (A.erase m).min' hne'
    have hm2 : m2 ∈ A.erase m := min'_mem _ hne'
    have hm2A : m2 ∈ A := mem_of_mem_erase hm2
    have hmm2 : m < m2 := lt_of_le_of_ne (hmin m2 hm2A) (Ne.symm (ne_of_mem_erase hm2))
    have habove : above A m2 = (A.erase m).erase m2 := by
      ext q; simp only [above, mem_filter, mem_erase]
      constructor
      · rintro ⟨hq, hlt⟩
        exact ⟨ne_of_gt hlt, ne_of_gt (lt_trans hmm2 hlt), hq⟩
      · rintro ⟨hq2, hqm, hq⟩
        exact ⟨hq, lt_of_le_of_ne ((A.erase m).min'_le q (mem_erase.2 ⟨hqm, hq⟩))
          (Ne.symm hq2)⟩
    have hcard : Even (above A m2).card := by
      rw [habove, card_erase_of_mem hm2]
      obtain ⟨k, hk⟩ := ho
      exact ⟨k, by omega⟩
    have h3 := hA m2 hm2A hcard
    rw [habove] at h3
    unfold roundedCond at h3
    rw [← mul_prod_erase (A.erase m) w hm2]
    have hwm2 : 1 ≤ w m2 := hw1 m2 hm2A
    have hle : w m ≤ w m2 := hmono m hmA m2 hm2A hmm2.le
    have hP2 := hP ((A.erase m).erase m2) ((erase_subset m2 _).trans (erase_subset m A))
    set Q := ∏ q ∈ (A.erase m).erase m2, w q
    have : w m * (w m2 * Q) ≤ Q * w m2 ^ 3 := by
      have h1 : w m * w m2 ≤ w m2 ^ 3 := by
        have a : w m * w m2 ≤ w m2 * w m2 := mul_le_mul_of_nonneg_right hle (by linarith)
        have b : w m2 * w m2 * 1 ≤ w m2 * w m2 * w m2 :=
          mul_le_mul_of_nonneg_left hwm2 (by positivity)
        nlinarith
      nlinarith
    linarith

end FirstForbiddenPrefix
end ResearchBankV22
end Erdos287
