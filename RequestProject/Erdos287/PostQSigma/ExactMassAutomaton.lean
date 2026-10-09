import RequestProject.Erdos287.QSigma.Certificate

/-!
# Erdős #287 — post-`Q_Σ` bank, §8: the repaired exact-mass path automaton

**Status: BANK (proved in Lean).**  The old modulo-`W` automaton is **RETIRED**
(see the regression fixture `modW_false_acceptance` below).

The automaton scans the positions `n = 0, 1, …, L-1` in increasing order.  Its state is

  `(position n, previousOmitted, omissionCount, exactIntegerMass)`

with `0 ≤ exactIntegerMass ≤ T`.  At position `n` it may

* **SKIP/SELECT** `n` (keep it in the selected set): the mass is unchanged;
* **TAKE/OMIT** `n`: allowed only if `n ∈ V`, the previous position was not omitted
  (adjacency), the new mass `m + b(n)` is still `≤ T`, and the count stays `≤ R`.

`reach_iff` : an exact omission solution exists iff an accepting state
`(L, *, *, T)` is reachable.  The physical instance is `exact_mass_automaton_iff`.
-/

open scoped BigOperators

namespace Erdos287.PostQSigma

open Erdos287.ExactSource

/-- Reachability in the exact-mass automaton.  `Reach V b T Rc n pv c m` says that after
scanning positions `< n` the state `(pv, c, m)` is reachable. -/
inductive Reach (V : Finset ℕ) (b : ℕ → ℕ) (T Rc : ℕ) : ℕ → Bool → ℕ → ℕ → Prop
  | start : Reach V b T Rc 0 false 0 0
  | skip {n : ℕ} {pv : Bool} {c m : ℕ} : Reach V b T Rc n pv c m → Reach V b T Rc (n + 1) false c m
  | take {n c m : ℕ} : Reach V b T Rc n false c m → n ∈ V → m + b n ≤ T → c + 1 ≤ Rc →
      Reach V b T Rc (n + 1) true (c + 1) (m + b n)

section Abstract

variable {V : Finset ℕ} {b : ℕ → ℕ} {T Rc : ℕ}

/-- Soundness invariant of the automaton. -/
theorem Reach.sound {n : ℕ} {pv : Bool} {c m : ℕ} (h : Reach V b T Rc n pv c m) :
    ∃ E : Finset ℕ, E ⊆ V ∧ (∀ x ∈ E, x < n) ∧ Indep E ∧ E.card = c ∧
      (∑ x ∈ E, b x) = m ∧ m ≤ T ∧ c ≤ Rc ∧ (pv = true ↔ (1 ≤ n ∧ n - 1 ∈ E)) := by
  induction h with
  | start => exact ⟨∅, by simp, by simp, by simp [Indep], by simp, by simp, by simp, by simp,
      by simp⟩
  | @skip n pv c m _ ih =>
    obtain ⟨E, hEV, hlt, hind, hc, hm, hmT, hcR, -⟩ := ih
    refine ⟨E, hEV, fun x hx => by have := hlt x hx; omega, hind, hc, hm, hmT, hcR, ?_⟩
    simp only [Bool.false_eq_true, false_iff, not_and]
    intro _ hE; have := hlt _ hE; omega
  | @take n c m _ hnV hmT hcR ih =>
    obtain ⟨E, hEV, hlt, hind, hc, hm, -, -, hpv⟩ := ih
    have hnE : n ∉ E := fun h' => by have := hlt n h'; omega
    refine ⟨insert n E, Finset.insert_subset hnV hEV, ?_, ?_, ?_, ?_, hmT, hcR, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · omega
      · have := hlt x hx; omega
    · intro x hx hx1
      rcases Finset.mem_insert.1 hx with rfl | hx
      · rcases Finset.mem_insert.1 hx1 with h' | h'
        · omega
        · have := hlt _ h'; omega
      · rcases Finset.mem_insert.1 hx1 with h' | h'
        · have : 1 ≤ n ∧ n - 1 ∈ E := ⟨by omega, by rw [← h']; simpa using hx⟩
          simp at hpv; exact absurd this.2 (hpv this.1)
        · exact hind x hx h'
    · rw [Finset.card_insert_of_notMem hnE, hc]
    · rw [Finset.sum_insert hnE, hm, add_comm]
    · simp

/-- Completeness invariant: every admissible exact set is traced by the automaton. -/
theorem Reach.complete {E : Finset ℕ} (hEV : E ⊆ V) (hind : Indep E) (hcR : E.card ≤ Rc)
    (hmT : (∑ x ∈ E, b x) ≤ T) (n : ℕ) :
    Reach V b T Rc n (decide (1 ≤ n ∧ n - 1 ∈ E)) (E.filter (· < n)).card
      (∑ x ∈ E.filter (· < n), b x) := by
  classical
  induction n with
  | zero =>
    have : E.filter (· < 0) = ∅ := by ext x; simp
    rw [this]; simpa using Reach.start
  | succ n ih =>
    by_cases hn : n ∈ E
    · have hpv : decide (1 ≤ n ∧ n - 1 ∈ E) = false := by
        simp only [decide_eq_false_iff_not, not_and]
        intro h1 h2
        exact hind (n - 1) h2 (by rwa [Nat.sub_add_cancel h1])
      rw [hpv] at ih
      have hfilt : E.filter (· < n + 1) = insert n (E.filter (· < n)) := by
        ext x; simp only [Finset.mem_filter, Finset.mem_insert]; constructor
        · rintro ⟨h1, h2⟩; by_cases hx : x = n
          · exact Or.inl hx
          · exact Or.inr ⟨h1, by omega⟩
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨hn, by omega⟩
          · exact ⟨h1, by omega⟩
      have hnot : n ∉ E.filter (· < n) := by simp
      have hdec : decide (1 ≤ n + 1 ∧ n + 1 - 1 ∈ E) = true := by simp [hn]
      rw [hdec, hfilt, Finset.card_insert_of_notMem hnot, Finset.sum_insert hnot, add_comm (b n)]
      refine Reach.take ih (hEV hn) ?_ ?_
      · rw [add_comm, ← Finset.sum_insert hnot, ← hfilt]
        exact (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans hmT
      · rw [← Finset.card_insert_of_notMem hnot, ← hfilt]
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans hcR
    · have hfilt : E.filter (· < n + 1) = E.filter (· < n) := by
        ext x; simp only [Finset.mem_filter]; constructor
        · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h | rfl
          · exact h
          · exact absurd h1 hn
        · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
      have hdec : decide (1 ≤ n + 1 ∧ n + 1 - 1 ∈ E) = false := by simp [hn]
      rw [hdec, hfilt]
      exact Reach.skip ih

/-- **Exact-mass automaton equivalence** (abstract form): for `V ⊆ [0, L)`, an independent
`E ⊆ V` with `|E| ≤ R` and `∑_{E} b = T` exists iff an accepting state is reachable. -/
theorem reach_iff {L : ℕ} (hVL : V ⊆ Finset.range L) :
    (∃ E : Finset ℕ, E ⊆ V ∧ Indep E ∧ E.card ≤ Rc ∧ (∑ x ∈ E, b x) = T) ↔
      ∃ pv c, Reach V b T Rc L pv c T := by
  constructor
  · rintro ⟨E, hEV, hind, hcR, hsum⟩
    have hc := Reach.complete (b := b) (T := T) hEV hind hcR hsum.le L
    have : E.filter (· < L) = E := Finset.filter_true_of_mem (fun x hx =>
      Finset.mem_range.1 (hVL (hEV hx)))
    rw [this, hsum] at hc
    exact ⟨_, _, hc⟩
  · rintro ⟨pv, c, h⟩
    obtain ⟨E, hEV, -, hind, hc, hm, -, hcR, -⟩ := h.sound
    exact ⟨E, hEV, hind, hc ▸ hcR, hm⟩

end Abstract

/-! ## Physical instance -/

lemma V_subset_range {a M : ℕ} {R : Finset ℕ} : V a M R ⊆ Finset.range (M + 1) := by
  intro n hn
  have := (mem_B.1 (V_subset_B hn)).2.1
  exact Finset.mem_range.2 (by omega)

lemma cast_sum_div (W : ℕ) (E : Finset ℕ) :
    ((∑ n ∈ E, W / n : ℕ) : ℤ) = ∑ n ∈ E, ((W / n : ℕ) : ℤ) := by
  push_cast; rfl

/-- **`exact_mass_automaton_iff`**: the exact source has a solution iff `T ≥ 0` and the
exact-mass automaton on `V`, with weights `W/n`, target `T` and count bound `R_T`, reaches an
accepting state. -/
theorem exact_mass_automaton_iff {a M : ℕ} {R : Finset ℕ} (ha : 0 < a) :
    (∃ E, SourceSol a M R E) ↔
      0 ≤ T a M R ∧ ∃ pv c, Reach (V a M R) (fun n => W a M R / n) (T a M R).toNat
        (RT a M R) (M + 1) pv c (T a M R).toNat := by
  rw [← reach_iff V_subset_range]
  constructor
  · rintro ⟨E, h⟩
    have hT := h.T_nonneg
    refine ⟨hT, E, h.1, h.2.1, h.card_le_RT ha, ?_⟩
    have h2 := h.2.2
    rw [← cast_sum_div] at h2
    omega
  · rintro ⟨hT, E, hEV, hind, -, hsum⟩
    refine ⟨E, hEV, hind, ?_⟩
    rw [← cast_sum_div, hsum, Int.toNat_of_nonneg hT]

/-! ## Regression firewall: modulo-`W` false acceptance (RETIRED automaton) -/

/-- What the retired modulo-`W` automaton accepts: an independent `E ⊆ V` whose mass is only
congruent to `T` modulo `W`. -/
def ModAccept (V : Finset ℕ) (b : ℕ → ℕ) (W T : ℕ) : Prop :=
  ∃ E ∈ V.powerset, Indep E ∧ (∑ x ∈ E, b x) % W = T % W

/-- **Fixture (DIAGNOSTIC)**: `V = {2,4,6,8}`, `W = 24`, weights `W/n = 12, 6, 4, 3`, `T = 1`.
The modulo-`W` automaton accepts (`12+6+4+3 = 25 ≡ 1`), but no exact solution exists. -/
theorem modW_false_acceptance :
    ModAccept {2, 4, 6, 8} (fun n => 24 / n) 24 1 ∧
      ¬ ∃ E ∈ ({2, 4, 6, 8} : Finset ℕ).powerset, Indep E ∧ (∑ x ∈ E, 24 / x) = 1 := by
  unfold ModAccept Indep
  decide

end Erdos287.PostQSigma
