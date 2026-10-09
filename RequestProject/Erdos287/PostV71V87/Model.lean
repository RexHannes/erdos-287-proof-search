import RequestProject.Erdos287.ProblemStatement
import RequestProject.Erdos287.TopLayer

/-!
# Erdős #287 — post-V71 → V87 bank: the formal counterexample model

**ERDŐS #287 REMAINS OPEN.  Nothing in this subtree proves it.**

A *word* is a finite set `A` of distinct positive denominators contained in an interval
`[a, M]` whose two endpoints are selected and which has no two consecutive omissions
(gap-two / 2-syndetic).  An *exact word* additionally has reciprocal mass exactly one.

We keep the exact mass statement (`ExactWord`) strictly separate from the weaker surrogates
(`ValuationSurrogate`, see also `MinorRepair.lean`), and we prove that an exact word with
`a > 1` is literally the same thing as an `Erdos287Counterexample`
(`ExactWord.toCounterexample`, `ofCounterexample`).

Prime-adic data (all for an arbitrary base `p`, usually prime):

* `v p n = n.factorization p`  — the `p`-adic valuation;
* `maxVal W p = max_{n ∈ A} v p n` (the project-wide `topExp`);
* `P W p = p ^ maxVal`        — the maximal primary power;
* `Q W p = p ^ (1 + maxVal)`  — the primary ceiling;
* `carrier W p`               — the maximal carrier set (selected multiples of `P W p`),
  shown equal to the maximal primary layer `topLayer`;
* `qstar W` — the minimal ceiling `min_p Q_p` over primes;
* `row W q` / `selRow W q` — the complete prime-power row `{n ∈ [a,M] : q ∣ n}` and its
  selected part.
-/

open scoped BigOperators

namespace Erdos287.PostV71V87

/-- A gap-two word on `[a, M]` with both endpoints selected. -/
structure Word where
  /-- The selected denominators. -/
  A : Finset ℕ
  /-- Left endpoint. -/
  a : ℕ
  /-- Right endpoint. -/
  M : ℕ
  /-- Denominators are positive. -/
  a_pos : 0 < a
  /-- Every selected denominator lies in `[a, M]`. -/
  sub : A ⊆ Finset.Icc a M
  /-- The left endpoint is selected. -/
  a_mem : a ∈ A
  /-- The right endpoint is selected. -/
  M_mem : M ∈ A
  /-- No two consecutive omissions inside `[a, M]`. -/
  gap : ∀ x, a ≤ x → x + 1 ≤ M → x ∈ A ∨ x + 1 ∈ A

/-- An exact word: a word with reciprocal mass exactly one. -/
structure ExactWord extends Word where
  /-- Exact reciprocal mass one. -/
  mass : ∑ n ∈ A, (1 : ℚ) / n = 1

namespace Word

variable (W : Word)

/-- Boolean selection `x_n`. -/
def x (n : ℕ) : Bool := decide (n ∈ W.A)

theorem x_eq_true_iff (n : ℕ) : W.x n = true ↔ n ∈ W.A := by simp [x]

/-- Reciprocal mass of the word. -/
def mass : ℚ := ∑ n ∈ W.A, (1 : ℚ) / n

/-- Window length `D = M - a`. -/
def D : ℕ := W.M - W.a

theorem a_le_M : W.a ≤ W.M := (Finset.mem_Icc.1 (W.sub W.a_mem)).2

theorem mem_Icc {n : ℕ} (h : n ∈ W.A) : W.a ≤ n ∧ n ≤ W.M := Finset.mem_Icc.1 (W.sub h)

theorem pos_of_mem {n : ℕ} (h : n ∈ W.A) : 0 < n := lt_of_lt_of_le W.a_pos (W.mem_Icc h).1

/-- The `p`-adic valuation. -/
def v (p n : ℕ) : ℕ := n.factorization p

/-- Maximal `p`-adic valuation over the word (the project-wide `topExp`). -/
def maxVal (p : ℕ) : ℕ := topExp W.A p

/-- Maximal primary power `P_p = p ^ maxVal`. -/
def P (p : ℕ) : ℕ := p ^ W.maxVal p

/-- Primary ceiling `Q_p = p ^ (1 + maxVal)`. -/
def Q (p : ℕ) : ℕ := p ^ (1 + W.maxVal p)

theorem Q_eq_mul (p : ℕ) : W.Q p = p * W.P p := by
  simp [Q, P, pow_add]

/-- The maximal primary layer `{n ∈ A : v_p n = maxVal}`. -/
def layer (p : ℕ) : Finset ℕ := topLayer W.A p

/-- The maximal carrier set: selected multiples of the maximal primary power. -/
def carrier (p : ℕ) : Finset ℕ := W.A.filter (fun n => W.P p ∣ n)

/-- A modulus is *absent* when it divides no selected denominator. -/
def Absent (d : ℕ) : Prop := ∀ n ∈ W.A, ¬ d ∣ n

/-- The complete `q`-row of the window. -/
def row (q : ℕ) : Finset ℕ := (Finset.Icc W.a W.M).filter (fun n => q ∣ n)

/-- The selected part of the `q`-row. -/
def selRow (q : ℕ) : Finset ℕ := W.A.filter (fun n => q ∣ n)

/-- The row of prime `p` is *active* when `p` divides some selected denominator. -/
def Active (p : ℕ) : Prop := 1 ≤ W.maxVal p

theorem selRow_subset_row (q : ℕ) : W.selRow q ⊆ W.row q := by
  intro n hn
  simp only [selRow, Finset.mem_filter] at hn
  simp only [row, Finset.mem_filter]
  exact ⟨W.sub hn.1, hn.2⟩

theorem v_le_maxVal {n : ℕ} (h : n ∈ W.A) (p : ℕ) : v p n ≤ W.maxVal p :=
  Finset.le_sup (f := fun a => Nat.factorization a p) h

/-- The maximal valuation is attained. -/
theorem exists_mem_v_eq_maxVal (p : ℕ) : ∃ n ∈ W.A, v p n = W.maxVal p := by
  obtain ⟨n, hn, h⟩ := Finset.exists_mem_eq_sup W.A ⟨W.a, W.a_mem⟩
    (fun a => Nat.factorization a p)
  exact ⟨n, hn, h.symm⟩

theorem layer_nonempty (p : ℕ) : (W.layer p).Nonempty := by
  obtain ⟨n, hn, h⟩ := W.exists_mem_v_eq_maxVal p
  exact ⟨n, mem_topLayer.2 ⟨hn, h⟩⟩

/-- The primary ceiling is absent. -/
theorem Q_absent {p : ℕ} (hp : p.Prime) : W.Absent (W.Q p) := by
  intro n hn hdvd
  have hn0 : n ≠ 0 := (W.pos_of_mem hn).ne'
  have := (hp.pow_dvd_iff_le_factorization hn0).1 hdvd
  have := W.v_le_maxVal hn p
  simp only [v] at this
  omega

/-- The maximal primary power divides an element of the maximal layer. -/
theorem P_dvd_of_mem_layer {p n : ℕ} (hp : p.Prime) (hn : n ∈ W.layer p) : W.P p ∣ n := by
  have h := mem_topLayer.1 hn
  have hn0 : n ≠ 0 := (W.pos_of_mem h.1).ne'
  exact (hp.pow_dvd_iff_le_factorization hn0).2 (by simp [maxVal, h.2])

/-- The maximal carrier set coincides with the maximal primary layer. -/
theorem carrier_eq_layer {p : ℕ} (hp : p.Prime) : W.carrier p = W.layer p := by
  ext n
  constructor
  · intro hn
    simp only [carrier, Finset.mem_filter] at hn
    have hn0 : n ≠ 0 := (W.pos_of_mem hn.1).ne'
    have h1 := (hp.pow_dvd_iff_le_factorization hn0).1 hn.2
    have h2 := W.v_le_maxVal hn.1 p
    exact mem_topLayer.2 ⟨hn.1, le_antisymm h2 h1⟩
  · intro hn
    simp only [carrier, Finset.mem_filter]
    exact ⟨(mem_topLayer.1 hn).1, W.P_dvd_of_mem_layer hp hn⟩

theorem one_lt_Q {p : ℕ} (hp : p.Prime) : 1 < W.Q p :=
  Nat.one_lt_pow (by omega) hp.one_lt

theorem P_pos {p : ℕ} (hp : p.Prime) : 0 < W.P p := pow_pos hp.pos _

/-- If the row of `p` is inactive, the ceiling is `p` itself. -/
theorem Q_eq_self_of_not_active {p : ℕ} (h : ¬ W.Active p) : W.Q p = p := by
  simp [Active] at h
  simp [Q, h]

theorem le_P_of_active {p : ℕ} (hp : p.Prime) (h : W.Active p) : p ≤ W.P p := by
  unfold P
  calc p = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ W.maxVal p := Nat.pow_le_pow_right hp.pos h

/-! ## Minimal ceiling `q_*` -/

theorem exists_ceiling : ∃ q, ∃ p, p.Prime ∧ W.Q p = q := ⟨_, 2, Nat.prime_two, rfl⟩

open Classical in
/-- The minimal primary ceiling `q_* = min_{p prime} Q_p`. -/
noncomputable def qstar : ℕ := Nat.find W.exists_ceiling

theorem qstar_le {p : ℕ} (hp : p.Prime) : W.qstar ≤ W.Q p := by
  classical
  exact Nat.find_min' W.exists_ceiling ⟨p, hp, rfl⟩

theorem qstar_spec : ∃ p, p.Prime ∧ W.Q p = W.qstar := by
  classical
  exact Nat.find_spec W.exists_ceiling

theorem one_lt_qstar : 1 < W.qstar := by
  obtain ⟨p, hp, h⟩ := W.qstar_spec
  rw [← h]; exact W.one_lt_Q hp

theorem qstar_absent : W.Absent W.qstar := by
  obtain ⟨p, hp, h⟩ := W.qstar_spec
  rw [← h]; exact W.Q_absent hp

/-- Every prime strictly below `q_*` has an active row. -/
theorem active_of_lt_qstar {p : ℕ} (hp : p.Prime) (hlt : p < W.qstar) : W.Active p := by
  by_contra h
  have := W.qstar_le hp
  rw [W.Q_eq_self_of_not_active h] at this
  omega

/-! ## Forced omissions and forced neighbours (positional mechanism) -/

/-- An absent modulus forces every one of its multiples in the window to be omitted. -/
theorem forced_omitted {d y : ℕ} (hd : W.Absent d) (hy : d ∣ y) : y ∉ W.A :=
  fun h => hd y h hy

/-- An omitted position of the window is strictly interior. -/
theorem interior_of_omitted {y : ℕ} (hy : W.a ≤ y ∧ y ≤ W.M) (h : y ∉ W.A) :
    W.a < y ∧ y < W.M := by
  refine ⟨lt_of_le_of_ne hy.1 ?_, lt_of_le_of_ne hy.2 ?_⟩
  · rintro rfl; exact h W.a_mem
  · rintro rfl; exact h W.M_mem

/-- Gap-two forces both neighbours of an omitted window position to be selected. -/
theorem neighbours_of_omitted {y : ℕ} (hy : W.a ≤ y ∧ y ≤ W.M) (h : y ∉ W.A) :
    y - 1 ∈ W.A ∧ y + 1 ∈ W.A := by
  have hi := W.interior_of_omitted hy h
  constructor
  · have := W.gap (y - 1) (by omega) (by omega)
    rcases this with h1 | h1
    · exact h1
    · exact absurd (by rwa [Nat.sub_add_cancel (by omega)] at h1) h
  · have := W.gap y (by omega) (by omega)
    rcases this with h1 | h1
    · exact absurd h1 h
    · exact h1

/-- **Literal guard pattern** `(x_{y-1}, x_y, x_{y+1}) = (1,0,1)` at every multiple of an
absent modulus inside the window. -/
theorem guard_pattern {d y : ℕ} (hd : W.Absent d) (hdy : d ∣ y) (hy : W.a ≤ y ∧ y ≤ W.M) :
    W.x (y - 1) = true ∧ W.x y = false ∧ W.x (y + 1) = true := by
  have h := W.forced_omitted hd hdy
  have hn := W.neighbours_of_omitted hy h
  simp [x, h, hn.1, hn.2]

end Word

/-! ## Faithfulness of the model -/

namespace ExactWord

variable (W : ExactWord)

/-- An exact word with left endpoint `a > 1` is an Erdős #287 counterexample. -/
theorem toCounterexample (ha : 1 < W.a) : Erdos287Counterexample W.A where
  card_ge := by
    by_contra hc
    push_neg at hc
    have hsub : W.A ⊆ {W.a} := by
      intro n hn
      have := Finset.card_le_one.1 (by omega) n hn W.a W.a_mem
      simp [this]
    have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun n : ℕ => (1 : ℚ) / n) hsub
      (fun i _ _ => by positivity)
    rw [W.mass] at hle
    simp at hle
    have : (1 : ℚ) < W.a := by exact_mod_cast ha
    have : (W.a : ℚ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ this
    linarith
  one_lt := fun n hn => lt_of_lt_of_le ha (W.mem_Icc hn).1
  sum_one := W.mass
  gap_le_two := by
    intro n hn ⟨b, hb, hnb⟩
    have hbM := (W.mem_Icc hb).2
    by_cases h1 : n + 1 ∈ W.A
    · exact Or.inl h1
    · right
      have hn1 : n + 1 < W.M := by
        rcases lt_or_eq_of_le (show n + 1 ≤ W.M by omega) with h | h
        · exact h
        · exact absurd (h ▸ W.M_mem) h1
      rcases W.gap (n + 1) (by have := (W.mem_Icc hn).1; omega) (by omega) with h2 | h2
      · exact absurd h2 h1
      · exact h2

end ExactWord

/-- Every Erdős #287 counterexample is an exact word on `[min A, max A]`. -/
noncomputable def ofCounterexample {A : Finset ℕ} (h : Erdos287Counterexample A) :
    ExactWord where
  A := A
  a := A.min' h.nonempty
  M := A.max' h.nonempty
  a_pos := lt_trans Nat.zero_lt_one (h.one_lt _ (Finset.min'_mem A h.nonempty))
  sub := fun _ hn => Finset.mem_Icc.2 ⟨Finset.min'_le _ _ hn, Finset.le_max' _ _ hn⟩
  a_mem := Finset.min'_mem _ _
  M_mem := Finset.max'_mem _ _
  gap := fun x hx hxM => h.toGap2CE.holes_isolated x hx hxM
  mass := h.sum_one

@[simp] theorem ofCounterexample_A {A : Finset ℕ} (h : Erdos287Counterexample A) :
    (ofCounterexample h).A = A := rfl

theorem ofCounterexample_one_lt_a {A : Finset ℕ} (h : Erdos287Counterexample A) :
    1 < (ofCounterexample h).a := h.one_lt _ (Finset.min'_mem A h.nonempty)

/-! ## Exact mass versus weaker surrogates -/

/-- A weaker *valuation surrogate* for exact mass at a finite set of primes `S`: the reduced
denominator of the reciprocal mass is coprime to every `p ∈ S`.  This is strictly weaker
than exact mass one (see `surrogate_not_exact` in `RegressionFixtures.lean`). -/
def ValuationSurrogate (A : Finset ℕ) (S : Finset ℕ) : Prop :=
  ∀ p ∈ S, ¬ p ∣ (∑ n ∈ A, (1 : ℚ) / n).den

/-- Exact mass implies every valuation surrogate. -/
theorem exact_implies_surrogate {A : Finset ℕ} (h : ∑ n ∈ A, (1 : ℚ) / n = 1)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p ≠ 1) : ValuationSurrogate A S := by
  intro p hp
  rw [h]
  simpa using hS p hp

end Erdos287.PostV71V87
