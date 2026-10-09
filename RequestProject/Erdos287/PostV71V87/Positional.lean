import RequestProject.Erdos287.PostV71V87.Model

/-!
# Erdős #287 — V84/V85 positional bank (exact, unconditional part)

The positional implication pattern

  absent modulus → forced omitted position → gap-two forced neighbour
    → singleton / conditioned prime-row rejection

is formalised here for exact words.  Everything in this file is **unconditional**
(no analytic input).  The analytic prime-supply deductions are in
`AnalyticProviders.lean`, behind explicit hypotheses.

Main results:

* `ExactWord.two_le_layer_card` — an active maximal primary layer has at least two elements
  (from the project's `topLayer_card_ne_one`);
* `ExactWord.P_le_D` — an active maximal primary power is at most `D = M - a`;
* `ExactWord.prime_le_D_of_active` — every active prime is at most `D`;
* `ExactWord.Q_two_le_D` — the dyadic ceiling satisfies `Q_2 ≤ M - a` (for `a > 1`);
* `ExactWord.not_active_of_lt_two_mul` — singleton prime-row rejection: a prime `ℓ` with
  `M < 2ℓ` has an empty row;
* `ExactWord.conditioned_row_rejection` — a layer that can contain at most one selected
  element cannot be the maximal layer;
* `ExactWord.positional_chain` — the full chain, ending in a contradiction.
-/

open scoped BigOperators

namespace Erdos287.PostV71V87

namespace ExactWord

variable (W : ExactWord)

theorem pos_of_mem' : ∀ n ∈ W.A, 0 < n := fun _ hn => W.pos_of_mem hn

/-- An active maximal primary layer is not a singleton. -/
theorem layer_card_ne_one {p : ℕ} (hp : p.Prime) (hact : W.Active p) :
    (W.layer p).card ≠ 1 :=
  topLayer_card_ne_one W.A p hp W.pos_of_mem' W.mass hact

/-- An active maximal primary layer has at least two elements. -/
theorem two_le_layer_card {p : ℕ} (hp : p.Prime) (hact : W.Active p) :
    2 ≤ (W.layer p).card := by
  have h1 := W.layer_card_ne_one hp hact
  have h2 := (W.layer_nonempty p).card_pos
  omega

/-- Two distinct elements of an active maximal layer. -/
theorem exists_two_in_layer {p : ℕ} (hp : p.Prime) (hact : W.Active p) :
    ∃ n₁ ∈ W.layer p, ∃ n₂ ∈ W.layer p, n₁ < n₂ := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (W.two_le_layer_card hp hact)
  rcases lt_or_gt_of_ne hxy with h | h
  · exact ⟨x, hx, y, hy, h⟩
  · exact ⟨y, hy, x, hx, h⟩

theorem mem_of_mem_layer {p n : ℕ} (h : n ∈ W.layer p) : n ∈ W.A :=
  (mem_topLayer.1 h).1

/-- An active maximal primary power is at most the window length `D = M - a`. -/
theorem P_le_D {p : ℕ} (hp : p.Prime) (hact : W.Active p) : W.P p ≤ W.D := by
  obtain ⟨n₁, h₁, n₂, h₂, hlt⟩ := W.exists_two_in_layer hp hact
  have d₁ := W.P_dvd_of_mem_layer hp h₁
  have d₂ := W.P_dvd_of_mem_layer hp h₂
  have hd : W.P p ∣ n₂ - n₁ := Nat.dvd_sub d₂ d₁
  have hle := Nat.le_of_dvd (by omega) hd
  have m₁ := W.mem_Icc (W.mem_of_mem_layer h₁)
  have m₂ := W.mem_Icc (W.mem_of_mem_layer h₂)
  unfold Word.D
  omega

/-- Every active prime is at most `D`. -/
theorem prime_le_D_of_active {p : ℕ} (hp : p.Prime) (hact : W.Active p) : p ≤ W.D :=
  le_trans (W.le_P_of_active hp hact) (W.P_le_D hp hact)

/-- Primes beyond the window length have empty rows. -/
theorem not_active_of_D_lt {p : ℕ} (hp : p.Prime) (h : W.D < p) : ¬ W.Active p :=
  fun hact => by have := W.prime_le_D_of_active hp hact; omega

/-- A selected element divisible by a prime makes that prime active. -/
theorem active_of_dvd {p n : ℕ} (hp : p.Prime) (hn : n ∈ W.A) (hd : p ∣ n) : W.Active p := by
  have hn0 : n ≠ 0 := (W.pos_of_mem hn).ne'
  have h1 : 1 ≤ n.factorization p := (hp.dvd_iff_one_le_factorization hn0).1 hd
  exact le_trans h1 (W.v_le_maxVal hn p)

/-- Elements of an active maximal layer are divisible by the prime. -/
theorem prime_dvd_of_mem_layer {p n : ℕ} (hp : p.Prime) (hact : W.Active p)
    (h : n ∈ W.layer p) : p ∣ n :=
  Nat.dvd_trans (by unfold Word.P; exact dvd_pow_self p (by unfold Word.Active at hact; omega))
    (W.P_dvd_of_mem_layer hp h)

/-- **Singleton prime-row rejection.**  A prime `ℓ` with `M < 2ℓ` has an empty row: the only
possible selected multiple would be `ℓ` itself, giving a singleton maximal layer. -/
theorem not_active_of_lt_two_mul {ℓ : ℕ} (hℓ : ℓ.Prime) (h : W.M < 2 * ℓ) :
    ¬ W.Active ℓ := by
  intro hact
  obtain ⟨n₁, h₁, n₂, h₂, hlt⟩ := W.exists_two_in_layer hℓ hact
  have d₁ := W.prime_dvd_of_mem_layer hℓ hact h₁
  have d₂ := W.prime_dvd_of_mem_layer hℓ hact h₂
  obtain ⟨k₁, hk₁⟩ := d₁
  obtain ⟨k₂, hk₂⟩ := d₂
  have m₁ := W.mem_Icc (W.mem_of_mem_layer h₁)
  have m₂ := W.mem_Icc (W.mem_of_mem_layer h₂)
  have p₁ := W.pos_of_mem (W.mem_of_mem_layer h₁)
  have hℓ2 := hℓ.two_le
  have hk1 : 1 ≤ k₁ := by
    rcases Nat.eq_zero_or_pos k₁ with h0 | h0
    · subst h0; simp at hk₁; omega
    · exact h0
  have hk2 : k₂ ≤ 1 := by
    by_contra hc
    push_neg at hc
    have : ℓ * 2 ≤ ℓ * k₂ := Nat.mul_le_mul_left ℓ hc
    omega
  have : ℓ * k₁ < ℓ * k₂ := by omega
  have := lt_of_mul_lt_mul_left this
  omega

/-- A prime `ℓ` with `M < 2ℓ` is never selected. -/
theorem prime_not_mem_of_lt_two_mul {ℓ : ℕ} (hℓ : ℓ.Prime) (h : W.M < 2 * ℓ) : ℓ ∉ W.A :=
  fun hm => W.not_active_of_lt_two_mul hℓ h (W.active_of_dvd hℓ hm (dvd_refl ℓ))

/-- **Conditioned prime-row rejection.**  If, for some `k ≥ 1`, every selected element of
exact `p`-adic valuation `k` lies in a set `T` with at most one element (e.g. because all
other candidate positions are forced omissions), then `k` is not the maximal valuation. -/
theorem conditioned_row_rejection {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (T : Finset ℕ)
    (hT : T.card ≤ 1) (hcover : ∀ n ∈ W.A, Word.v p n = k → n ∈ T) : W.maxVal p ≠ k := by
  intro hmax
  have hact : W.Active p := by unfold Word.Active; omega
  have hsub : W.layer p ⊆ T := by
    intro n hn
    have h := mem_topLayer.1 hn
    exact hcover n h.1 (by simp only [Word.v]; rw [h.2]; exact hmax)
  have := Finset.card_le_card hsub
  have := W.two_le_layer_card hp hact
  omega

/-- **Positional chain.**  Let `d` be an absent modulus and `y` a multiple of `d` in the
window.  Then `y` is omitted, both neighbours are selected, and therefore neither neighbour
can be a prime `ℓ` with `M < 2ℓ`. -/
theorem positional_chain {d y ℓ : ℕ} (hd : W.Absent d) (hdy : d ∣ y)
    (hy : W.a ≤ y ∧ y ≤ W.M) (hℓ : ℓ.Prime) (hℓM : W.M < 2 * ℓ)
    (hl : ℓ + 1 = y ∨ ℓ = y + 1) : False := by
  have hom := W.forced_omitted hd hdy
  have hn := W.neighbours_of_omitted hy hom
  rcases hl with h | h
  · exact W.prime_not_mem_of_lt_two_mul hℓ hℓM (by
      have : ℓ = y - 1 := by omega
      rw [this]; exact hn.1)
  · exact W.prime_not_mem_of_lt_two_mul hℓ hℓM (h ▸ hn.2)

/-! ## The dyadic ceiling `Q_2 ≤ M - a` -/

/-- Two distinct odd multiples of `2^e` differ by at least `2^(e+1)`. -/
theorem two_pow_succ_le_sub {e n₁ n₂ : ℕ} (hlt : n₁ < n₂)
    (h₁ : n₁.factorization 2 = e) (h₂ : n₂.factorization 2 = e) (hn₁ : n₁ ≠ 0) :
    2 ^ (e + 1) ≤ n₂ - n₁ := by
  have hn₂ : n₂ ≠ 0 := by omega
  have e₁ := Nat.ordProj_mul_ordCompl_eq_self n₁ 2
  have e₂ := Nat.ordProj_mul_ordCompl_eq_self n₂ 2
  have o₁ := Nat.not_dvd_ordCompl Nat.prime_two hn₁
  have o₂ := Nat.not_dvd_ordCompl Nat.prime_two hn₂
  rw [h₁] at e₁ o₁
  rw [h₂] at e₂ o₂
  set m₁ := n₁ / 2 ^ e
  set m₂ := n₂ / 2 ^ e
  have hm : m₁ < m₂ := by
    by_contra hc; push_neg at hc
    have : 2 ^ e * m₂ ≤ 2 ^ e * m₁ := Nat.mul_le_mul_left _ hc
    omega
  have hev : 2 ∣ m₂ - m₁ := by omega
  obtain ⟨t, ht⟩ := hev
  have ht1 : 1 ≤ t := by omega
  have : n₂ - n₁ = 2 ^ e * (m₂ - m₁) := by
    rw [Nat.mul_sub, e₁, e₂]
  rw [this, ht, pow_succ]
  exact Nat.mul_le_mul_left _ (by omega)

/-- **`Q_2 ≤ M - a`.**  For an exact word with `a > 1` the dyadic primary ceiling is at most
the window length. -/
theorem Q_two_le_D (ha : 1 < W.a) : W.Q 2 ≤ W.D := by
  by_cases hact : W.Active 2
  · obtain ⟨n₁, h₁, n₂, h₂, hlt⟩ := W.exists_two_in_layer Nat.prime_two hact
    have l₁ := mem_topLayer.1 h₁
    have l₂ := mem_topLayer.1 h₂
    have := two_pow_succ_le_sub hlt l₁.2 l₂.2 (W.pos_of_mem l₁.1).ne'
    have m₁ := W.mem_Icc l₁.1
    have m₂ := W.mem_Icc l₂.1
    unfold Word.Q Word.D
    rw [add_comm]
    unfold Word.maxVal
    omega
  · rw [W.Q_eq_self_of_not_active hact]
    -- every selected element is odd; `a` and `M` are distinct odd numbers
    have hodd : ∀ n ∈ W.A, ¬ 2 ∣ n := fun n hn hd => hact (W.active_of_dvd Nat.prime_two hn hd)
    have hce := W.toCounterexample ha
    have hcard := hce.card_ge
    have hne : W.a ≠ W.M := by
      intro h
      have hsub : W.A ⊆ {W.a} := by
        intro n hn
        have := W.mem_Icc hn
        simp; omega
      have := Finset.card_le_card hsub
      simp at this; omega
    have h1 := hodd _ W.a_mem
    have h2 := hodd _ W.M_mem
    have := W.a_le_M
    unfold Word.D
    omega

end ExactWord

end Erdos287.PostV71V87
