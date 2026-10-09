import RequestProject.Erdos287.QSigma.Bridge

/-!
# Erdős #287 — post-`Q_Σ` bank, §17 (row lemma), §18 (V60) and §19: diameter–primary cap,
contact defects

**Status: BANK (proved in Lean).**  No historical novelty is claimed for the diameter cap.

For a counterexample `A` with `a = min A`, `M = max A`:

* `diameter_primary_cap` — for every selected `n` and every prime power `p^r ∣ n` (`r ≥ 1`),
  `p^r ≤ M - a`;
* `dvd_lcm_of_diameter` — hence `n ∣ lcm(1, …, M - a)`;
* `top_strip_omitted` — every prime power in `(M - a, M]` is omitted;
* `large_prime_row_card_ge_three` — a nonempty row `{n ∈ A : p ∣ n}` of a prime with
  `2M < p²` has at least three selected denominators;
* `defect_contradiction` — a contact `(n, n+1)` inside `[a, M]` with both endpoints omitted
  (`I_e(A) = 1`) contradicts the gap-two condition;
* `ContactDefect287` — the uniform defect assertion (**defined, NOT asserted**);
  `erdos287_of_ContactDefect287` shows it would imply #287 outright.
-/

open scoped BigOperators

namespace Erdos287.PostQSigma

open Erdos287 Erdos287.ExactSource

variable {A : Finset ℕ}

/-- **Diameter–primary cap.** -/
theorem diameter_primary_cap (h : Erdos287Counterexample A) {n p r : ℕ} (hn : n ∈ A)
    (hp : p.Prime) (hr : 1 ≤ r) (hdvd : p ^ r ∣ n) :
    p ^ r ≤ A.max' h.nonempty - A.min' h.nonempty := by
  classical
  have hpos : ∀ x ∈ A, 0 < x := fun x hx => by have := h.one_lt x hx; omega
  have hn0 : n ≠ 0 := (hpos n hn).ne'
  have hvn : r ≤ n.factorization p := (hp.pow_dvd_iff_le_factorization hn0).1 hdvd
  have hle : n.factorization p ≤ topExp A p :=
    Finset.le_sup (f := fun x => Nat.factorization x p) hn
  have he : 1 ≤ topExp A p := by omega
  by_contra hcon
  push_neg at hcon
  -- the top layer has at most one element
  have hsub : ∀ x ∈ topLayer A p, ∀ y ∈ topLayer A p, x = y := by
    intro x hx y hy
    obtain ⟨hxA, hxe⟩ := mem_topLayer.1 hx
    obtain ⟨hyA, hye⟩ := mem_topLayer.1 hy
    have hdx : p ^ topExp A p ∣ x :=
      (hp.pow_dvd_iff_le_factorization (hpos x hxA).ne').2 hxe.ge
    have hdy : p ^ topExp A p ∣ y :=
      (hp.pow_dvd_iff_le_factorization (hpos y hyA).ne').2 hye.ge
    have hpr : p ^ r ≤ p ^ topExp A p := Nat.pow_le_pow_right hp.pos (by omega)
    have hx1 := Finset.min'_le A x hxA
    have hx2 := Finset.le_max' A x hxA
    have hy1 := Finset.min'_le A y hyA
    have hy2 := Finset.le_max' A y hyA
    by_contra hxy
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · have : p ^ topExp A p ∣ y - x := Nat.dvd_sub hdy hdx
      have := Nat.le_of_dvd (by omega) this
      omega
    · have : p ^ topExp A p ∣ x - y := Nat.dvd_sub hdx hdy
      have := Nat.le_of_dvd (by omega) this
      omega
  have hne : (topLayer A p).Nonempty := by
    obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup A h.nonempty (fun x => Nat.factorization x p)
    exact ⟨x, mem_topLayer.2 ⟨hx, hxe.symm⟩⟩
  have hcard : (topLayer A p).card = 1 := by
    obtain ⟨x, hx⟩ := hne
    rw [Finset.card_eq_one]
    exact ⟨x, Finset.eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy => hsub y hy x hx⟩⟩
  exact topLayer_card_ne_one A p hp hpos h.sum_one he hcard

/-- **Every selected denominator divides `lcm(1, …, M - a)`.** -/
theorem dvd_lcm_of_diameter (h : Erdos287Counterexample A) {n : ℕ} (hn : n ∈ A) :
    n ∣ (Finset.Icc 1 (A.max' h.nonempty - A.min' h.nonempty)).lcm id := by
  have hn0 : n ≠ 0 := by have := h.one_lt n hn; omega
  set L := (Finset.Icc 1 (A.max' h.nonempty - A.min' h.nonempty)).lcm id
  have hL0 : L ≠ 0 := by
    intro hL
    rw [Finset.lcm_eq_zero_iff] at hL
    obtain ⟨x, hx, hx0⟩ := hL
    simp only [Finset.mem_Icc, id] at hx hx0; omega
  rw [← Nat.factorization_prime_le_iff_dvd hn0 hL0]
  intro p hp
  set k := n.factorization p
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk]; exact Nat.zero_le _
  · have hpk : p ^ k ∣ n := Nat.ordProj_dvd n p
    have hcap := diameter_primary_cap h hn hp hk hpk
    have hmem : p ^ k ∈ Finset.Icc 1 (A.max' h.nonempty - A.min' h.nonempty) :=
      Finset.mem_Icc.2 ⟨Nat.one_le_pow _ _ hp.pos, hcap⟩
    have : p ^ k ∣ L := Finset.dvd_lcm (f := id) hmem
    exact (hp.pow_dvd_iff_le_factorization hL0).1 this

/-- **Top strip**: every prime power `q = p^r` (`r ≥ 1`) with `M - a < q` is omitted. -/
theorem top_strip_omitted (h : Erdos287Counterexample A) {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hq : A.max' h.nonempty - A.min' h.nonempty < p ^ r) : p ^ r ∉ A := fun hmem =>
  absurd (diameter_primary_cap h hmem hp hr dvd_rfl) (not_le.2 hq)

/-- **Small-support row lemma**: if `2M < p²` and some selected denominator is divisible by
`p`, then at least three selected denominators are divisible by `p`. -/
theorem large_prime_row_card_ge_three (h : Erdos287Counterexample A) {p : ℕ} (hp : p.Prime)
    (hp2 : 2 * A.max' h.nonempty < p ^ 2) (hrow : (A.filter (fun n => p ∣ n)).Nonempty) :
    3 ≤ (A.filter (fun n => p ∣ n)).card := by
  classical
  have hpos : ∀ x ∈ A, 0 < x := fun x hx => by have := h.one_lt x hx; omega
  set M := A.max' h.nonempty
  -- every valuation is at most `1`
  have hv1 : ∀ x ∈ A, x.factorization p ≤ 1 := by
    intro x hx
    by_contra hc; push_neg at hc
    have : p ^ 2 ∣ x := (hp.pow_dvd_iff_le_factorization (hpos x hx).ne').2 hc
    have := Nat.le_of_dvd (hpos x hx) this
    have := Finset.le_max' A x hx
    omega
  obtain ⟨n, hn⟩ := hrow
  obtain ⟨hnA, hpn⟩ := Finset.mem_filter.1 hn
  have hvn : 1 ≤ n.factorization p := (hp.dvd_iff_one_le_factorization (hpos n hnA).ne').1 hpn
  have he : topExp A p = 1 := le_antisymm (Finset.sup_le (fun x hx => hv1 x hx))
    (le_trans hvn (Finset.le_sup (f := fun x => Nat.factorization x p) hnA))
  have hlayer : topLayer A p = A.filter (fun n => p ∣ n) := by
    ext x
    rw [mem_topLayer, Finset.mem_filter, he]
    constructor
    · rintro ⟨hx, hx1⟩
      exact ⟨hx, (hp.dvd_iff_one_le_factorization (hpos x hx).ne').2 hx1.ge⟩
    · rintro ⟨hx, hpx⟩
      exact ⟨hx, le_antisymm (hv1 x hx) ((hp.dvd_iff_one_le_factorization (hpos x hx).ne').1 hpx)⟩
  have he1 : 1 ≤ topExp A p := he.ge
  have hne1 := topLayer_card_ne_one A p hp hpos h.sum_one he1
  rw [hlayer] at hne1
  by_contra hlt
  push_neg at hlt
  have hc2 : (A.filter (fun n => p ∣ n)).card = 2 := by
    have : 0 < (A.filter (fun n => p ∣ n)).card := Finset.card_pos.2 ⟨n, hn⟩
    omega
  obtain ⟨x, y, hxy, hxyeq⟩ := Finset.card_eq_two.1 hc2
  have h2 := topLayer_two_obstruction A p hp hpos h.sum_one he1 (hlayer.trans hxyeq) hxy
  have hxA : x ∈ A := (Finset.mem_filter.1 (hxyeq ▸ Finset.mem_insert_self x {y})).1
  have hyA : y ∈ A := (Finset.mem_filter.1 (hxyeq ▸ Finset.mem_insert_of_mem
    (Finset.mem_singleton_self y))).1
  have hfx : x.factorization p = 1 := by
    have := (mem_topLayer.1 ((hlayer.trans hxyeq) ▸ Finset.mem_insert_self x {y})).2
    rw [this, he]
  have hfy : y.factorization p = 1 := by
    have := (mem_topLayer.1 ((hlayer.trans hxyeq) ▸ Finset.mem_insert_of_mem
      (Finset.mem_singleton_self y))).2
    rw [this, he]
  rw [hfx, hfy, pow_one] at h2
  have hxM := Finset.le_max' A x hxA
  have hyM := Finset.le_max' A y hyA
  have hxle : x / p * p ≤ x := Nat.div_mul_le_self x p
  have hyle : y / p * p ≤ y := Nat.div_mul_le_self y p
  have hsum_pos : 0 < x / p + y / p := by
    have hpx : p ∣ x := (hp.dvd_iff_one_le_factorization (hpos x hxA).ne').2 hfx.ge
    obtain ⟨c, rfl⟩ := hpx
    have : 0 < c := by
      rcases Nat.eq_zero_or_pos c with hc | hc
      · have := hpos _ hxA; rw [hc, mul_zero] at this; omega
      · exact hc
    rw [Nat.mul_div_cancel_left c hp.pos]; exact Nat.add_pos_left this _
  have hle := Nat.le_of_dvd hsum_pos h2
  have : p * p ≤ (x / p + y / p) * p := Nat.mul_le_mul_right p hle
  nlinarith

/-! ## Contact defects -/

/-- `I_e(A) = 1`: both endpoints of the contact `(n, n+1)` are omitted. -/
def Defect (A : Finset ℕ) (n : ℕ) : Prop := n ∉ A ∧ n + 1 ∉ A

/-- **A defect inside `[a, M]` contradicts the gap-two condition.** -/
theorem defect_contradiction (h : Erdos287Counterexample A) {n : ℕ}
    (hn : A.min' h.nonempty ≤ n) (hn1 : n + 1 ≤ A.max' h.nonempty) (hd : Defect A n) : False :=
  holes_isolated h hn hn1 hd.1 hd.2

/-- **`ContactDefect287` (DEFINED, NOT ASSERTED).**  Every hypothetical counterexample has a
supplied contact `n` (from the family `contacts M`) inside `[a, M]` with `I_e(A) = 1`. -/
def ContactDefect287 (contacts : ℕ → Finset ℕ) : Prop :=
  ∀ A : Finset ℕ, ∀ h : Erdos287Counterexample A, ∃ n ∈ contacts (A.max' h.nonempty),
    A.min' h.nonempty ≤ n ∧ n + 1 ≤ A.max' h.nonempty ∧ Defect A n

/-- `ContactDefect287` would settle #287 outright (it is as strong as the problem). -/
theorem erdos287_of_ContactDefect287 {contacts : ℕ → Finset ℕ}
    (hcd : ContactDefect287 contacts) : ∀ A : Finset ℕ, ¬ Erdos287Counterexample A := by
  intro A h
  obtain ⟨n, -, h1, h2, hd⟩ := hcd A h
  exact defect_contradiction h h1 h2 hd

end Erdos287.PostQSigma
