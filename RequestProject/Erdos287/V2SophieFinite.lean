import RequestProject.Erdos287.TopLayer
import RequestProject.Erdos287.Counterexample

/-!
# Erdős Problem #287 — the V2 finite route (top-layer only)

This file is **append-only**: no earlier statement is edited, weakened or deleted.

It rebuilds the plus/minus Sophie blockers on a strictly finite, top-layer-only footing.
The two controlling banked inputs are

* `Erdos287.topLayer_congruence` (with its singleton/pair corollaries
  `Erdos287.topLayer_card_ne_one` and `Erdos287.topLayer_two_obstruction`), and
* `Erdos287.Gap2CE.holes_isolated`.

Deliberately **not** used on this route:

* the analytic placement inequality `Erdos287.Gap2CE.exp_lower` (`e·(N-1) < M`) — replaced
  by the purely finite `Erdos287.Gap2CE.halfRange_min_le` (`N ≤ ⌊M/2⌋`);
* the numerator threshold `C` and `Erdos287.C_two` (`C 2 = 3`) — replaced by the direct
  top-layer obstruction `1 ≡ 0`, `2⁻¹ ≡ 0`, `1 + 2⁻¹ ≡ 0 (mod q)`.

Both remain in the bank as historical/redundant lemmas.
-/

open scoped BigOperators

namespace Erdos287

/-! ## Top-layer hole lemmas (no `C`, no analytic input) -/

/-- If every element of `A` is at most `M` and `M < q²`, then no element of `A` carries
`q`-adic valuation `≥ 2`, so the top exponent is at most `1`. -/
theorem topExp_le_one_of_lt_sq {A : Finset ℕ} {M q : ℕ} (hq : q.Prime)
    (hpos : ∀ a ∈ A, 0 < a) (hAM : ∀ a ∈ A, a ≤ M) (hsq : M < q * q) :
    topExp A q ≤ 1 := by
  refine Finset.sup_le fun a ha => ?_
  by_contra hcon
  push_neg at hcon
  have h2 : 2 ≤ Nat.factorization a q := hcon
  have hdvd : q ^ 2 ∣ a := (pow_dvd_pow q h2).trans (Nat.ordProj_dvd a q)
  have : q ^ 2 ≤ a := Nat.le_of_dvd (hpos a ha) hdvd
  have := hAM a ha
  nlinarith [sq_nonneg q]

/-- **Top-half prime hole.**  If `p` is a prime with `M/2 < p ≤ M` (written `M < 2p`), then
`p` is not a denominator: it would be an isolated top `p`-adic layer, i.e. a singleton,
which the top-layer congruence forbids. -/
theorem topHalf_prime_hole {A : Finset ℕ} {M p : ℕ} (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a) (hAM : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) (hM2 : M < 2 * p) :
    p ∉ A := by
  intro hpA
  -- every element of `A` with positive `p`-valuation equals `p`
  have honly : ∀ a ∈ A, 1 ≤ Nat.factorization a p → a = p := by
    intro a ha hv
    have hdvd : p ∣ a := by
      have := (pow_dvd_pow p hv).trans (Nat.ordProj_dvd a p)
      simpa using this
    obtain ⟨c, rfl⟩ := hdvd
    have hapos := hpos _ ha
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with rfl | h
      · simp at hapos
      · exact h
    have hle := hAM _ ha
    have hp2 := hp.two_le
    have hc2 : c < 2 := by nlinarith
    have : c = 1 := by omega
    simp [this]
  have hfp : Nat.factorization p p = 1 := hp.factorization_self
  have hle : topExp A p ≤ 1 := by
    refine Finset.sup_le fun a ha => ?_
    by_contra hcon
    push_neg at hcon
    have h1 : 1 ≤ Nat.factorization a p := by omega
    have : a = p := honly a ha h1
    subst this
    omega
  have hge : 1 ≤ topExp A p := by
    have : Nat.factorization p p ≤ topExp A p :=
      Finset.le_sup (f := fun a => Nat.factorization a p) hpA
    omega
  have htop : topExp A p = 1 := le_antisymm hle hge
  have hsingle : topLayer A p = {p} := by
    apply Finset.eq_singleton_iff_unique_mem.2
    refine ⟨mem_topLayer.2 ⟨hpA, by rw [hfp, htop]⟩, ?_⟩
    intro x hx
    obtain ⟨hxA, hxv⟩ := mem_topLayer.1 hx
    exact honly x hxA (by omega)
  exact topLayer_card_ne_one A p hp hpos hsum (by omega) (by rw [hsingle]; simp)

/-- **The `q` / `2q` hole pair.**  Let `q > 3` be prime with `M < q²` and `M < 3q`.  Then the
only multiples of `q` in `[1,M]` are `q` and `2q`, both of `q`-valuation exactly `1`; the
possible nonempty top layers are `{q}`, `{2q}`, `{q,2q}`, and the top-layer congruence kills
each (`1 ≡ 0`, `2⁻¹ ≡ 0`, `1 + 2⁻¹ ≡ 0 (mod q)`, the last forcing `q ∣ 3`).  Hence both `q`
and `2q` are holes. -/
theorem q_and_two_mul_q_holes {A : Finset ℕ} {M q : ℕ} (hq : q.Prime) (hq3 : 3 < q)
    (hpos : ∀ a ∈ A, 0 < a) (hAM : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) (hsq : M < q * q) (hM3 : M < 3 * q) :
    q ∉ A ∧ 2 * q ∉ A := by
  have hqnd2 : ¬ q ∣ 2 := by
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have hfq : Nat.factorization q q = 1 := hq.factorization_self
  have hf2q : Nat.factorization (2 * q) q = 1 := by
    rw [Nat.factorization_mul (by norm_num) hq.pos.ne']
    simp [hfq, Nat.factorization_eq_zero_of_not_dvd hqnd2]
  have hoq : ordCompl[q] q = 1 := by simp [hfq, Nat.div_self hq.pos]
  have ho2q : ordCompl[q] (2 * q) = 2 := by
    rw [hf2q, pow_one, Nat.mul_div_cancel _ hq.pos]
  -- the key: neither `q` nor `2q` can be a denominator
  have key : ¬ (q ∈ A ∨ 2 * q ∈ A) := by
    intro hmem
    have hle : topExp A q ≤ 1 := topExp_le_one_of_lt_sq hq hpos hAM hsq
    have hge : 1 ≤ topExp A q := by
      rcases hmem with h | h
      · have : Nat.factorization q q ≤ topExp A q :=
          Finset.le_sup (f := fun a => Nat.factorization a q) h
        omega
      · have : Nat.factorization (2 * q) q ≤ topExp A q :=
          Finset.le_sup (f := fun a => Nat.factorization a q) h
        omega
    have htop : topExp A q = 1 := le_antisymm hle hge
    -- the top layer is contained in `{q, 2q}`
    have hsub : topLayer A q ⊆ {q, 2 * q} := by
      intro x hx
      obtain ⟨hxA, hxv⟩ := mem_topLayer.1 hx
      have hdvd : q ∣ x := by
        have := (pow_dvd_pow q (by omega : 1 ≤ Nat.factorization x q)).trans
          (Nat.ordProj_dvd x q)
        simpa using this
      obtain ⟨c, rfl⟩ := hdvd
      have hcpos : 0 < c := by
        rcases Nat.eq_zero_or_pos c with rfl | h
        · have := hpos _ hxA; simp at this
        · exact h
      have hle' := hAM _ hxA
      have hq2 := hq.two_le
      have hc2 : c ≤ 2 := by nlinarith
      interval_cases c <;> simp [mul_comm]
    -- it is nonempty
    have hne : (topLayer A q).Nonempty := by
      rcases hmem with h | h
      · exact ⟨q, mem_topLayer.2 ⟨h, by rw [hfq, htop]⟩⟩
      · exact ⟨2 * q, mem_topLayer.2 ⟨h, by rw [hf2q, htop]⟩⟩
    have hcard1 : (topLayer A q).card ≠ 1 :=
      topLayer_card_ne_one A q hq hpos hsum (by omega)
    have hcardpos : 1 ≤ (topLayer A q).card := Finset.card_pos.2 hne
    have hpairne : q ≠ 2 * q := by omega
    have hcard2 : ({q, 2 * q} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hpairne]), Finset.card_singleton]
    have hcardle : (topLayer A q).card ≤ 2 := by
      have := Finset.card_le_card hsub
      omega
    have hcardeq : (topLayer A q).card = 2 := by omega
    have heq : topLayer A q = {q, 2 * q} :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have hdvd3 := topLayer_two_obstruction A q hq hpos hsum (by omega) heq hpairne
    rw [hoq, ho2q] at hdvd3
    have := Nat.le_of_dvd (by norm_num) hdvd3
    omega
  exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩

namespace Gap2CE

variable (ce : Gap2CE)

/-! ## Purely finite placement: `N ≤ ⌊M/2⌋` -/

/-- **Finite placement.**  For any gap-`≤2` counterexample with `M ≥ 2` we have
`N ≤ ⌊M/2⌋`.  (The hypothesis `2 ≤ M` is necessary: `A = {1}` satisfies every field of
`Gap2CE`, and there `N = 1 > 0 = ⌊M/2⌋`.)

Proof: if `2N > M` then `A ⊆ [N,M]` gives
`1 = ∑_{a∈A} 1/a ≤ 1/N + (M-N)/(N+1) ≤ 1/N + (N-1)/(N+1) < 1`. -/
theorem halfRange_min_le (hM : 2 ≤ ce.M) : ce.N ≤ ce.M / 2 := by
  by_contra hcon
  push_neg at hcon
  set n := ce.N with hn
  set m := ce.M with hm
  have hnm : n ≤ m := Finset.min'_le _ _ ce.M_mem
  have hn2 : 2 ≤ n := by omega
  have hlt : m < 2 * n := by omega
  -- `A ⊆ [n, m]`
  have hsubset : ce.A ⊆ Finset.Icc n m := fun x hx =>
    Finset.mem_Icc.2 ⟨Finset.min'_le _ _ hx, Finset.le_max' _ _ hx⟩
  have hsum1 : (1 : ℚ) ≤ ∑ x ∈ Finset.Icc n m, (1 : ℚ) / x := by
    calc (1 : ℚ) = ∑ a ∈ ce.A, (1 : ℚ) / a := ce.hsum.symm
      _ ≤ ∑ x ∈ Finset.Icc n m, (1 : ℚ) / x :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by positivity)
  -- split off the first term
  have hins : Finset.Icc n m = insert n (Finset.Icc (n + 1) m) := by
    ext x
    simp [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnotmem : n ∉ Finset.Icc (n + 1) m := by simp
  have hsplit : ∑ x ∈ Finset.Icc n m, (1 : ℚ) / x
      = 1 / n + ∑ x ∈ Finset.Icc (n + 1) m, (1 : ℚ) / x := by
    rw [hins, Finset.sum_insert hnotmem]
  have hcard : (Finset.Icc (n + 1) m).card = m - n := by
    rw [Nat.card_Icc]; omega
  have htail : ∑ x ∈ Finset.Icc (n + 1) m, (1 : ℚ) / x
      ≤ ((m - n : ℕ) : ℚ) * (1 / ((n : ℚ) + 1)) := by
    have hbound : ∀ x ∈ Finset.Icc (n + 1) m, (1 : ℚ) / x ≤ 1 / ((n : ℚ) + 1) := by
      intro x hx
      have hx' : n + 1 ≤ x := (Finset.mem_Icc.1 hx).1
      have : ((n : ℚ) + 1) ≤ (x : ℚ) := by exact_mod_cast hx'
      apply one_div_le_one_div_of_le (by positivity) this
    calc ∑ x ∈ Finset.Icc (n + 1) m, (1 : ℚ) / x
        ≤ ∑ _x ∈ Finset.Icc (n + 1) m, 1 / ((n : ℚ) + 1) :=
          Finset.sum_le_sum hbound
      _ = ((m - n : ℕ) : ℚ) * (1 / ((n : ℚ) + 1)) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hnq : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn2
  have hmn : ((m - n : ℕ) : ℚ) ≤ (n : ℚ) - 1 := by
    have h : (m - n : ℕ) + 1 ≤ n := by omega
    have h' : (((m - n : ℕ) + 1 : ℕ) : ℚ) ≤ (n : ℚ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hnpos : (0 : ℚ) < (n : ℚ) := by linarith
  have hfinal : ∑ x ∈ Finset.Icc n m, (1 : ℚ) / x < 1 := by
    rw [hsplit]
    have hstep : 1 / (n : ℚ) + ((m - n : ℕ) : ℚ) * (1 / ((n : ℚ) + 1)) < 1 := by
      have h1 : ((m - n : ℕ) : ℚ) * (1 / ((n : ℚ) + 1)) ≤ ((n : ℚ) - 1) / ((n : ℚ) + 1) := by
        rw [mul_one_div]
        gcongr
      have h2 : 1 / (n : ℚ) + ((n : ℚ) - 1) / ((n : ℚ) + 1) < 1 := by
        rw [div_add_div _ _ (by positivity) (by positivity), div_lt_one (by positivity)]
        nlinarith
      linarith
    linarith [htail]
  linarith

/-! ## The V2 plus/minus Sophie blockers -/

/-- A `q`/`2q` hole pair for the counterexample. -/
theorem holes_q_two_q {q : ℕ} (hq : q.Prime) (hq3 : 3 < q)
    (hsq : ce.M < q * q) (hM3 : ce.M < 3 * q) : q ∉ ce.A ∧ 2 * q ∉ ce.A :=
  q_and_two_mul_q_holes hq hq3 ce.hpos (fun a ha => Finset.le_max' _ _ ha) ce.hsum hsq hM3

/-- A top-half prime is a hole of the counterexample. -/
theorem hole_topHalf_prime {p : ℕ} (hp : p.Prime) (hM2 : ce.M < 2 * p) : p ∉ ce.A :=
  topHalf_prime_hole hp ce.hpos (fun a ha => Finset.le_max' _ _ ha) ce.hsum hM2

/-- **V2 plus Sophie blocker.**  `q > 3` prime, `p = 2q + 1` prime, `p ≤ M`, `M < 3q`,
`M < q²` ⟹ no gap-`≤2` counterexample.

Dependencies: `halfRange_min_le`, `q_and_two_mul_q_holes`, `topHalf_prime_hole`,
`holes_isolated`, and elementary `ℕ` inequalities.  Neither `exp_lower` nor `C` is used. -/
theorem v2_plus_sophie_blocker {q p : ℕ}
    (hq : q.Prime) (hq3 : 3 < q) (hp : p.Prime) (heq : p = 2 * q + 1)
    (hpM : p ≤ ce.M) (hM3 : ce.M < 3 * q) (hsq : ce.M < q * q) : False := by
  have h2q : 2 * q ∉ ce.A := (ce.holes_q_two_q hq hq3 hsq hM3).2
  have hph : p ∉ ce.A := ce.hole_topHalf_prime hp (by omega)
  have hM2 : 2 ≤ ce.M := by omega
  have hN : ce.N ≤ ce.M / 2 := ce.halfRange_min_le hM2
  have hN2q : ce.N ≤ 2 * q := by omega
  rcases ce.holes_isolated (2 * q) hN2q (by omega) with h | h
  · exact h2q h
  · exact hph (by rw [heq]; exact h)

/-- **V2 minus Sophie blocker.**  `q > 3` prime, `p = 2q - 1` prime (written `p + 1 = 2q`),
`p + 1 ≤ M`, `M < 3q`, `M < q²` ⟹ no gap-`≤2` counterexample.

The inequality `3q < 4q - 2 = 2p` needed for the top-half step follows from `q > 3`. -/
theorem v2_minus_sophie_blocker {q p : ℕ}
    (hq : q.Prime) (hq3 : 3 < q) (hp : p.Prime) (heq : p + 1 = 2 * q)
    (hpM : p + 1 ≤ ce.M) (hM3 : ce.M < 3 * q) (hsq : ce.M < q * q) : False := by
  have h2q : 2 * q ∉ ce.A := (ce.holes_q_two_q hq hq3 hsq hM3).2
  have hph : p ∉ ce.A := ce.hole_topHalf_prime hp (by omega)
  have hM2 : 2 ≤ ce.M := by omega
  have hN : ce.N ≤ ce.M / 2 := ce.halfRange_min_le hM2
  have hNp : ce.N ≤ p := by omega
  rcases ce.holes_isolated p hNp (by omega) with h | h
  · exact hph h
  · exact h2q (by rw [← heq]; exact h)

end Gap2CE

end Erdos287
