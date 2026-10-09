import RequestProject.Erdos287.PostV71V87.RepairedRecurrence

/-!
# Erdős #287 — V86/V87 physical consequences

* `Word.card_internalMultiples_ge` — the window contains at least `⌊D/d⌋ − 1` interior
  multiples of `d`;
* `Word.guard_at_internal_qstar` — the literal pattern `(x_{y−1}, x_y, x_{y+1}) = (1,0,1)` at
  every interior multiple `y` of `q_*`;
* `Word.disjoint_guards`, `Word.exists_disjoint_guard_family` — pairwise-disjoint guard
  triples: at least `⌊D/(2 q_*)⌋ − 1` of them always, and `⌊D/q_*⌋ − 1` when `q_* ≥ 3`;
* `many_disjoint_guards` — combined with the repaired recurrence theorem: the number of
  pairwise-disjoint guard triples is `≥ c · log D log log D / log log log D − 2`;
* `Word.carrier_reserve` — for every non-exceptional prime `p` with `p² ≤ D`:
  `P_p ≥ p` and `P_p⁴ > D` (i.e. `P_p > D^{1/4}`); **no largeness condition is needed**, and
  only `P_p ≥ p` (not the unsupported strict `P_p > p`) is claimed;
* `Word.carrier_overlap_le_four` — under `M⁴ < (D+1)⁵` an element lies in at most four such
  carrier sets; `ExactWord.overlap_condition` shows the condition holds for exact words with
  `a > 1`, `M ≥ 34`;
* `ExactWord.carrier_union_lower` — `#E ≤ 2 · |⋃_{p ∈ E} carrier p|` for any finite set `E` of
  non-exceptional primes with `p² ≤ D`.
-/

open scoped BigOperators

namespace Erdos287.PostV71V87

/-- Pairwise coprime divisors: their product divides. -/
theorem prod_dvd_of_pairwise_coprime {s : Finset ℕ} (f : ℕ → ℕ) {n : ℕ}
    (hcop : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Nat.Coprime (f a) (f b)) (hd : ∀ a ∈ s, f a ∣ n) :
    ∏ a ∈ s, f a ∣ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h1 : Nat.Coprime (f a) (∏ b ∈ s, f b) := by
      refine Nat.Coprime.prod_right (fun b hb => ?_)
      exact hcop a (Finset.mem_insert_self _ _) b (Finset.mem_insert_of_mem hb)
        (fun h => ha (h ▸ hb))
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd h1 (hd a (Finset.mem_insert_self _ _)) ?_
    exact ih (fun x hx y hy hxy => hcop x (Finset.mem_insert_of_mem hx) y
      (Finset.mem_insert_of_mem hy) hxy) (fun x hx => hd x (Finset.mem_insert_of_mem hx))

/-- The guard triple centred at `y`. -/
def guardTriple (y : ℕ) : Finset ℕ := {y - 1, y, y + 1}

namespace Word

variable (W : Word)

/-- Interior multiples of `d` in the window. -/
def internalMultiples (d : ℕ) : Finset ℕ := (Finset.Ioo W.a W.M).filter (fun y => d ∣ y)

/-- **Count of interior multiples.**  `⌊D/d⌋ ≤ #(interior multiples of d) + 1`. -/
theorem card_internalMultiples_ge {d : ℕ} (hd : 1 ≤ d) :
    W.D / d ≤ (W.internalMultiples d).card + 1 := by
  set k := W.D / d
  have hinj : Set.InjOn (fun i => d * (W.a / d + i)) (Finset.Icc 1 (k - 1) : Set ℕ) := by
    intro i _ j _ h
    simp only at h
    have := Nat.eq_of_mul_eq_mul_left (by omega) h
    omega
  have hmaps : ∀ i ∈ Finset.Icc 1 (k - 1), d * (W.a / d + i) ∈ W.internalMultiples d := by
    intro i hi
    obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi
    simp only [internalMultiples, Finset.mem_filter, Finset.mem_Ioo]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
    · have h1 := Nat.mod_add_div W.a d
      have h2 := Nat.mod_lt W.a (show d > 0 by omega)
      have h3 : d * i ≥ d := by nlinarith
      rw [mul_add]; omega
    · have h1 := Nat.mod_add_div W.a d
      have h4 : d * k ≤ W.D := Nat.mul_div_le _ _
      have h5 : d * i ≤ d * (k - 1) := Nat.mul_le_mul_left _ hik
      have h6 : d * (k - 1) + d = d * k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · omega
        · rw [← Nat.mul_succ]; congr 1; omega
      have h7 : W.D = W.M - W.a := rfl
      have := W.a_le_M
      rw [mul_add]; omega
  have := Finset.card_le_card_of_injOn _
    (fun i hi => Finset.mem_coe.2 (hmaps i (Finset.mem_coe.1 hi))) hinj
  simp at this
  omega

/-- **Guard pattern at interior `q_*`-multiples.** -/
theorem guard_at_internal_qstar {y : ℕ} (hy : y ∈ W.internalMultiples W.qstar) :
    W.x (y - 1) = true ∧ W.x y = false ∧ W.x (y + 1) = true := by
  simp only [internalMultiples, Finset.mem_filter, Finset.mem_Ioo] at hy
  exact W.guard_pattern W.qstar_absent hy.2 ⟨hy.1.1.le, hy.1.2.le⟩

/-- Guard triples at distinct positive multiples of `d ≥ 3` are disjoint. -/
theorem disjoint_guards {d y y' : ℕ} (hd : 3 ≤ d) (hy : d ∣ y) (hy' : d ∣ y') (hne : y ≠ y')
    (h1 : 1 ≤ y) (h1' : 1 ≤ y') : Disjoint (guardTriple y) (guardTriple y') := by
  have hsep : y + 3 ≤ y' ∨ y' + 3 ≤ y := by
    rcases lt_or_gt_of_ne hne with h | h
    · left
      have := Nat.le_of_dvd (by omega) (Nat.dvd_sub hy' hy)
      omega
    · right
      have := Nat.le_of_dvd (by omega) (Nat.dvd_sub hy hy')
      omega
  rw [Finset.disjoint_left]
  intro z hz hz'
  simp only [guardTriple, Finset.mem_insert, Finset.mem_singleton] at hz hz'
  omega

/-- Interior multiples are positive. -/
theorem pos_of_mem_internalMultiples {d y : ℕ} (hy : y ∈ W.internalMultiples d) : 1 ≤ y := by
  simp only [internalMultiples, Finset.mem_filter, Finset.mem_Ioo] at hy
  omega

/-- **Pairwise-disjoint guard triples.**  There is a family `Y` of interior `q_*`-multiples
whose guard triples are pairwise disjoint, with `⌊D/(2 q_*)⌋ ≤ |Y| + 1`; if `q_* ≥ 3` one may
take all interior multiples, with `⌊D/q_*⌋ ≤ |Y| + 1`. -/
theorem exists_disjoint_guard_family :
    ∃ Y ⊆ W.internalMultiples W.qstar,
      (Y : Set ℕ).PairwiseDisjoint guardTriple ∧ W.D / (2 * W.qstar) ≤ Y.card + 1 ∧
      (3 ≤ W.qstar → W.D / W.qstar ≤ Y.card + 1) := by
  have hq := W.one_lt_qstar
  by_cases h3 : 3 ≤ W.qstar
  · refine ⟨W.internalMultiples W.qstar, Finset.Subset.refl _, ?_, ?_, fun _ => ?_⟩
    · intro y hy y' hy' hne
      have hd := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
      have hd' := (Finset.mem_filter.1 (Finset.mem_coe.1 hy')).2
      exact disjoint_guards h3 hd hd' hne (W.pos_of_mem_internalMultiples hy)
        (W.pos_of_mem_internalMultiples hy')
    · exact le_trans (Nat.div_le_div_left (by omega) (by omega))
        (W.card_internalMultiples_ge (by omega))
    · exact W.card_internalMultiples_ge (by omega)
  · refine ⟨W.internalMultiples (2 * W.qstar), ?_, ?_, W.card_internalMultiples_ge (by omega),
      fun h => absurd h h3⟩
    · intro y hy
      simp only [internalMultiples, Finset.mem_filter] at hy ⊢
      exact ⟨hy.1, dvd_trans (dvd_mul_left _ _) hy.2⟩
    · intro y hy y' hy' hne
      have hd := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
      have hd' := (Finset.mem_filter.1 (Finset.mem_coe.1 hy')).2
      exact disjoint_guards (by omega) hd hd' hne (W.pos_of_mem_internalMultiples hy)
        (W.pos_of_mem_internalMultiples hy')

/-! ## Carrier reserve -/

/-- **Carrier reserve (V86/V87).**  For every non-exceptional prime `p` with `p² ≤ D`:
`P_p ≥ p` and `P_p⁴ > D`.  No largeness assumption is needed; only `P_p ≥ p` is claimed. -/
theorem carrier_reserve {p : ℕ} (hp : p.Prime) (hpD : p * p ≤ W.D) (hne : ¬ W.Exceptional p) :
    p ≤ W.P p ∧ W.D < W.P p ^ 4 := by
  have hact : W.Active p := by
    by_contra h
    apply hne
    unfold Exceptional
    rw [W.Q_eq_self_of_not_active h]; exact hpD
  have hPp := W.le_P_of_active hp hact
  refine ⟨hPp, ?_⟩
  have hQ : W.D < W.Q p * W.Q p := by unfold Exceptional at hne; omega
  rw [W.Q_eq_mul] at hQ
  by_contra hc
  push_neg at hc
  by_cases h4 : W.D < p ^ 4
  · have : p ^ 4 ≤ W.P p ^ 4 := Nat.pow_le_pow_left hPp 4
    omega
  · push_neg at h4
    have h1 : (p * W.P p * (p * W.P p)) ^ 2 = p ^ 4 * W.P p ^ 4 := by ring
    have h2 : p ^ 4 * W.P p ^ 4 ≤ W.D * W.D := Nat.mul_le_mul h4 hc
    have h3 : (W.D + 1) * (W.D + 1) ≤ (p * W.P p * (p * W.P p)) ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul hQ hQ
    nlinarith

/-- Maximal primary powers of distinct primes are coprime. -/
theorem P_coprime {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) :
    Nat.Coprime (W.P p) (W.P r) :=
  Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hr).2 hpr)

/-- The finite set of non-exceptional primes `p` with `p² ≤ D`. -/
noncomputable def reservePrimes : Finset ℕ :=
  (Finset.range (W.D + 1)).filter (fun p => p.Prime ∧ p * p ≤ W.D ∧ ¬ W.Exceptional p)

theorem mem_reservePrimes {p : ℕ} :
    p ∈ W.reservePrimes ↔ p.Prime ∧ p * p ≤ W.D ∧ ¬ W.Exceptional p := by
  unfold reservePrimes
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have := h.1.two_le
    nlinarith [h.2.1]

/-- **At most four overlaps.**  If `M⁴ < (D+1)⁵`, every selected element lies in at most four
carrier sets of reserve primes. -/
theorem carrier_overlap_le_four (hMD : W.M ^ 4 < (W.D + 1) ^ 5) {n : ℕ} (hn : n ∈ W.A) :
    (W.reservePrimes.filter (fun p => n ∈ W.carrier p)).card ≤ 4 := by
  set S := W.reservePrimes.filter (fun p => n ∈ W.carrier p)
  have hdvd : ∏ p ∈ S, W.P p ∣ n := by
    refine prod_dvd_of_pairwise_coprime _ (fun p hp r hr hpr => ?_) (fun p hp => ?_)
    · have hp' := (W.mem_reservePrimes.1 (Finset.mem_filter.1 hp).1).1
      have hr' := (W.mem_reservePrimes.1 (Finset.mem_filter.1 hr).1).1
      exact W.P_coprime hp' hr' hpr
    · have := (Finset.mem_filter.1 hp).2
      simp only [carrier, Finset.mem_filter] at this
      exact this.2
  have hle : ∏ p ∈ S, W.P p ≤ W.M :=
    le_trans (Nat.le_of_dvd (W.pos_of_mem hn) hdvd) (W.mem_Icc hn).2
  have hlow : (W.D + 1) ^ S.card ≤ (∏ p ∈ S, W.P p) ^ 4 := by
    rw [← Finset.prod_pow, ← Finset.prod_const]
    refine Finset.prod_le_prod' (fun p hp => ?_)
    have h := W.mem_reservePrimes.1 (Finset.mem_filter.1 hp).1
    exact (W.carrier_reserve h.1 h.2.1 h.2.2).2
  have h4 : (∏ p ∈ S, W.P p) ^ 4 ≤ W.M ^ 4 := Nat.pow_le_pow_left hle 4
  by_contra hc
  push_neg at hc
  have h5 : (W.D + 1) ^ 5 ≤ (W.D + 1) ^ S.card := Nat.pow_le_pow_right (by omega) hc
  omega

end Word

namespace ExactWord

variable (W : ExactWord)

/-- The overlap condition `M⁴ < (D+1)⁵` holds for exact words with `a > 1`, `M ≥ 34`. -/
theorem overlap_condition (ha : 1 < W.a) (hM : 34 ≤ W.M) : W.M ^ 4 < (W.D + 1) ^ 5 := by
  have hs := W.two_mul_a_add_two_le ha (by omega)
  have hMD : W.M ≤ 2 * W.D := by unfold Word.D; omega
  have hD : 16 ≤ W.D := by unfold Word.D; omega
  have h1 : W.M ^ 4 ≤ (2 * W.D) ^ 4 := Nat.pow_le_pow_left hMD 4
  have h2 : (2 * W.D) ^ 4 ≤ W.D ^ 5 := by
    calc (2 * W.D) ^ 4 = 16 * W.D ^ 4 := by ring
      _ ≤ W.D * W.D ^ 4 := Nat.mul_le_mul_right _ hD
      _ = W.D ^ 5 := by ring
  have h3 : W.D ^ 5 < (W.D + 1) ^ 5 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  omega

/-- **Carrier-union lower bound.**  For exact words with `a > 1`, `M ≥ 34`:
`#reservePrimes ≤ 2 · |⋃_{p} carrier p|`. -/
theorem carrier_union_lower (ha : 1 < W.a) (hM : 34 ≤ W.M) :
    W.reservePrimes.card ≤ 2 * (W.reservePrimes.biUnion W.carrier).card := by
  classical
  set E := W.reservePrimes
  set U := E.biUnion W.carrier
  have hcond := W.overlap_condition ha hM
  have hsum := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun p n => n ∈ W.carrier p) (s := E) (t := U)
  have habove : ∀ p ∈ E, Finset.bipartiteAbove (fun p n => n ∈ W.carrier p) U p = W.carrier p := by
    intro p hp
    ext n
    simp only [Finset.bipartiteAbove, Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨Finset.mem_biUnion.2 ⟨p, hp, h⟩, h⟩
  have hlow : 2 * E.card ≤ ∑ p ∈ E, (W.carrier p).card := by
    rw [mul_comm, ← smul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ (fun p hp => ?_)
    have h := W.mem_reservePrimes.1 hp
    have hres := W.toWord.carrier_reserve h.1 h.2.1 h.2.2
    have hact : W.Active p := by
      by_contra hc
      have := W.le_P_of_active h.1
      unfold Word.Active at hc
      push_neg at hc
      have hP : W.P p = 1 := by unfold Word.P; rw [show W.maxVal p = 0 by omega]; simp
      have := h.1.two_le
      omega
    rw [W.carrier_eq_layer h.1]
    simpa using W.two_le_layer_card h.1 hact
  have hup : ∑ n ∈ U, (Finset.bipartiteBelow (fun p n => n ∈ W.carrier p) E n).card ≤ 4 * U.card := by
    rw [mul_comm, ← smul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ (fun n hn => ?_)
    obtain ⟨p, -, hpn⟩ := Finset.mem_biUnion.1 hn
    have hnA : n ∈ W.A := (Finset.mem_filter.1 hpn).1
    have := W.toWord.carrier_overlap_le_four hcond hnA
    simpa [Finset.bipartiteBelow] using this
  have hcongr : ∑ p ∈ E, (Finset.bipartiteAbove (fun p n => n ∈ W.carrier p) U p).card =
      ∑ p ∈ E, (W.carrier p).card := Finset.sum_congr rfl (fun p hp => by rw [habove p hp])
  omega

end ExactWord

/-- **Many disjoint guard triples (V87 consequence).**  There are `c > 0` and `M0` such that
every exact word with `a > 1`, `M ≥ M0` has a family of pairwise-disjoint guard triples, all
centred at interior multiples of `q_*`, of size at least
`c · log D · log log D / log log log D − 2`. -/
theorem many_disjoint_guards :
    ∃ c : ℝ, 0 < c ∧ ∃ M0 : ℕ, ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M →
      ∃ Y ⊆ W.internalMultiples W.qstar, (Y : Set ℕ).PairwiseDisjoint guardTriple ∧
        (∀ y ∈ Y, W.x (y - 1) = true ∧ W.x y = false ∧ W.x (y + 1) = true) ∧
        c * gRec (Real.log W.D) ≤ (Y.card : ℝ) + 2 := by
  obtain ⟨c, hc, M0, hrec⟩ := repaired_recurrence
  refine ⟨c / 2, by positivity, M0, fun W ha hM => ?_⟩
  have hq1 := W.one_lt_qstar
  obtain ⟨Y, hY, hdisj, hcount, -⟩ := W.exists_disjoint_guard_family
  refine ⟨Y, hY, hdisj, fun y hy => W.guard_at_internal_qstar (hY hy), ?_⟩
  have h1 := hrec W ha hM
  have hq : (0 : ℝ) < W.qstar := by exact_mod_cast (show 0 < W.qstar by have := W.one_lt_qstar; omega)
  have h2 : (W.D : ℝ) / (2 * W.qstar) - 1 ≤ (W.D / (2 * W.qstar) : ℕ) := by
    have := Nat.lt_div_mul_add (a := W.D) (show 0 < 2 * W.qstar by omega)
    have h3 : (W.D : ℝ) < (W.D / (2 * W.qstar) : ℕ) * (2 * W.qstar) + 2 * W.qstar := by
      exact_mod_cast this
    rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
    nlinarith
  have h4 : ((W.D / (2 * W.qstar) : ℕ) : ℝ) ≤ Y.card + 1 := by exact_mod_cast hcount
  have h5 : (W.D : ℝ) / (2 * W.qstar) = ((W.D : ℝ) / W.qstar) / 2 := by
    field_simp
  rw [h5] at h2
  have : c / 2 * gRec (Real.log W.D) = (c * gRec (Real.log W.D)) / 2 := by ring
  rw [this]
  linarith

end Erdos287.PostV71V87
