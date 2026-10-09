import RequestProject.Erdos287.PostV87V90R.ModelCompatibility

/-!
# Erdős #287 — post-V87 → V90R: bounded-cofactor row rigidity

**ERDŐS #287 REMAINS OPEN.  Everything here is unconditional.**

For `H ≥ 1` put `L_H = lcm(1, …, H)` and `B_H = ∑_{j=1}^H L_H / j` (a positive integer,
`BH_pos`).

`selRow_empty_of_bounded_cofactors`: in an exact word, if `p` is prime, `p > B_H`, and every
selected multiple of `p` is `p·j` with `1 ≤ j ≤ H`, then **no** selected denominator is divisible
by `p`.  The load-bearing arithmetic: with `J` the set of selected cofactors, the exact identity
`∑ 1/n = 1` multiplied by `p · L_H · ∏_{p ∤ n ∈ A} n` shows `p ∣ X := ∑_{j ∈ J} L_H/j`, while
`0 ≤ X ≤ B_H < p`; so `X = 0`, forcing `J = ∅`.

*Audit note.*  The prose hypothesis `p² > M` is **not needed** once the cofactor hypothesis is
stated; it is dropped.  The cofactor hypothesis itself follows from `M < p (H + 1)`
(`cofactor_bound_of_lt`, used in `selRow_empty_of_lt`).

`adjacent_empty_rows_contradiction`: two adjacent window positions `n, n+1` lying in empty
`p`- and `q`-rows contradict gap-two.  Packaged as `ContactWitness W` with
`ContactWitness.false`.
-/

open scoped BigOperators

namespace Erdos287.PostV87V90R

open Erdos287 Erdos287.PostV71V87

/-- `L_H = lcm(1, …, H)`. -/
def LH (H : ℕ) : ℕ := (Finset.Icc 1 H).lcm id

/-- `B_H = ∑_{j=1}^H L_H / j`. -/
def BH (H : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 H, LH H / j

theorem dvd_LH {H j : ℕ} (hj : j ∈ Finset.Icc 1 H) : j ∣ LH H := Finset.dvd_lcm hj

theorem LH_pos (H : ℕ) : 0 < LH H := by
  unfold LH
  rcases Nat.eq_zero_or_pos ((Finset.Icc 1 H).lcm id) with h | h
  · rw [Finset.lcm_eq_zero_iff] at h
    simp at h
  · exact h

/-- `B_H` is a positive integer for `H ≥ 1`. -/
theorem BH_pos {H : ℕ} (hH : 1 ≤ H) : 0 < BH H := by
  unfold BH
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 H := Finset.mem_Icc.2 ⟨le_rfl, hH⟩
  have := Finset.single_le_sum (f := fun j => LH H / j) (fun _ _ => Nat.zero_le _) h1
  simp only [Nat.div_one] at this
  exact lt_of_lt_of_le (LH_pos H) this

theorem one_le_LH_div {H j : ℕ} (hj : j ∈ Finset.Icc 1 H) : 1 ≤ LH H / j := by
  have hj1 := (Finset.mem_Icc.1 hj).1
  exact (Nat.one_le_div_iff (by omega)).2 (Nat.le_of_dvd (LH_pos H) (dvd_LH hj))

/-- Bounded cofactors follow from `M < p (H + 1)`. -/
theorem cofactor_bound_of_lt (W : Word) {p H : ℕ} (hM : W.M < p * (H + 1)) :
    ∀ n ∈ W.A, p ∣ n → ∃ j, 1 ≤ j ∧ j ≤ H ∧ n = p * j := by
  intro n hn hpn
  obtain ⟨j, rfl⟩ := hpn
  have hpos := W.pos_of_mem hn
  have hle := (W.mem_Icc hn).2
  refine ⟨j, ?_, ?_, rfl⟩
  · rcases Nat.eq_zero_or_pos j with h | h
    · rw [h] at hpos; simp at hpos
    · exact h
  · by_contra hc
    push_neg at hc
    have : p * (H + 1) ≤ p * j := Nat.mul_le_mul_left _ hc
    omega

/-- **Bounded-cofactor row rigidity.**  In an exact word, if `p` is prime, `p > B_H`, and every
selected multiple of `p` has the form `p·j` with `1 ≤ j ≤ H`, then the selected `p`-row is
empty. -/
theorem selRow_empty_of_bounded_cofactors (W : ExactWord) {p H : ℕ} (hp : p.Prime)
    (hpB : BH H < p) (hcof : ∀ n ∈ W.A, p ∣ n → ∃ j, 1 ≤ j ∧ j ≤ H ∧ n = p * j) :
    ∀ n ∈ W.A, ¬ p ∣ n := by
  classical
  set A1 := W.A.filter (fun n => ¬ p ∣ n) with hA1
  set A2 := W.A.filter (fun n => p ∣ n) with hA2
  set J := A2.image (fun n => n / p) with hJ
  have hp0 : 0 < p := hp.pos
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  -- cofactors lie in `[1, H]`
  have hJsub : J ⊆ Finset.Icc 1 H := by
    intro j hj
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hj
    obtain ⟨hnA, hpn⟩ := Finset.mem_filter.1 hn
    obtain ⟨k, hk1, hkH, rfl⟩ := hcof n hnA hpn
    rw [Nat.mul_div_cancel_left _ hp0]
    exact Finset.mem_Icc.2 ⟨hk1, hkH⟩
  have hinj : Set.InjOn (fun n => n / p) A2 := by
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.1 hx).2
    have hy' := (Finset.mem_filter.1 hy).2
    simp only at hxy
    rw [← Nat.div_mul_cancel hx', ← Nat.div_mul_cancel hy', hxy]
  -- split the exact mass
  have hsplit : ∑ n ∈ A1, (1 : ℚ) / n + ∑ n ∈ A2, (1 : ℚ) / n = 1 := by
    rw [hA1, hA2, add_comm, Finset.sum_filter_add_sum_filter_not]; exact W.mass
  have hA2J : ∑ n ∈ A2, (1 : ℚ) / n = (1 / p) * ∑ j ∈ J, (1 : ℚ) / j := by
    rw [hJ, Finset.sum_image hinj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hpn := (Finset.mem_filter.1 hn).2
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (W.pos_of_mem (Finset.mem_filter.1 hn).1).ne'
    have : (n : ℚ) = p * ((n / p : ℕ) : ℚ) := by
      rw [Nat.cast_div hpn hpQ]; field_simp
    have hq0 : ((n / p : ℕ) : ℚ) ≠ 0 := by
      intro h; rw [h, mul_zero] at this; exact hn0 this
    rw [this]; field_simp
  -- integer quantities
  set R := ∏ n ∈ A1, n with hR
  set L := LH H with hL
  set N1 := ∑ n ∈ A1, R / n with hN1
  set X := ∑ j ∈ J, L / j with hX
  have hRS : (R : ℚ) * ∑ n ∈ A1, (1 : ℚ) / n = N1 := by
    rw [hN1, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hdvd : n ∣ R := Finset.dvd_prod_of_mem _ hn
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (W.pos_of_mem (Finset.mem_filter.1 hn).1).ne'
    rw [Nat.cast_div hdvd hn0]; ring
  have hLS : (L : ℚ) * ∑ j ∈ J, (1 : ℚ) / j = X := by
    rw [hX, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjI := hJsub hj
    have hdvd : j ∣ L := dvd_LH hjI
    have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (by have := (Finset.mem_Icc.1 hjI).1; omega)
    rw [Nat.cast_div hdvd hj0]; ring
  -- `p R L = p L N1 + R X`
  have hidQ : ((p * R * L : ℕ) : ℚ) = ((p * L * N1 + R * X : ℕ) : ℚ) := by
    push_cast
    rw [← hRS, ← hLS]
    have := congrArg (fun z => (p : ℚ) * R * L * z) hsplit
    simp only [mul_one] at this
    rw [← this, hA2J]
    field_simp
  have hid : p * R * L = p * L * N1 + R * X := by exact_mod_cast hidQ
  have hpRX : p ∣ R * X := by
    have h1 : p ∣ p * R * L := by rw [mul_assoc]; exact dvd_mul_right _ _
    rw [hid] at h1
    exact (Nat.dvd_add_right (by rw [mul_assoc]; exact dvd_mul_right _ _)).1 h1
  have hpR : ¬ p ∣ R := by
    intro h
    obtain ⟨n, hn, hpn⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 h
    exact (Finset.mem_filter.1 hn).2 hpn
  have hpX : p ∣ X := (Nat.Prime.dvd_mul hp).1 hpRX |>.resolve_left hpR
  have hXle : X ≤ BH H := Finset.sum_le_sum_of_subset_of_nonneg hJsub (fun _ _ _ => Nat.zero_le _)
  have hX0 : X = 0 := by
    by_contra hne
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hpX
    omega
  intro n hn hpn
  have hjJ : n / p ∈ J := Finset.mem_image.2 ⟨n, Finset.mem_filter.2 ⟨hn, hpn⟩, rfl⟩
  have h1 : 1 ≤ L / (n / p) := one_le_LH_div (hJsub hjJ)
  have : L / (n / p) ≤ X := Finset.single_le_sum (f := fun j => L / j)
    (fun _ _ => Nat.zero_le _) hjJ
  omega

/-- Selected-row form of row rigidity: `selRow p = ∅`. -/
theorem selRow_eq_empty (W : ExactWord) {p H : ℕ} (hp : p.Prime) (hpB : BH H < p)
    (hcof : ∀ n ∈ W.A, p ∣ n → ∃ j, 1 ≤ j ∧ j ≤ H ∧ n = p * j) :
    W.selRow p = ∅ := by
  ext n
  simp only [Word.selRow, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
  exact selRow_empty_of_bounded_cofactors W hp hpB hcof n

/-- Row rigidity with the cofactor bound derived from `M < p (H + 1)`. -/
theorem selRow_empty_of_lt (W : ExactWord) {p H : ℕ} (hp : p.Prime) (hpB : BH H < p)
    (hM : W.M < p * (H + 1)) : ∀ n ∈ W.A, ¬ p ∣ n :=
  selRow_empty_of_bounded_cofactors W hp hpB (cofactor_bound_of_lt W.toWord hM)

/-- **Adjacent empty rows contradict gap-two.**  If `n, n+1 ∈ [a, M]`, `p ∣ n`, `q ∣ n+1`, and
both rows are rigid (prime, above `B_H`, bounded cofactors), the exact word cannot exist. -/
theorem adjacent_empty_rows_contradiction (W : ExactWord) {p q H H' n : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpB : BH H < p) (hqB : BH H' < q)
    (hcofp : ∀ x ∈ W.A, p ∣ x → ∃ j, 1 ≤ j ∧ j ≤ H ∧ x = p * j)
    (hcofq : ∀ x ∈ W.A, q ∣ x → ∃ j, 1 ≤ j ∧ j ≤ H' ∧ x = q * j)
    (hpn : p ∣ n) (hqn : q ∣ n + 1) (hn : W.a ≤ n) (hn1 : n + 1 ≤ W.M) : False :=
  omitted_neighbours W.toWord hn hn1
    (fun h => selRow_empty_of_bounded_cofactors W hp hpB hcofp n h hpn)
    (fun h => selRow_empty_of_bounded_cofactors W hq hqB hcofq (n + 1) h hqn)

/-- A **contact witness** for an exact word: two rigid prime rows meeting adjacent window
positions.  All fields are concrete numerical facts. -/
structure ContactWitness (W : ExactWord) where
  p : ℕ
  q : ℕ
  H : ℕ
  n : ℕ
  hp : p.Prime
  hq : q.Prime
  hpB : BH H < p
  hqB : BH H < q
  hpM : W.M < p * (H + 1)
  hqM : W.M < q * (H + 1)
  hpn : p ∣ n
  hqn : q ∣ n + 1
  hn : W.a ≤ n
  hn1 : n + 1 ≤ W.M

/-- **No exact word admits a contact witness.** -/
theorem ContactWitness.false {W : ExactWord} (c : ContactWitness W) : False :=
  adjacent_empty_rows_contradiction W c.hp c.hq c.hpB c.hqB
    (cofactor_bound_of_lt W.toWord c.hpM) (cofactor_bound_of_lt W.toWord c.hqM)
    c.hpn c.hqn c.hn c.hn1

end Erdos287.PostV87V90R
