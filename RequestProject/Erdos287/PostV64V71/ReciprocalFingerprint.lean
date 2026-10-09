import RequestProject.Erdos287.Window

/-!
# Erdős #287 — V68/V69 reciprocal subset-sum fingerprint `Ξ_H`

**Status: BANK (LEAN PROVED).**

* `recipSums H` — the finite set `S_H` of **distinct** rational values
  `∑_{j∈J} 1/j`, `J ⊆ {1,…,H}` (a `Finset ℚ`, so multiplicities are discarded);
* `Xi H` — the product of the reduced numerators of the **nonzero** distinct values in `S_H`
  (the value `0`, coming from `J = ∅`, is excluded);
* `num_dvd_Xi` — the reduced numerator of every nonzero value of `S_H` divides `Ξ_H`;
* `exists_cofactor_set` — the reciprocal congruence: if a reciprocal-sum-`1` set `A ⊆ [1,M]`
  contains a multiple of the prime `p`, then some nonempty `S ⊆ {1,…,⌊M/p⌋}` has
  `p ∣ num(∑_{s∈S} 1/s)` (top `p`-adic layer, cofactors);
* `good_large_prime_row_empty` — **V68 row emptiness**: if `⌊M/q⌋ ≤ H` (in particular if
  `q > M/H`) and `q ∤ Ξ_H`, then no element of `A` is divisible by `q`.

The proof literally uses the reciprocal congruence (`topLayer_congruence`) and the reduced
numerator divisibility; it uses no prime-row independence, random-residue heuristic or
modulo-`W` surrogate.

Integer-first size bank (no transcendental input):

* `lcmTo H = lcm(1,…,H)`, `BH H = ∑_{j=1}^H lcm(1,…,H)/j`;
* `num_le_BH` — `num(s) ≤ B_H` for every reciprocal subset sum `s`;
* `Xi_le_BH_pow` — `Ξ_H ≤ B_H^(#S_H - 1)`;
* `card_recipSums_le` — `#S_H ≤ 2^H`;
* `Xi_le_BH_pow_two_pow` — the crude bound `Ξ_H ≤ B_H^(2^H)` (for `H ≥ 1`).
-/

open scoped BigOperators

namespace Erdos287.PostV64V71

open Erdos287

/-- `S_H`: the set of **distinct** reciprocal subset sums `∑_{j∈J} 1/j`, `J ⊆ {1,…,H}`. -/
def recipSums (H : ℕ) : Finset ℚ :=
  (Finset.Icc 1 H).powerset.image (fun J : Finset ℕ => ∑ j ∈ J, (1 : ℚ) / (j : ℚ))

/-- `Ξ_H`: the product of the reduced positive numerators of the distinct **nonzero** values
of `S_H`. -/
def Xi (H : ℕ) : ℕ := ∏ s ∈ (recipSums H).filter (· ≠ 0), s.num.natAbs

theorem mem_recipSums {H : ℕ} {s : ℚ} :
    s ∈ recipSums H ↔ ∃ J ⊆ Finset.Icc 1 H, ∑ j ∈ J, (1 : ℚ) / j = s := by
  simp [recipSums]

theorem zero_mem_recipSums (H : ℕ) : (0 : ℚ) ∈ recipSums H :=
  mem_recipSums.2 ⟨∅, Finset.empty_subset _, by simp⟩

/-- `Ξ_H > 0`. -/
theorem Xi_pos (H : ℕ) : 0 < Xi H := by
  unfold Xi
  refine Finset.prod_pos fun s hs => ?_
  have hs0 : s ≠ 0 := (Finset.mem_filter.1 hs).2
  exact Int.natAbs_pos.2 (Rat.num_ne_zero.2 hs0)

/-- **Numerator divisibility**: the reduced numerator of a nonzero reciprocal subset sum
divides `Ξ_H`. -/
theorem num_dvd_Xi {H : ℕ} {s : ℚ} (hs : s ∈ recipSums H) (h0 : s ≠ 0) :
    s.num.natAbs ∣ Xi H :=
  Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨hs, h0⟩)

/-- **Reciprocal congruence (cofactor form).**  If `A ⊆ [1,M]` has `∑ 1/a = 1` and contains a
multiple of the prime `p`, then there is a nonempty `S ⊆ {1,…,⌊M/p⌋}` (the cofactors of the
top `p`-adic layer) with `p ∣ num(∑_{s∈S} 1/s)`. -/
theorem exists_cofactor_set
    (A : Finset ℕ) (M p : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a) (hAM : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) {a₀ : ℕ} (ha₀A : a₀ ∈ A) (ha₀q : p ∣ a₀) :
    ∃ S : Finset ℕ, S.Nonempty ∧ S ⊆ Finset.Icc 1 (M / p) ∧
      (p : ℤ) ∣ (∑ s ∈ S, (1 : ℚ) / s).num := by
  haveI := Fact.mk hp
  set E := A.sup (fun a => Nat.factorization a p)
  have hE_ge_e : 1 ≤ E := by
    refine le_trans ?_ (Finset.le_sup (f := fun a => Nat.factorization a p) ha₀A)
    exact (hp.dvd_iff_one_le_factorization (ne_of_gt (hpos a₀ ha₀A))).1 ha₀q
  have hE_nonempty : (topLayer A p).Nonempty := by
    obtain ⟨a, haA, haE⟩ : ∃ a ∈ A, Nat.factorization a p = E := by
      exact Finset.exists_max_image _ _ ⟨ a₀, ha₀A ⟩ |> fun ⟨ a, ha₁, ha₂ ⟩ => ⟨ a, ha₁,
        le_antisymm ( Finset.le_sup ( f := fun a => Nat.factorization a p ) ha₁ )
          ( Finset.sup_le fun x hx => ha₂ x hx ) ⟩
    exact ⟨ a, Finset.mem_filter.mpr ⟨ haA, haE ⟩ ⟩
  have hsum_cong : (∑ a ∈ topLayer A p, (((ordCompl[p] a : ℕ) : ZMod p))⁻¹) = 0 :=
    topLayer_congruence A p hp hpos hsum hE_ge_e
  set S := (topLayer A p).image (fun a => ordCompl[p] a) with hS_def
  have hS_nonempty : S.Nonempty := ⟨ _, Finset.mem_image_of_mem _ hE_nonempty.choose_spec ⟩
  have hS_subset : S ⊆ Finset.Icc 1 (M / p) := by
    intro s hs; obtain ⟨ a, ha, rfl ⟩ := Finset.mem_image.mp hs
    have haA : a ∈ A := topLayer_subset _ _ ha
    have haE : Nat.factorization a p = E := (Finset.mem_filter.1 ha).2
    have ha0 : 0 < a := hpos a haA
    refine Finset.mem_Icc.2 ⟨?_, ?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd ha0 (Nat.ordProj_dvd _ _)) (pow_pos hp.pos _)
    · have h1 : a / p ^ (Nat.factorization a p) ≤ M / p ^ (Nat.factorization a p) :=
        Nat.div_le_div_right (hAM a haA)
      have h2 : M / p ^ (Nat.factorization a p) ≤ M / p ^ 1 := by
        apply Nat.div_le_div_left (pow_le_pow_right₀ hp.one_lt.le (by omega)) (pow_pos hp.pos 1)
      simpa using le_trans h1 h2
  have hS_pos : ∀ s ∈ S, 0 < s := fun s hs => (Finset.mem_Icc.mp (hS_subset hs)).1
  have hS_not_div : ∀ s ∈ S, ¬ p ∣ s := by
    intro s hs; obtain ⟨ a, ha, rfl ⟩ := Finset.mem_image.mp hs
    exact Nat.not_dvd_ordCompl hp ( ne_of_gt ( hpos a ( topLayer_subset _ _ ha ) ) )
  have hS_sum_inv_zero : (∑ s ∈ S, ((s : ZMod p))⁻¹) = 0 := by
    rw [ Finset.sum_image ]
    · exact hsum_cong
    intros a ha b hb hab
    have ha' := (Finset.mem_filter.1 ha).2
    have hb' := (Finset.mem_filter.1 hb).2
    have h1 := Nat.div_mul_cancel ( Nat.ordProj_dvd a p )
    have h2 := Nat.div_mul_cancel ( Nat.ordProj_dvd b p )
    simp only at hab
    rw [ha'] at h1 hab; rw [hb'] at h2 hab
    rw [← h1, ← h2, hab]
  refine ⟨S, hS_nonempty, hS_subset, ?_⟩
  convert dvd_num_of_sum_inv_zero S p hp hS_pos hS_not_div hS_sum_inv_zero using 1

/-- **V68 good-row emptiness.**  Let `A ⊆ [1,M]` with `∑ 1/a = 1`, let `q` be prime with
`⌊M/q⌋ ≤ H` and `q ∤ Ξ_H`.  Then no element of `A` is divisible by `q`. -/
theorem good_large_prime_row_empty
    (A : Finset ℕ) (M H q : ℕ) (hq : q.Prime)
    (hpos : ∀ a ∈ A, 0 < a) (hAM : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) (hqH : M / q ≤ H) (hXi : ¬ q ∣ Xi H) :
    ∀ a ∈ A, ¬ q ∣ a := by
  intro a ha hqa
  obtain ⟨S, hSne, hSsub, hdvd⟩ := exists_cofactor_set A M q hq hpos hAM hsum ha hqa
  set s : ℚ := ∑ x ∈ S, (1 : ℚ) / x
  have hsmem : s ∈ recipSums H := by
    refine mem_recipSums.2 ⟨S, fun x hx => ?_, rfl⟩
    have := Finset.mem_Icc.1 (hSsub hx)
    exact Finset.mem_Icc.2 ⟨this.1, le_trans this.2 hqH⟩
  have hspos : 0 < s := by
    refine Finset.sum_pos (fun x hx => ?_) hSne
    have := (Finset.mem_Icc.1 (hSsub hx)).1
    positivity
  have h1 : q ∣ s.num.natAbs := by
    have := Int.natAbs_dvd_natAbs.2 hdvd
    simpa using this
  exact hXi (dvd_trans h1 (num_dvd_Xi hsmem hspos.ne'))

/-- `q > M/H` (as `M < q·H`) implies `⌊M/q⌋ ≤ H`. -/
theorem div_le_of_lt_mul {M H q : ℕ} (h : M < q * H) : M / q ≤ H := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · exact (Nat.div_lt_iff_lt_mul hq).2 (by rw [mul_comm]; exact h) |>.le

/-! ## Integer-first size bank -/

/-- `L_H = lcm(1,…,H)`. -/
def lcmTo (H : ℕ) : ℕ := (Finset.Icc 1 H).lcm id

/-- `B_H = ∑_{j=1}^H L_H / j`. -/
def BH (H : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 H, lcmTo H / j

theorem lcmTo_pos (H : ℕ) : 0 < lcmTo H := by
  unfold lcmTo
  apply Nat.pos_of_ne_zero
  rw [Ne, Finset.lcm_eq_zero_iff]
  simp

theorem dvd_lcmTo {H j : ℕ} (hj : j ∈ Finset.Icc 1 H) : j ∣ lcmTo H :=
  Finset.dvd_lcm (s := Finset.Icc 1 H) (f := id) hj

/-- Every reciprocal subset sum has numerator `≤ B_H` (numerator of the reduced form). -/
theorem num_le_BH {H : ℕ} {s : ℚ} (hs : s ∈ recipSums H) : s.num.natAbs ≤ BH H := by
  obtain ⟨J, hJ, rfl⟩ := mem_recipSums.1 hs
  set L := lcmTo H
  have hL : 0 < L := lcmTo_pos H
  -- `∑_{j∈J} 1/j = (∑_{j∈J} L/j) / L`
  have hrepr : ∑ j ∈ J, (1 : ℚ) / j = ((∑ j ∈ J, L / j : ℕ) : ℚ) / (L : ℚ) := by
    rw [eq_div_iff (by positivity), Finset.sum_mul]
    push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjL : j ∣ L := dvd_lcmTo (hJ hj)
    have hj0 : (j : ℚ) ≠ 0 := by
      have := (Finset.mem_Icc.1 (hJ hj)).1; positivity
    rw [Nat.cast_div hjL hj0]
    field_simp
  rw [hrepr]
  set num := (∑ j ∈ J, L / j : ℕ)
  have hnum_le : num ≤ BH H := by
    unfold BH
    exact Finset.sum_le_sum_of_subset_of_nonneg hJ (fun _ _ _ => Nat.zero_le _)
  have key : (((num : ℚ) / (L : ℚ)).num.natAbs) ≤ num := by
    have h := Rat.num_dvd (num : ℤ) (show (L : ℤ) ≠ 0 by exact_mod_cast hL.ne')
    rw [Rat.divInt_eq_div] at h
    simp only [Int.cast_natCast] at h
    rcases Nat.eq_zero_or_pos num with h0 | h0
    · rw [h0]; simp
    · have := Int.natAbs_dvd_natAbs.2 h
      simpa using Nat.le_of_dvd h0 this
  exact le_trans key hnum_le

/-- `#S_H ≤ 2^H`. -/
theorem card_recipSums_le (H : ℕ) : (recipSums H).card ≤ 2 ^ H := by
  unfold recipSums
  refine le_trans Finset.card_image_le ?_
  simp

/-- **Integer fingerprint bound**: `Ξ_H ≤ B_H^(#S_H - 1)`. -/
theorem Xi_le_BH_pow (H : ℕ) : Xi H ≤ BH H ^ ((recipSums H).card - 1) := by
  unfold Xi
  have hcard : ((recipSums H).filter (· ≠ 0)).card = (recipSums H).card - 1 := by
    have h := Finset.card_filter_add_card_filter_not (s := recipSums H) (fun s : ℚ => s ≠ 0)
    have h2 : ((recipSums H).filter (fun s : ℚ => ¬ s ≠ 0)) = {0} := by
      ext x; simp only [Finset.mem_filter, not_not, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨zero_mem_recipSums H, rfl⟩
    rw [h2, Finset.card_singleton] at h
    omega
  rw [← hcard]
  exact Finset.prod_le_pow_card _ _ _ fun s hs => num_le_BH (Finset.mem_filter.1 hs).1

/-- `B_H ≥ 1` for `H ≥ 1`. -/
theorem one_le_BH {H : ℕ} (hH : 1 ≤ H) : 1 ≤ BH H := by
  unfold BH
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 H := Finset.mem_Icc.2 ⟨le_rfl, hH⟩
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) h1)
  simpa using lcmTo_pos H

/-- **Crude fingerprint bound**: `Ξ_H ≤ B_H^(2^H)` for `H ≥ 1`. -/
theorem Xi_le_BH_pow_two_pow {H : ℕ} (hH : 1 ≤ H) : Xi H ≤ BH H ^ (2 ^ H) :=
  le_trans (Xi_le_BH_pow H)
    (Nat.pow_le_pow_right (one_le_BH hH) (le_trans (Nat.sub_le _ _) (card_recipSums_le H)))

end Erdos287.PostV64V71
