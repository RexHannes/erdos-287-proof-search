import RequestProject.Erdos287.SourceChain.Physical.PairIdentity
import RequestProject.Erdos287.SourceChain.Physical.Presieve
import RequestProject.Erdos287.SourceChain.Physical.Scalar.Majorant

/-!
# Erdős #287 — Task C: independent semantic bridge from the Maynard square `w_X(t)`

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

`pairSum_eq_packets` (`PairIdentity.lean`) starts from `PairSum`, whose inner Maynard sum is
already restricted to `d_j = d_ℓ = 1`.  Here we start instead from objects defined
*independently* of the packet formula:

* `maynardFull t = ∑_{d : d_i ∣ L_i(t) ∀ i} ω_d` — the **full** Maynard sum (no coordinate is
  restricted);
* `wX t = 1_{c₁X<t<c₂X} 1_{W∣t} (maynardFull t)^2` — the physical weight `w_X(t)` of §6;
* `twoPrimeMoment j ℓ = ∑_t w_X(t) 1_{L_j(t) prime} 1_{L_ℓ(t) prime}` — the literal two-prime
  moment;
* `majorizedMoment S j ℓ = ∑_t w_X^{[ℓ]}(t) 1_{L_j(t) prime} U_X(L_ℓ(t))`, with
  `w_X^{[ℓ]}` the Maynard square with the `ℓ`-th divisor deleted (`d_ℓ = 1`);
* `actualScalar Sp` — the packet-layer scalar sieve built from the **actual** `ℓ_X` of
  `Physical/Scalar/` (support `1 ≤ d ≤ D_tot`).

Kernel-proved:

* `maynardFull_collapse` — on the window, if `L_j(t)` is prime then every `d` with `d_j ≠ 1`
  has `ω_d = 0` (from the support of `ω`, *not* by definition), so `d_j = 1` is forced;
* `majorizedMoment_eq_pairSum` — the ℓ-deleted majorised moment equals `PairSum` exactly;
* `pairSum_eq_packets_pos` — `pairSum_eq_packets` without the `W`-coprimality hypothesis on the
  scalar support (needed because the actual `ℓ_X` sieves all primes `< u`);
* `majorizedMoment_eq_packets` — **exact equality** of the moment with the labelled packet sum
  `∑_{ξ ∈ Ξ_{jℓ}} Γ_ξ ∑_{(d,f_ξ)=1} ℓ_X(d) P_j(f_ξ d, b_{ξ,d})` for the actual `ℓ_X`;
* `twoPrimeMoment_le_packets` — the literal two-prime moment is bounded by that packet sum,
  using the proved pointwise majorant `U_X(v) ≥ 1_{v prime > z}`, `U_X ≥ 0`.
-/

open scoped BigOperators
open Finset

namespace Erdos287.Physical

/-- **The packet-layer scalar sieve built from the actual `ℓ_X`.** -/
noncomputable def actualScalar (Sp : Sieve.ScalarParams) : ScalarSieve where
  supp := (range (⌊Sp.Dtot⌋₊ + 1)).filter (0 < ·)
  coeff := Sp.ellX

/-- The actual `U_X` agrees with the packet-layer `U`. -/
theorem actualScalar_U {Sp : Sieve.ScalarParams} (hS : Sp.Good) {v : ℕ} (hv : v ≠ 0) :
    (actualScalar Sp).U v = Sp.UX v := by
  classical
  unfold ScalarSieve.U Sieve.ScalarParams.UX actualScalar
  simp only
  apply Finset.sum_subset
  · intro e he
    simp only [mem_filter, mem_range] at he
    exact Nat.mem_divisors.2 ⟨he.2, hv⟩
  · intro e he hne
    by_contra hc
    apply hne
    have hlev := Sieve.ScalarParams.ellX_level hS hc
    have he0 : 0 < e := Nat.pos_of_mem_divisors he
    simp only [mem_filter, mem_range]
    refine ⟨⟨Nat.lt_succ_of_le (Nat.le_floor hlev), he0⟩, Nat.dvd_of_mem_divisors he⟩

namespace ScalarSieve

/-- Restriction of a scalar sieve to `W`-coprime support. -/
def restrictW (S : ScalarSieve) (W : ℕ) : ScalarSieve where
  supp := S.supp.filter (fun e => Nat.Coprime e W)
  coeff := S.coeff

end ScalarSieve

namespace PhysData

variable (P : PhysData)

/-- The window `c₁X < t < c₂X`. -/
def InWindow (t : ℕ) : Prop := P.c1 * P.X < t ∧ (t : ℝ) < P.c2 * P.X

/-- **Full Maynard sum** `∑_{d : d_i ∣ L_i(t) ∀ i} ω_d` (no restricted coordinate). -/
noncomputable def maynardFull (t : ℕ) : ℝ :=
  ∑ d ∈ Fintype.piFinset (fun i => (P.L i t).divisors), P.omega d

open Classical in
/-- **The physical weight** `w_X(t) = 1_{c₁X<t<c₂X} 1_{W∣t} (∑_{d_i ∣ L_i(t)} ω_d)^2`. -/
noncomputable def wX (t : ℕ) : ℝ :=
  (if P.InWindow t ∧ P.W ∣ t then 1 else 0) * P.maynardFull t ^ 2

open Classical in
/-- **The literal two-prime moment** `∑_t w_X(t) 1_{L_j(t) prime} 1_{L_ℓ(t) prime}`. -/
noncomputable def twoPrimeMoment (j l : Fin P.k) : ℝ :=
  ∑ t ∈ range (P.tMax + 1), P.wX t * (if (P.L j t).Prime ∧ (P.L l t).Prime then 1 else 0)

open Classical in
/-- Maynard sum with the `ℓ`-th divisor deleted (`d_ℓ = 1`). -/
noncomputable def maynardDel (l : Fin P.k) (t : ℕ) : ℝ :=
  ∑ d ∈ (Fintype.piFinset (fun i => (P.L i t).divisors)).filter (fun d => d l = 1), P.omega d

open Classical in
/-- `w_X^{[ℓ]}(t)`: the Maynard square with the `ℓ`-th divisor deleted. -/
noncomputable def wXdel (l : Fin P.k) (t : ℕ) : ℝ :=
  (if P.InWindow t ∧ P.W ∣ t then 1 else 0) * P.maynardDel l t ^ 2

open Classical in
/-- **The ℓ-deleted majorised moment** `∑_t w_X^{[ℓ]}(t) 1_{L_j(t) prime} U_X(L_ℓ(t))`. -/
noncomputable def majorizedMoment (S : ScalarSieve) (j l : Fin P.k) : ℝ :=
  ∑ t ∈ range (P.tMax + 1), P.wXdel l t * (if (P.L j t).Prime then 1 else 0) * S.U (P.L l t)

/-- Support of `ω` (§6: `∏ d_i ≤ X^{δ_s}`), in the coordinatewise form used here. -/
def OmegaSupport (δ : ℝ) : Prop := ∀ d, P.omega d ≠ 0 → ∀ i, (d i : ℝ) ≤ P.X ^ δ

variable {P}

theorem L_gt_of_window {t : ℕ} (ht : P.InWindow t) (i : Fin P.k) :
    (P.a i : ℝ) * P.c1 * P.X + 1 < P.L i t ∨ P.a i = 0 := by
  rcases Nat.eq_zero_or_pos (P.a i) with h | h
  · exact Or.inr h
  · left
    unfold L; push_cast
    have : (0 : ℝ) < P.a i := by exact_mod_cast h
    have := ht.1
    nlinarith

/-- **Collapse**: if `L_j(t)` is prime, every divisor vector with `d_j ≠ 1` carries `ω_d = 0`. -/
theorem omega_zero_of_prime (hP : P.WGood) {δ : ℝ} (hsupp : P.OmegaSupport δ)
    (hδ : ∀ i, P.X ^ δ < (P.a i : ℝ) * P.c1 * P.X + 1) {t : ℕ} (ht : P.InWindow t)
    {j : Fin P.k} (hpr : (P.L j t).Prime) {d : Fin P.k → ℕ} (hd : d j ∣ P.L j t)
    (hd1 : d j ≠ 1) : P.omega d = 0 := by
  by_contra hne
  have hle := hsupp d hne j
  rcases (Nat.dvd_prime hpr).1 hd with h | h
  · exact hd1 h
  · rcases L_gt_of_window ht j with hgt | h0
    · rw [h] at hle; linarith [hδ j]
    · exact absurd h0 (hP.a_pos j).ne'

theorem maynardFull_collapse (hP : P.WGood) {δ : ℝ} (hsupp : P.OmegaSupport δ)
    (hδ : ∀ i, P.X ^ δ < (P.a i : ℝ) * P.c1 * P.X + 1) {t : ℕ} (ht : P.InWindow t)
    {j : Fin P.k} (hpr : (P.L j t).Prime) (Q : (Fin P.k → ℕ) → Prop) [DecidablePred Q] :
    ∑ d ∈ (Fintype.piFinset (fun i => (P.L i t).divisors)).filter Q, P.omega d =
      ∑ d ∈ (Fintype.piFinset (fun i => (P.L i t).divisors)).filter (fun d => Q d ∧ d j = 1),
        P.omega d := by
  classical
  rw [← Finset.filter_filter]
  symm
  apply Finset.sum_filter_of_ne
  intro d hd hne
  by_contra h1
  have hdj : d j ∣ P.L j t :=
    Nat.dvd_of_mem_divisors (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hd).1 j)
  exact hne (omega_zero_of_prime hP hsupp hδ ht hpr hdj h1)

theorem mem_Tset_iff_window {t : ℕ} : t ∈ P.Tset ↔ t < P.tMax + 1 ∧ P.InWindow t := by
  unfold Tset InWindow
  simp only [mem_filter, mem_range]

/-- **Exact**: the ℓ-deleted majorised moment equals the designated-pair term `PairSum`. -/
theorem majorizedMoment_eq_pairSum (hP : P.WGood) {δ : ℝ} (hsupp : P.OmegaSupport δ)
    (hδ : ∀ i, P.X ^ δ < (P.a i : ℝ) * P.c1 * P.X + 1) (S : ScalarSieve) (j l : Fin P.k) :
    P.majorizedMoment S j l = P.PairSum S j l := by
  classical
  unfold majorizedMoment PairSum
  rw [show P.Tset = (range (P.tMax + 1)).filter P.InWindow from by
    ext t; rw [mem_Tset_iff_window, mem_filter, mem_range], Finset.sum_filter]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  by_cases hw : P.InWindow t
  · rw [if_pos hw]
    unfold wXdel
    by_cases hpr : (P.L j t).Prime
    · have hTs : t ∈ P.Tset := mem_Tset_iff_window.2 ⟨Finset.mem_range.1 ht, hw⟩
      rw [maynardInner_eq_divisors j l hTs]
      have hc := maynardFull_collapse hP hsupp hδ hw hpr (fun d => d l = 1)
      unfold maynardDel
      rw [hc]
      have : (Fintype.piFinset fun i => (P.L i t).divisors).filter (fun d => d l = 1 ∧ d j = 1) =
          (Fintype.piFinset fun i => (P.L i t).divisors).filter (fun d => d j = 1 ∧ d l = 1) := by
        ext d; simp only [mem_filter]; tauto
      rw [this]
      by_cases hW : P.W ∣ t
      · simp only [hw, hW, hpr, and_self, if_true]; ring
      · simp [hW]
    · simp [hpr]
  · rw [if_neg hw]
    unfold wXdel
    simp [hw]

theorem coprime_L_W {t : ℕ} (hW : P.W ∣ t) (i : Fin P.k) : Nat.Coprime (P.L i t) P.W := by
  obtain ⟨m, rfl⟩ := hW
  unfold L
  rw [show P.a i * (P.W * m) + 1 = 1 + (P.a i * m) * P.W by ring]
  simp

theorem U_restrictW {S : ScalarSieve} {v : ℕ} (hv : Nat.Coprime v P.W) :
    (S.restrictW P.W).U v = S.U v := by
  classical
  unfold ScalarSieve.U ScalarSieve.restrictW
  simp only
  rw [Finset.filter_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext e
  simp only [mem_filter]
  constructor
  · rintro ⟨he, -, hd⟩; exact ⟨he, hd⟩
  · rintro ⟨he, hd⟩; exact ⟨he, Nat.Coprime.coprime_dvd_left hd hv, hd⟩

theorem pairSum_restrictW (S : ScalarSieve) (j l : Fin P.k) :
    P.PairSum (S.restrictW P.W) j l = P.PairSum S j l := by
  classical
  unfold PairSum
  refine Finset.sum_congr rfl (fun t _ => ?_)
  by_cases h : P.W ∣ t ∧ (P.L j t).Prime
  · rw [U_restrictW (coprime_L_W h.1 l)]
  · simp [h]

theorem pairPackets_restrictW (S : ScalarSieve) (j l : Fin P.k) :
    P.PairPackets (S.restrictW P.W) j l = P.PairPackets S j l := by
  classical
  unfold PairPackets ScalarSieve.restrictW
  simp only
  refine Finset.sum_congr rfl (fun ξ _ => ?_)
  congr 1
  rw [Finset.filter_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext e
  simp only [mem_filter]
  constructor
  · rintro ⟨he, -, hf⟩; exact ⟨he, hf⟩
  · rintro ⟨he, hf⟩
    refine ⟨he, ?_, hf⟩
    have hWf : P.W ∣ P.f ξ := by unfold f; exact Dvd.intro_left _ rfl |>.trans (Dvd.intro _ rfl)
    exact (Nat.Coprime.coprime_dvd_left hWf hf).symm

/-- `pairSum_eq_packets` for any scalar sieve with positive support (no `W`-coprimality). -/
theorem pairSum_eq_packets_pos (hP : P.WGood) (S : ScalarSieve) (hS : ∀ e ∈ S.supp, 0 < e)
    {j l : Fin P.k} (hjl : j < l) : P.PairSum S j l = P.PairPackets S j l := by
  rw [← pairSum_restrictW, ← pairPackets_restrictW]
  refine pairSum_eq_packets hP _ ?_ hjl
  intro e he
  obtain ⟨he', hcop⟩ := Finset.mem_filter.1 he
  exact ⟨hS e he', hcop⟩

theorem actualScalar_pos (Sp : Sieve.ScalarParams) : ∀ e ∈ (actualScalar Sp).supp, 0 < e :=
  fun _ he => (Finset.mem_filter.1 he).2

/-- **Exact equality** of the ℓ-deleted majorised moment, built from the independently defined
Maynard square, with the labelled designated-pair packet sum for the **actual** `ℓ_X`. -/
theorem majorizedMoment_eq_packets (hP : P.WGood) {δ : ℝ} (hsupp : P.OmegaSupport δ)
    (hδ : ∀ i, P.X ^ δ < (P.a i : ℝ) * P.c1 * P.X + 1) (Sp : Sieve.ScalarParams)
    {j l : Fin P.k} (hjl : j < l) :
    P.majorizedMoment (actualScalar Sp) j l = P.PairPackets (actualScalar Sp) j l := by
  rw [majorizedMoment_eq_pairSum hP hsupp hδ, pairSum_eq_packets_pos hP _ (actualScalar_pos Sp) hjl]

/-- **The literal two-prime moment is bounded by the labelled packet sum** with the actual
`ℓ_X`, provided `L_ℓ(t) > z` on the window (`z = D_H` the top of the box grid). -/
theorem twoPrimeMoment_le_packets (hP : P.WGood) {δ : ℝ} (hsupp : P.OmegaSupport δ)
    (hδ : ∀ i, P.X ^ δ < (P.a i : ℝ) * P.c1 * P.X + 1) {Sp : Sieve.ScalarParams} (hS : Sp.Good)
    {j l : Fin P.k} (hjl : j < l) (hz : Sp.ztop ≤ (P.a l : ℝ) * P.c1 * P.X + 1) :
    P.twoPrimeMoment j l ≤ P.PairPackets (actualScalar Sp) j l := by
  classical
  rw [← majorizedMoment_eq_packets hP hsupp hδ Sp hjl]
  unfold twoPrimeMoment majorizedMoment
  refine Finset.sum_le_sum (fun t _ => ?_)
  have hL0 : P.L l t ≠ 0 := by unfold L; omega
  have hU0 : 0 ≤ (actualScalar Sp).U (P.L l t) := by
    rw [actualScalar_U hS hL0]; exact Sieve.ScalarParams.UX_nonneg hS hL0
  have hdel0 : 0 ≤ P.wXdel l t := by
    unfold wXdel; exact mul_nonneg (by split_ifs <;> norm_num) (sq_nonneg _)
  by_cases hboth : (P.L j t).Prime ∧ (P.L l t).Prime
  · rw [if_pos hboth, if_pos hboth.1, mul_one, mul_one]
    by_cases hw : P.InWindow t
    · -- `d_ℓ = 1` is forced by primality of `L_ℓ(t)`
      have hfull : P.maynardFull t = P.maynardDel l t := by
        unfold maynardFull maynardDel
        have := maynardFull_collapse hP hsupp hδ hw hboth.2 (fun _ => True)
        simp only [Finset.filter_true, true_and] at this
        exact this
      have hwx : P.wX t = P.wXdel l t := by unfold wX wXdel; rw [hfull]
      rw [hwx]
      have hgt : Sp.ztop < P.L l t := by
        rcases L_gt_of_window hw l with h | h
        · linarith
        · exact absurd h (hP.a_pos l).ne'
      have hU1 : 1 ≤ (actualScalar Sp).U (P.L l t) := by
        rw [actualScalar_U hS hL0]; exact Sieve.ScalarParams.UX_ge_one_of_prime hS hboth.2 hgt
      nlinarith
    · have : P.wX t = 0 := by unfold wX; simp [hw]
      rw [this]
      exact mul_nonneg hdel0 hU0
  · rw [if_neg hboth, mul_zero]
    exact mul_nonneg (mul_nonneg hdel0 (by split_ifs <;> norm_num)) hU0

end PhysData

end Erdos287.Physical
