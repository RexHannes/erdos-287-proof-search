import RequestProject.Erdos287.SourceChain.Physical.Scalar.Ownership

/-!
# Erdős #287 — scalar sieve: support, level, parity and the pointwise majorant

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Main results about the actual coefficient `ℓ_X` of `Physical/Scalar/Weights.lean`:

* `kappa_even`, `kappa_odd` — `κ_J = λ⁺_low` for even `J`, `λ⁻_low` for odd `J`;
* `ellX_J0_sector` — the `J = 0` sector is the **entire** low upper-sieve weight `λ⁺_low(d)`;
* `ellX_support` — `ℓ_X(d) ≠ 0` only for squarefree `d = b·a` with `b` a product of low primes
  `< u` and `a` a product of high (boxed) primes;
* `ellX_level` — `ℓ_X(d) ≠ 0 ⇒ d ≤ D_tot = D_low · D_int^{1+τ}` (the internal level is
  `D_int`, the total level `D_tot`);
* `UX_eq_parity_sum` — `U_X(v) = ∑_J (-1)^J (∑_{b∣v} κ_J(b)) (∑_{a∣v} hw_J(a))`;
* `UX_nonneg` and `UX_majorant` — **the pointwise upper-majorant statement**:
  `U_X(v) ≥ 0`, and `U_X(v) ≥ 1` whenever `v` has no prime factor `≤ z = D_H`;
  `UX_ge_indicator` combines them, `UX_ge_one_of_prime` is the prime event.

The majorant is proved by the parity-sensitive sign argument of §15: for even `J` the upper
low sieve `∑_{b∣v} λ⁺_low(b) ≥ 1_{(v,P(u))=1}`, for odd `J` the lower low sieve
`∑_{b∣v} λ⁻_low(b) ≤ 1_{(v,P(u))=1}` *before* multiplication by `(-1)^J = -1`; then the high
box sum `∑_J (-1)^J ∑_{a∣v} hw_J(a) ≥ 1_{no high prime divides v}` by the Rosser inequality
for Lichtman's (parity-dependent) `𝐃_J^+`.  No positivity hypothesis is assumed.
-/

open scoped BigOperators
open Finset

namespace Erdos287.Physical.Sieve

/-- Odd-position admissibility with a fixed threshold, for a weight `f`. -/
def OddPosAdm (f : ℕ → ℝ) (θ : ℝ) (A : Finset ℕ) : Prop :=
  ∀ p ∈ A, Even (above A p).card → (∏ q ∈ above A p, f q) * f p ^ 3 < θ

theorem OddPosAdm_pre (f : ℕ → ℝ) (θ : ℝ) :
    ∀ s p, (∀ x ∈ s, p < x) → OddPosAdm f θ (insert p s) → OddPosAdm f θ s := by
  intro s p hp h q hq hev
  have := h q (Finset.mem_insert_of_mem hq)
  rw [above_insert_of_lt hp hq] at this
  exact this hev

theorem OddPosAdm_ext (f : ℕ → ℝ) (θ : ℝ) (U : ℕ → Prop) : ∀ s p, U p → (∀ x ∈ s, p < x) →
    Odd s.card → OddPosAdm f θ s → OddPosAdm f θ (insert p s) := by
  intro s p _ hp hodd h q hq hev
  rcases Finset.mem_insert.1 hq with rfl | hq
  · rw [above_insert_self hp] at hev
    exact absurd hev (Nat.not_even_iff_odd.2 hodd)
  · rw [above_insert_of_lt hp hq] at hev ⊢
    exact h q hq hev

theorem OddPosAdm_empty (f : ℕ → ℝ) (θ : ℝ) : OddPosAdm f θ ∅ :=
  fun p hp => absurd hp (Finset.notMem_empty p)

/-- Double divisor sums: `∑_{d∣v} ∑_{ba=d} F(b,a) = ∑_{b∣v} ∑_{a∣v} F(b,a)` when `F` is
supported on coprime pairs. -/
theorem sum_divisors_antidiag {M : Type*} [AddCommMonoid M] {v : ℕ} (hv : v ≠ 0)
    (F : ℕ → ℕ → M) (hF : ∀ b a, F b a ≠ 0 → Nat.Coprime b a) :
    ∑ d ∈ v.divisors, ∑ x ∈ d.divisorsAntidiagonal, F x.1 x.2 =
      ∑ b ∈ v.divisors, ∑ a ∈ v.divisors, F b a := by
  rw [Finset.sum_sigma', ← Finset.sum_product']
  refine Finset.sum_bij_ne_zero (fun y _ _ => y.2) ?_ ?_ ?_ ?_
  · intro y hy _
    obtain ⟨hd, hx⟩ := Finset.mem_sigma.1 hy
    obtain ⟨hmul, hd0⟩ := Nat.mem_divisorsAntidiagonal.1 hx
    have hdv := Nat.dvd_of_mem_divisors hd
    rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors]
    exact ⟨⟨(Dvd.intro _ hmul).trans hdv, hv⟩, ⟨(Dvd.intro_left _ hmul).trans hdv, hv⟩⟩
  · intro y1 hy1 _ y2 hy2 _ h
    obtain ⟨-, hx1⟩ := Finset.mem_sigma.1 hy1
    obtain ⟨-, hx2⟩ := Finset.mem_sigma.1 hy2
    have e1 := (Nat.mem_divisorsAntidiagonal.1 hx1).1
    have e2 := (Nat.mem_divisorsAntidiagonal.1 hx2).1
    simp only at h
    have hd : y1.1 = y2.1 := by rw [← e1, ← e2, h]
    exact Sigma.ext hd (heq_of_eq h)
  · intro x hx hF0
    obtain ⟨hb, ha⟩ := Finset.mem_product.1 hx
    have hcop := hF x.1 x.2 hF0
    have hdv : x.1 * x.2 ∣ v :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (Nat.dvd_of_mem_divisors hb)
        (Nat.dvd_of_mem_divisors ha)
    refine ⟨⟨x.1 * x.2, x⟩, ?_, hF0, rfl⟩
    rw [Finset.mem_sigma, Nat.mem_divisors, Nat.mem_divisorsAntidiagonal]
    exact ⟨⟨hdv, hv⟩, rfl, fun h0 => hv (Nat.eq_zero_of_zero_dvd (h0 ▸ hdv))⟩
  · intro y _ _; rfl

namespace ScalarParams

variable {S : ScalarParams}

theorem kappa_even {J : ℕ} (h : Even J) : S.kappa J = S.lamLowPlus := by
  unfold kappa; rw [if_pos h]

theorem kappa_odd {J : ℕ} (h : ¬ Even J) : S.kappa J = S.lamLowMinus := by
  unfold kappa; rw [if_neg h]

theorem hw_support {J a : ℕ} (h : S.hw J a ≠ 0) : S.GoodHigh J a ∧ S.HighAdm a.primeFactors := by
  classical
  unfold hw at h
  split_ifs at h with hc
  · exact hc
  · exact absurd rfl h

theorem hw_nonneg (J a : ℕ) : 0 ≤ S.hw J a := by
  classical
  unfold hw; split_ifs <;> norm_num

/-- The box weight `f(q) = D_{box(q)}`. -/
noncomputable def fBox (S : ScalarParams) (q : ℕ) : ℝ := S.boxEnd (S.boxOf q)

theorem fBox_ge_u0 (hS : S.Good) (q : ℕ) : S.u0 ≤ S.fBox q := boxEnd_ge_u0 hS _

theorem fBox_mono (hS : S.Good) {A : Finset ℕ} (hA : ∀ p ∈ A, S.IsHigh p) :
    ∀ x ∈ A, ∀ y ∈ A, x ≤ y → S.fBox x ≤ S.fBox y := fun x hx y hy hxy =>
  (boxEnd_le_iff hS).2 (boxOf_mono hS (hA x hx) (hA y hy) hxy)

theorem highAdm_iff (A : Finset ℕ) :
    S.HighAdm A ↔ OddPosAdm S.fBox (S.threshold A.card) A := Iff.rfl

/-- The product of the box values of an odd-position-admissible set is below the threshold. -/
theorem prod_fBox_lt (hS : S.Good) {A : Finset ℕ} (hA : ∀ p ∈ A, S.IsHigh p) (hne : A.Nonempty)
    {θ : ℝ} (hadm : OddPosAdm S.fBox θ A) : ∏ q ∈ A, S.fBox q < θ := by
  obtain ⟨p, hp, hev, hle⟩ := exists_odd_position_witness S.fBox A hne
    (fun x _ => (u0_gt_one hS).le.trans (fBox_ge_u0 hS x)) (fBox_mono hS hA)
  have h1 := hadm p hp hev
  have hp1 : 1 ≤ S.fBox p := (u0_gt_one hS).le.trans (fBox_ge_u0 hS p)
  have h0 : 0 ≤ ∏ q ∈ above A p, S.fBox q := Finset.prod_nonneg (fun x _ =>
    le_trans zero_le_one ((u0_gt_one hS).le.trans (fBox_ge_u0 hS x)))
  have : (∏ q ∈ above A p, S.fBox q) * S.fBox p ^ 2 ≤
      (∏ q ∈ above A p, S.fBox q) * S.fBox p ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp1 (by norm_num)) h0
  linarith

/-- **Range of `J`**: an admissible set of high primes has at most `ε₀^{-2} = T²` elements. -/
theorem card_le_T_sq (hS : S.Good) {A : Finset ℕ} (hA : ∀ p ∈ A, S.IsHigh p)
    (hadm : OddPosAdm S.fBox S.Dint A) : A.card ≤ S.T ^ 2 := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp
  have hlt := prod_fBox_lt hS hA hne hadm
  have hge : S.u0 ^ A.card ≤ ∏ q ∈ A, S.fBox q := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => (u0_pos hS).le) (fun x _ => fBox_ge_u0 hS x)
  have hD : S.Dint = S.u0 ^ (S.T ^ 2) := by
    rw [← u0_pow_T_sq hS, show ((S.T : ℝ)) ^ 2 = ((S.T ^ 2 : ℕ) : ℝ) by push_cast; rfl,
      Real.rpow_natCast]
  have : S.u0 ^ A.card < S.u0 ^ (S.T ^ 2) := by rw [← hD]; linarith
  exact ((pow_lt_pow_iff_right₀ (u0_gt_one hS)).1 this).le

/-! ### Parity -/

/-- **The `J = 0` sector is the entire low upper-sieve weight** `λ⁺_low(d)`. -/
theorem ellX_J0_sector {d : ℕ} (hd : d ≠ 0) :
    (-1 : ℝ) ^ 0 * ∑ x ∈ d.divisorsAntidiagonal, S.kappa 0 x.1 * S.hw 0 x.2 = S.lamLowPlus d := by
  classical
  rw [pow_zero, one_mul, kappa_even (⟨0, rfl⟩ : Even 0)]
  rw [Finset.sum_eq_single (d, 1)]
  · have : S.hw 0 1 = 1 := by
      unfold hw
      rw [if_pos]
      refine ⟨⟨squarefree_one, by simp, by simp⟩, ?_⟩
      intro p hp; simp at hp
    rw [this, mul_one]
  · intro x hx hne
    obtain ⟨hmul, -⟩ := Nat.mem_divisorsAntidiagonal.1 hx
    have h2 : x.2 ≠ 1 := by
      intro h; apply hne; ext
      · simpa [h] using hmul
      · exact h
    have : S.hw 0 x.2 = 0 := by
      unfold hw
      rw [if_neg]
      rintro ⟨⟨hsq, -, hc⟩, -⟩
      apply h2
      rw [← Nat.prod_primeFactors_of_squarefree hsq, Finset.card_eq_zero.1 hc, Finset.prod_empty]
    rw [this, mul_zero]
  · intro h; exact absurd (Nat.mem_divisorsAntidiagonal.2 ⟨mul_one d, hd⟩) h

/-! ### Support and level -/

/-- **Support**: `ℓ_X(d) ≠ 0` only for `d = b·a` with `b` squarefree with all prime factors
low (`< u`), and `a` a squarefree product of high primes with admissible box vector. -/
theorem ellX_support (hS : S.Good) {d : ℕ} (h : S.ellX d ≠ 0) :
    ∃ J ∈ range (S.T ^ 2 + 1), ∃ b a, b * a = d ∧ S.kappa J b ≠ 0 ∧
      (Squarefree b ∧ ∀ p ∈ b.primeFactors, (p : ℝ) < S.u0) ∧
      S.GoodHigh J a ∧ S.HighAdm a.primeFactors := by
  rw [ellX_eq_setForm hS] at h
  obtain ⟨J, hJ, hJne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hJne' : ∑ x ∈ d.divisorsAntidiagonal, S.kappa J x.1 * S.hw J x.2 ≠ 0 := by
    intro h0; apply hJne; rw [h0, mul_zero]
  obtain ⟨x, hx, hxne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hJne'
  have hk : S.kappa J x.1 ≠ 0 := fun h0 => hxne (by rw [h0, zero_mul])
  have hh : S.hw J x.2 ≠ 0 := fun h0 => hxne (by rw [h0, mul_zero])
  exact ⟨J, hJ, x.1, x.2, (Nat.mem_divisorsAntidiagonal.1 hx).1, hk, kappa_support hk,
    hw_support hh⟩

theorem high_part_le (hS : S.Good) {J a : ℕ} (hg : S.GoodHigh J a)
    (hadm : S.HighAdm a.primeFactors) : (a : ℝ) ≤ S.Dint ^ (1 + S.tau) := by
  obtain ⟨hsq, hhigh, -⟩ := hg
  have hτ : 0 ≤ 1 + S.tau := by linarith [tau_pos hS]
  have hDint1 : 1 ≤ S.Dint ^ (1 + S.tau) := Real.one_le_rpow (Dint_gt_one hS).le hτ
  rw [← Nat.prod_primeFactors_of_squarefree hsq]
  push_cast
  rcases a.primeFactors.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, Finset.prod_empty]; exact hDint1
  have hle : ∏ q ∈ a.primeFactors, (q : ℝ) ≤ ∏ q ∈ a.primeFactors, S.fBox q ^ (1 + S.tau) := by
    apply Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
    intro q hq
    have := (boxOf_spec (hhigh q hq)).2.2
    rwa [boxTop] at this
  rw [Real.finset_prod_rpow a.primeFactors S.fBox (fun q _ => (boxEnd_pos hS _).le)] at hle
  have hlt := prod_fBox_lt hS hhigh hne hadm
  have h0 : 0 ≤ ∏ q ∈ a.primeFactors, S.fBox q :=
    Finset.prod_nonneg (fun q _ => (boxEnd_pos hS _).le)
  calc ∏ q ∈ a.primeFactors, (q : ℝ) ≤ (∏ q ∈ a.primeFactors, S.fBox q) ^ (1 + S.tau) := hle
    _ ≤ S.threshold a.primeFactors.card ^ (1 + S.tau) := Real.rpow_le_rpow h0 hlt.le hτ
    _ ≤ S.Dint ^ (1 + S.tau) := threshold_rpow_le hS _

/-- **Level**: `ℓ_X(d) ≠ 0 ⇒ d ≤ D_tot = D_low · D_int^{1+τ}`. -/
theorem ellX_level (hS : S.Good) {d : ℕ} (h : S.ellX d ≠ 0) : (d : ℝ) ≤ S.Dtot := by
  obtain ⟨J, -, b, a, rfl, hk, -, hg, hadm⟩ := ellX_support hS h
  have hb := kappa_level hS hk
  have ha := high_part_le hS hg hadm
  rw [← Dlow_mul hS]
  push_cast
  exact mul_le_mul hb ha (Nat.cast_nonneg _) (le_trans zero_le_one (Dlow_ge_one hS))

/-! ### The pointwise majorant -/

theorem kappa_hw_coprime (hS : S.Good) {J : ℕ} (b a : ℕ) (h : S.kappa J b * S.hw J a ≠ 0) :
    Nat.Coprime b a := by
  have hk : S.kappa J b ≠ 0 := fun h0 => h (by rw [h0, zero_mul])
  have hh : S.hw J a ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
  obtain ⟨-, hlow⟩ := kappa_support hk
  obtain ⟨⟨hsq, hhigh, -⟩, -⟩ := hw_support hh
  rw [Nat.coprime_iff_gcd_eq_one, ← Nat.Coprime]
  apply Nat.coprime_of_dvd
  intro p hp hpb hpa
  have hb0 : b ≠ 0 := by
    rintro rfl; apply hk
    unfold kappa; split_ifs <;> simp [lamLowPlus, lamLowMinus]
  have h1 := hlow p (Nat.mem_primeFactors.2 ⟨hp, hpb, hb0⟩)
  have h2 := hhigh p (Nat.mem_primeFactors.2 ⟨hp, hpa, hsq.ne_zero⟩)
  exact not_low_of_high hS h2 h1

/-- **`U_X(v) = ∑_J (-1)^J K_J(v) HW_J(v)`** with `K_J(v) = ∑_{b∣v} κ_J(b)`,
`HW_J(v) = ∑_{a∣v} hw_J(a)`. -/
theorem UX_eq_parity_sum (hS : S.Good) {v : ℕ} (hv : v ≠ 0) :
    S.UX v = ∑ J ∈ range (S.T ^ 2 + 1), (-1 : ℝ) ^ J *
      ((∑ b ∈ v.divisors, S.kappa J b) * (∑ a ∈ v.divisors, S.hw J a)) := by
  unfold UX
  simp_rw [ellX_eq_setForm hS]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  rw [← Finset.mul_sum, sum_divisors_antidiag hv (fun b a => S.kappa J b * S.hw J a)
    (fun b a h => kappa_hw_coprime hS b a h), Finset.sum_mul_sum]

/-- The high box sum: `∑_{J ≤ T²} (-1)^J ∑_{a∣v} hw_J(a) ≥ 1_{no high prime divides v}`. -/
theorem high_sum_ge (hS : S.Good) {v : ℕ} (hv : v ≠ 0) [DecidablePred S.IsHigh] :
    (if v.primeFactors.filter S.IsHigh = ∅ then (1 : ℝ) else 0) ≤
      ∑ J ∈ range (S.T ^ 2 + 1), (-1 : ℝ) ^ J * ∑ a ∈ v.divisors, S.hw J a := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  set g : ℕ → ℝ := fun a => ∑ J ∈ range (S.T ^ 2 + 1), (-1 : ℝ) ^ J * S.hw J a with hg
  have hgsupp : ∀ d, g d ≠ 0 → Squarefree d ∧ ∀ p ∈ d.primeFactors, S.IsHigh p := by
    intro d hd
    obtain ⟨J, -, hJ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
    have : S.hw J d ≠ 0 := fun h0 => hJ (by rw [h0, mul_zero])
    obtain ⟨⟨hsq, hhigh, -⟩, -⟩ := hw_support this
    exact ⟨hsq, hhigh⟩
  rw [show (∑ a ∈ v.divisors, ∑ J ∈ range (S.T ^ 2 + 1), (-1 : ℝ) ^ J * S.hw J a) =
    ∑ a ∈ v.divisors, g a from rfl, sum_divisors_eq_sum_powerset hv S.IsHigh g hgsupp]
  set Th := v.primeFactors.filter S.IsHigh
  have hThigh : ∀ A ∈ Th.powerset, ∀ p ∈ A, S.IsHigh p := fun A hA p hp =>
    (Finset.mem_filter.1 (Finset.mem_powerset.1 hA hp)).2
  -- value of `g` on a squarefree product of high primes
  have hgA : ∀ A ∈ Th.powerset, g (∏ p ∈ A, p) =
      if S.HighAdm A ∧ A.card ≤ S.T ^ 2 then (-1 : ℝ) ^ A.card else 0 := by
    intro A hA
    have hAp : ∀ p ∈ A, p.Prime := fun p hp => (hThigh A hA p hp).1
    have hpf : (∏ p ∈ A, p).primeFactors = A := Nat.primeFactors_prod hAp
    simp only [hg]
    rw [Finset.sum_eq_single A.card]
    · unfold hw GoodHigh
      rw [hpf]
      by_cases hc : S.HighAdm A ∧ A.card ≤ S.T ^ 2
      · rw [if_pos ⟨⟨squarefree_prod_primes hAp, hThigh A hA, rfl⟩, hc.1⟩, if_pos hc, mul_one]
      · rw [if_neg hc]
        by_cases hadm : S.HighAdm A
        · have hmem : A.card ∉ range (S.T ^ 2 + 1) := by
            intro hm; exact hc ⟨hadm, Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)⟩
          rw [if_pos ⟨⟨squarefree_prod_primes hAp, hThigh A hA, rfl⟩, hadm⟩, mul_one]
          -- this branch is outside the summation range: handled below
          exact absurd (Nat.lt_succ_iff.2 (card_le_T_sq hS (hThigh A hA) (fun p hp hev =>
            lt_of_lt_of_le (hadm p hp hev) (threshold_le_Dint hS _)))) (by
              rwa [Finset.mem_range] at hmem)
        · rw [if_neg (fun h => hadm h.2), mul_zero]
    · intro J _ hJ
      unfold hw GoodHigh
      rw [hpf, if_neg (fun h => hJ h.1.2.2.symm), mul_zero]
    · intro hm
      unfold hw GoodHigh
      rw [hpf]
      by_cases hadm : S.HighAdm A
      · exact absurd (Finset.mem_range.2 (Nat.lt_succ_iff.2 (card_le_T_sq hS (hThigh A hA)
          (fun p hp hev => lt_of_lt_of_le (hadm p hp hev) (threshold_le_Dint hS _))))) hm
      · rw [if_neg (fun h => hadm h.2), mul_zero]
  rw [Finset.sum_congr rfl hgA]
  -- compare with the uniform family `OddPosAdm fBox D_int`
  have key := rosser_upper (OddPosAdm S.fBox S.Dint) S.IsHigh (OddPosAdm_empty _ _)
    (OddPosAdm_pre _ _) (OddPosAdm_ext _ _ _) Th (fun p hp => (Finset.mem_filter.1 hp).2)
  have key' := (Int.cast_le (R := ℝ)).2 key
  push_cast at key'
  refine le_trans (le_of_eq_of_le ?_ key') (Finset.sum_le_sum (fun A hA => ?_))
  · rfl
  · -- termwise comparison
    by_cases hev : Even A.card
    · have : (S.HighAdm A ∧ A.card ≤ S.T ^ 2) ↔ OddPosAdm S.fBox S.Dint A := by
        unfold HighAdm threshold
        rw [if_pos hev]
        exact ⟨fun h => h.1, fun h => ⟨h, card_le_T_sq hS (hThigh A hA) h⟩⟩
      by_cases h : OddPosAdm S.fBox S.Dint A
      · rw [if_pos h, if_pos (this.2 h)]
      · rw [if_neg h, if_neg (fun h' => h (this.1 h'))]
    · have hneg : (-1 : ℝ) ^ A.card = -1 := Odd.neg_one_pow (Nat.not_even_iff_odd.1 hev)
      have himp : S.HighAdm A → OddPosAdm S.fBox S.Dint A := fun h p hp hev' =>
        lt_of_lt_of_le (h p hp hev') (threshold_le_Dint hS _)
      rw [hneg]
      by_cases h : OddPosAdm S.fBox S.Dint A
      · rw [if_pos h]; split_ifs <;> norm_num
      · rw [if_neg h, if_neg (fun h' => h (himp h'.1))]

/-- **Pointwise lower bound** `U_X(v) ≥ 1_{(v,P(u))=1} · 1_{no high prime divides v}`. -/
theorem UX_ge_rough (hS : S.Good) {v : ℕ} (hv : v ≠ 0) [DecidablePred S.IsHigh] :
    roughLow S.u0 v * (if v.primeFactors.filter S.IsHigh = ∅ then (1 : ℝ) else 0) ≤ S.UX v := by
  rw [UX_eq_parity_sum hS hv]
  have hρ0 : 0 ≤ roughLow S.u0 v := by unfold roughLow; split_ifs <;> norm_num
  calc roughLow S.u0 v * (if v.primeFactors.filter S.IsHigh = ∅ then (1 : ℝ) else 0)
      ≤ roughLow S.u0 v * ∑ J ∈ range (S.T ^ 2 + 1), (-1 : ℝ) ^ J *
          ∑ a ∈ v.divisors, S.hw J a := mul_le_mul_of_nonneg_left (high_sum_ge hS hv) hρ0
    _ = ∑ J ∈ range (S.T ^ 2 + 1), (-1 : ℝ) ^ J *
          (roughLow S.u0 v * ∑ a ∈ v.divisors, S.hw J a) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun J _ => by ring)
    _ ≤ _ := by
        refine Finset.sum_le_sum (fun J _ => ?_)
        have hHW : 0 ≤ ∑ a ∈ v.divisors, S.hw J a := Finset.sum_nonneg (fun a _ => hw_nonneg J a)
        by_cases hev : Even J
        · rw [hev.neg_one_pow, one_mul, one_mul, kappa_even hev]
          exact mul_le_mul_of_nonneg_right (lamLowPlus_sum_ge hv) hHW
        · rw [(Nat.not_even_iff_odd.1 hev).neg_one_pow, kappa_odd hev, neg_one_mul, neg_one_mul,
            neg_le_neg_iff]
          exact mul_le_mul_of_nonneg_right (lamLowMinus_sum_le hS hv) hHW

/-- **`U_X(v) ≥ 0`** for every `v ≥ 1`. -/
theorem UX_nonneg (hS : S.Good) {v : ℕ} (hv : v ≠ 0) : 0 ≤ S.UX v := by
  classical
  refine le_trans ?_ (UX_ge_rough hS hv)
  have : 0 ≤ roughLow S.u0 v := by unfold roughLow; split_ifs <;> norm_num
  exact mul_nonneg this (by split_ifs <;> norm_num)

/-- **Majorant**: `U_X(v) ≥ 1` whenever `v ≥ 1` has no prime factor `≤ z = D_H`. -/
theorem UX_majorant (hS : S.Good) {v : ℕ} (hv : v ≠ 0)
    (hz : ∀ p ∈ v.primeFactors, S.ztop < p) : 1 ≤ S.UX v := by
  classical
  refine le_trans (le_of_eq ?_) (UX_ge_rough hS hv)
  have hu : S.u0 ≤ S.ztop := boxEnd_ge_u0 hS _
  have h1 : roughLow S.u0 v = 1 := by
    unfold roughLow
    rw [if_pos]
    rw [Finset.filter_eq_empty_iff]
    intro p hp hlt
    have := hz p hp
    linarith
  have h2 : v.primeFactors.filter S.IsHigh = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro p hp hh
    have := hz p hp
    have := high_le_ztop hS hh
    linarith
  rw [h1, if_pos h2, one_mul]

/-- **The pointwise upper-majorant statement**:
`U_X(v) ≥ 1_{v has no prime factor ≤ z}` and `U_X(v) ≥ 0`. -/
theorem UX_ge_indicator (hS : S.Good) {v : ℕ} (hv : v ≠ 0) [Decidable (∀ p ∈ v.primeFactors, S.ztop < p)] :
    (if ∀ p ∈ v.primeFactors, S.ztop < p then (1 : ℝ) else 0) ≤ S.UX v := by
  split_ifs with h
  · exact UX_majorant hS hv h
  · exact UX_nonneg hS hv

/-- **Prime event**: `U_X(p) ≥ 1` for every prime `p > z`. -/
theorem UX_ge_one_of_prime (hS : S.Good) {p : ℕ} (hp : p.Prime) (hpz : S.ztop < p) :
    1 ≤ S.UX p := by
  refine UX_majorant hS hp.ne_zero (fun q hq => ?_)
  rw [hp.primeFactors, Finset.mem_singleton] at hq
  rw [hq]; exact hpz

end ScalarParams

end Erdos287.Physical.Sieve
