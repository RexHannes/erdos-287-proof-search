import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilyAggregate

/-!
# Erdős #287 — the Urem estimate for an actual Heath–Brown cell

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

* `physUrem_smul_left`, `physUrem_sum_right` — `physUrem` is linear in `α` and in `β`;
* `prod_support_le`, `betaSeq_lt` — the actual `β` is supported on `m < 2^{E}`,
  `E = ∑_{i ≠ c} (e_i + 1) + 1`;
* `betaSeq_eq_sum_dy` — exact dyadic splitting of the actual `β` into pieces `dy k β`;
* `betaSeq_dy_sq_le` — the actual `β` second moment on `[2^k, 2^{k+1})`:
  `∑ β² ≤ (1 + log 2M)^{10} · 2M (1 + log 2M)^{256}`, `M = 2^k`.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.TypeII.UremFamily

open Erdos287.Physical Erdos287.Physical.TypeII Erdos287.Physical.Sieve
  Erdos287.Physical.Sieve.ScalarParams Erdos287.Physical.Factor

/-- The rescaled arithmetic function `n ↦ w α(n)`. -/
noncomputable def scaleAF (w : ℝ) (α : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => w * α n, by simp⟩

lemma scaleAF_apply (w : ℝ) (α : ArithmeticFunction ℝ) (n : ℕ) : scaleAF w α n = w * α n := rfl

lemma scaleAF_mul_apply (w : ℝ) (α β : ArithmeticFunction ℝ) (v : ℕ) :
    (scaleAF w α * β) v = w * (α * β) v := by
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, mul_sum]
  refine sum_congr rfl (fun x _ => ?_)
  rw [scaleAF_apply]; ring

/-- `physUrem` is homogeneous in `α`. -/
lemma physUrem_scale_left (S : ScalarParams) (δ N Γ : ℝ) (f c A : ℕ) (B : ℤ) (K K' : ℕ)
    (w : ℝ) (α β : ArithmeticFunction ℝ) :
    physUrem S δ N Γ f c A B K K' (scaleAF w α) β = w * physUrem S δ N Γ f c A B K K' α β := by
  unfold physUrem
  simp only [scaleAF_mul_apply, mul_sum]
  refine sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ =>
    sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => ?_)))))
  refine sum_congr rfl (fun _ _ => ?_)
  ring

lemma physUrem_add_right (S : ScalarParams) (δ N Γ : ℝ) (f c A : ℕ) (B : ℤ) (K K' : ℕ)
    (α β₁ β₂ : ArithmeticFunction ℝ) :
    physUrem S δ N Γ f c A B K K' α (β₁ + β₂) =
      physUrem S δ N Γ f c A B K K' α β₁ + physUrem S δ N Γ f c A B K K' α β₂ := by
  unfold physUrem
  simp only [mul_add, ArithmeticFunction.add_apply, add_mul, sum_add_distrib]

lemma physUrem_zero_right (S : ScalarParams) (δ N Γ : ℝ) (f c A : ℕ) (B : ℤ) (K K' : ℕ)
    (α : ArithmeticFunction ℝ) : physUrem S δ N Γ f c A B K K' α 0 = 0 := by
  unfold physUrem
  simp

/-- `physUrem` is additive in `β`. -/
lemma physUrem_sum_right (S : ScalarParams) (δ N Γ : ℝ) (f c A : ℕ) (B : ℤ) (K K' : ℕ)
    (α : ArithmeticFunction ℝ) {ι : Type*} (s : Finset ι) (β : ι → ArithmeticFunction ℝ) :
    physUrem S δ N Γ f c A B K K' α (∑ k ∈ s, β k) =
      ∑ k ∈ s, physUrem S δ N Γ f c A B K K' α (β k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [physUrem_zero_right]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, physUrem_add_right, ih]

/-- Support of a convolution product: if `f_i(a) ≠ 0 ⇒ a ≤ U_i`, then
`(∏ f_i)(m) ≠ 0 ⇒ m ≤ ∏ U_i`. -/
lemma prod_support_le {ι : Type*} (s : Finset ι) (f : ι → ArithmeticFunction ℝ) (U : ι → ℕ)
    (hU : ∀ i ∈ s, ∀ a, f i a ≠ 0 → a ≤ U i) :
    ∀ m, (∏ i ∈ s, f i) m ≠ 0 → m ≤ ∏ i ∈ s, U i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro m hm
    rw [prod_empty, ArithmeticFunction.one_apply] at hm
    split_ifs at hm with h
    · simp [h]
    · exact absurd rfl hm
  | insert a s ha ih =>
    intro m hm
    rw [prod_insert ha, ArithmeticFunction.mul_apply] at hm
    obtain ⟨x, hx, hne⟩ := exists_ne_zero_of_sum_ne_zero hm
    obtain ⟨hxm, -⟩ := Nat.mem_divisorsAntidiagonal.1 hx
    have h1 : f a x.1 ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have h2 : (∏ i ∈ s, f i) x.2 ≠ 0 := fun h => hne (by rw [h, mul_zero])
    rw [prod_insert ha, ← hxm]
    exact Nat.mul_le_mul (hU a (mem_insert_self a s) _ h1)
      (ih (fun i hi => hU i (mem_insert_of_mem hi)) _ h2)

/-- The dyadic exponent bounding the support of the actual `β`. -/
def betaTop (e : Fin 6 → ℕ) (c : Fin 6) : ℕ := ∑ i ∈ univ.erase c, (e i + 1) + 1

/-- **Support of the actual `β`**: `β_m ≠ 0 ⇒ m < 2^{E}`. -/
theorem betaSeq_lt (z z₀ j : ℕ) (e : Fin 6 → ℕ) (c : Fin 6) {m : ℕ}
    (hm : betaSeq z z₀ j e c m ≠ 0) : m < 2 ^ betaTop e c := by
  have h := prod_support_le (univ.erase c) (fun i => dy (e i) (roughVar z₀ (hbVar z j i)))
    (fun i => 2 ^ (e i + 1)) (fun i _ a ha => by
      rw [dy_apply] at ha
      split_ifs at ha with h
      · exact h.2.le
      · exact absurd rfl ha) m hm
  rw [prod_pow_eq_pow_sum] at h
  unfold betaTop
  rw [pow_succ]
  have : 0 < 2 ^ ∑ i ∈ univ.erase c, (e i + 1) := by positivity
  omega

/-- **Exact dyadic splitting of the actual `β`**: `β = ∑_{k < E} dy k β`. -/
theorem betaSeq_eq_sum_dy (z z₀ j : ℕ) (e : Fin 6 → ℕ) (c : Fin 6) :
    betaSeq z z₀ j e c = ∑ k ∈ range (betaTop e c), dy k (betaSeq z z₀ j e c) := by
  rw [← truncE_eq_sum_dy]
  ext m
  rw [truncE_apply]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (betaSeq_lt z z₀ j e c (by intro h'; exact hne (by rw [h'])))

lemma dy_support (k : ℕ) (g : ArithmeticFunction ℝ) :
    ∀ m, dy k g m ≠ 0 → 2 ^ k ≤ m ∧ m < 2 * 2 ^ k := by
  intro m hm
  rw [dy_apply] at hm
  split_ifs at hm with h
  · exact ⟨h.1, by rw [pow_succ] at h; omega⟩
  · exact absurd rfl hm

/-- The `β` energy bound used below. -/
noncomputable def betaEnergy (M : ℕ) : ℝ :=
  (1 + Real.log ((2 * M : ℕ) : ℝ)) ^ 10 *
    (((2 * M : ℕ) : ℝ) * (1 + Real.log ((2 * M : ℕ) : ℝ)) ^ 256)

/-- **The actual `β` second moment** on a dyadic block: for `M = 2^k`,
`∑_{M ≤ m < 2M} (dy k β)_m² ≤ (1 + log 2M)^{10} · 2M (1 + log 2M)^{256}`. -/
theorem betaSeq_dy_sq_le (z z₀ j : ℕ) (e : Fin 6 → ℕ) (c : Fin 6) (k : ℕ) :
    ∑ m ∈ Ico (2 ^ k) (2 * 2 ^ k), dy k (betaSeq z z₀ j e c) m ^ 2 ≤ betaEnergy (2 ^ k) := by
  set M := 2 ^ k
  have hL : 0 ≤ 1 + Real.log ((2 * M : ℕ) : ℝ) := one_add_log_nonneg _
  have hterm : ∀ m ∈ Ico M (2 * M), dy k (betaSeq z z₀ j e c) m ^ 2 ≤
      (1 + Real.log ((2 * M : ℕ) : ℝ)) ^ 10 * ((m.divisors.card : ℝ)) ^ 8 := by
    intro m hm
    obtain ⟨h1, h2⟩ := mem_Ico.1 hm
    have hM0 : 0 < M := by positivity
    have hm0 : m ≠ 0 := by omega
    have hb := abs_betaSeq_le z z₀ j e c (m := m)
    have hd := divisorPow_le 4 hm0
    have hlogm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
    have hlogle : 1 + Real.log m ≤ 1 + Real.log ((2 * M : ℕ) : ℝ) := by
      have : Real.log m ≤ Real.log ((2 * M : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hm0) (by exact_mod_cast h2.le)
      linarith
    have hz : 0 ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 5) m := zetaPow_nonneg 5 m
    have hβ : |dy k (betaSeq z z₀ j e c) m| ≤
        (1 + Real.log ((2 * M : ℕ) : ℝ)) ^ 5 * ((m.divisors.card : ℝ)) ^ 4 := by
      refine (abs_dy_le (by positivity) hb).trans ?_
      have h5 : (1 + Real.log m) ^ 5 ≤ (1 + Real.log ((2 * M : ℕ) : ℝ)) ^ 5 :=
        pow_le_pow_left₀ (by linarith) hlogle 5
      exact mul_le_mul h5 hd hz (by positivity)
    calc dy k (betaSeq z z₀ j e c) m ^ 2 = |dy k (betaSeq z z₀ j e c) m| ^ 2 := (sq_abs _).symm
      _ ≤ ((1 + Real.log ((2 * M : ℕ) : ℝ)) ^ 5 * ((m.divisors.card : ℝ)) ^ 4) ^ 2 := by
          gcongr
      _ = (1 + Real.log ((2 * M : ℕ) : ℝ)) ^ 10 * ((m.divisors.card : ℝ)) ^ 8 := by ring
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  unfold betaEnergy
  have h8 := sum_Ico_tau_pow_le M 8
  rw [show (2 : ℕ) ^ 8 = 256 by norm_num] at h8
  exact mul_le_mul_of_nonneg_left h8 (pow_nonneg hL _)

/-- The normalised actual coefficient `alphaSeq / alphaNorm` as an arithmetic function. -/
noncomputable def alphaNormed (z z₀ j : ℕ) (e : Fin 6 → ℕ) (c : Fin 6) : ArithmeticFunction ℝ :=
  ⟨fun n => alphaSeq z z₀ j e c n / alphaNorm e c, by simp⟩

lemma alphaNorm_pos {e : Fin 6 → ℕ} {c : Fin 6} (hN : 2 ≤ alphaScale e c) : 0 < alphaNorm e c := by
  unfold alphaNorm
  split_ifs
  · have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * alphaScale e c by linarith); linarith
  · norm_num

lemma alphaSeq_eq_scale (z z₀ j : ℕ) (e : Fin 6 → ℕ) (c : Fin 6) (hN : 2 ≤ alphaScale e c) :
    alphaSeq z z₀ j e c = scaleAF (alphaNorm e c) (alphaNormed z z₀ j e c) := by
  ext n
  rw [scaleAF_apply]
  change _ = alphaNorm e c * (alphaSeq z z₀ j e c n / alphaNorm e c)
  field_simp [(alphaNorm_pos hN).ne']

/-- **The Urem estimate for an actual Heath–Brown cell.**  For the actual coefficients
`α = alphaSeq z z₀ j e c` and `β = betaSeq z z₀ j e c` of a dyadic Heath–Brown cell, and the
literal packets `Ξ`, assuming

* Maynard I, Lemma 13.8 (`MaynardLemma13_8`, published, not formalized);
* the interval Siegel–Walfisz condition (6.1) for the two base sequences `1_{P^-(n) ≥ z₀}` and
  `μ(n) 1_{P^-(n) ≥ z₀}` at the scale `N' = 2^{e_c} - 1/2`, with constants `c_A`;
* the parameter conditions: divisor exponent `b ≥ 2k + 1`, `K ≤ 2^n`, `4·2^{e_c}·2^{E} ≤ K'`, base cap
  `f_ξ ≤ F`, band cap `l < 2^{n₀}`, `N' ≥ 2` and the modulus cutoff `2F2^{n₀} ≤ N'/(log N')^C`,

the packet sum `∑_ξ |physUrem_ξ(α, β)|` is at most `alphaNorm e c` times the sum over the dyadic
pieces `M = 2^k` (`k < E`) of the explicit bound of `actual_family_urem_explicit`, with
`B_β = betaEnergy M`.  The constants `C`, `C'` depend only on `b`, `c_A` and `A`. -/
theorem cell_urem_bound (hM : MaynardLemma13_8) {b : ℕ} (hb : 0 < b) (cSW : ℝ → ℝ)
    {Aexp : ℝ} (hAexp : 0 < Aexp) :
    ∃ C Cimp : ℝ, ∀ (P : PhysData), P.WGood → ∀ (Bf : ℝ), (∀ v i t, |P.fp v i t| ≤ Bf) →
    (2 * P.k : ℝ) + 1 ≤ b →
    ∀ (Ξ : Finset (Packet P.k)), Ξ ⊆ P.XiAll → ∀ (S : ScalarParams), S.Good →
    ∀ (δ N : ℝ) (K n n0 K' F : ℕ), K ≤ 2 ^ n →
    ∀ (z z₀ j : ℕ) (e : Fin 6 → ℕ) (c : Fin 6),
    4 * 2 ^ e c * 2 ^ betaTop e c ≤ K' →
    (∀ ξ ∈ Ξ, P.f ξ ≤ F) →
    (∀ ξ ∈ Ξ, ∀ J (Pb : Fin J → Fin S.H) (χ : Fin S.Kc → Fin 3) l r,
      physCoefCut S δ N (P.Gamma ξ) (P.f ξ) K J Pb χ l r ≠ 0 → l < 2 ^ n0) →
    2 ≤ alphaScale e c →
    IntervalSWAt (roughOne z₀) (alphaScale e c) b cSW →
    IntervalSWAt (roughMu z₀) (alphaScale e c) b cSW →
    ((2 * F * 2 ^ n0 : ℕ) : ℝ) ≤ alphaScale e c / Real.log (alphaScale e c) ^ C →
    ∑ ξ ∈ Ξ, |physUrem S δ N (P.Gamma ξ) (P.f ξ) (P.cRes ξ) (P.A ξ) (P.B ξ) K K'
        (alphaSeq z z₀ j e c) (betaSeq z z₀ j e c)| ≤
      alphaNorm e c * ∑ k ∈ range (betaTop e c),
        (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) * (1 + Real.log K) ^ (2 ^ (b + 1)) *
          n0 * Real.sqrt (betaEnergy (2 ^ k)) *
          Real.sqrt (((P.V * Bf ^ P.k) ^ 2 * (P.k : ℝ) ^ 2) * (1 + Real.log F) ^ (2 ^ (2 * P.k)) *
            ((2 ^ k : ℕ) + F * (2 ^ n0 : ℕ))) *
          Real.sqrt (((P.V * Bf ^ P.k) ^ 2 * (P.k : ℝ) ^ 2) *
            (Cimp * (alphaScale e c) ^ 2 / Real.log (alphaScale e c) ^ Aexp)) := by
  obtain ⟨C, Cimp, hC⟩ := actual_family_urem_explicit hM hb (fun A => 2 * cSW A) hAexp
  refine ⟨C, Cimp, ?_⟩
  intro P hP Bf hBf hkb Ξ hΞ S hS δ N K n n0 K' F hKn z z₀ j e c hK' hF hl0 hN h1 hμ hcut
  have hW := alphaNorm_pos hN
  have hsplit : ∀ ξ ∈ Ξ, |physUrem S δ N (P.Gamma ξ) (P.f ξ) (P.cRes ξ) (P.A ξ) (P.B ξ) K K'
        (alphaSeq z z₀ j e c) (betaSeq z z₀ j e c)| ≤
      alphaNorm e c * ∑ k ∈ range (betaTop e c), |physUrem S δ N (P.Gamma ξ) (P.f ξ) (P.cRes ξ)
        (P.A ξ) (P.B ξ) K K' (alphaNormed z z₀ j e c) (dy k (betaSeq z z₀ j e c))| := by
    intro ξ _
    conv_lhs => rw [alphaSeq_eq_scale z z₀ j e c hN, betaSeq_eq_sum_dy z z₀ j e c,
      physUrem_scale_left, physUrem_sum_right]
    rw [abs_mul, abs_of_pos hW]
    exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) hW.le
  refine (sum_le_sum hsplit).trans ?_
  rw [← mul_sum, sum_comm]
  refine mul_le_mul_of_nonneg_left (sum_le_sum (fun k hk => ?_)) hW.le
  have hk : k < betaTop e c := mem_range.1 hk
  have hK'k : 4 * 2 ^ e c * 2 ^ k ≤ K' :=
    le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hk.le)) hK'
  have hα : ∀ m, alphaNormed z z₀ j e c m ≠ 0 → 2 ^ e c ≤ m ∧ m < 2 * 2 ^ e c := by
    intro m hm
    have : alphaSeq z z₀ j e c m ≠ 0 := by
      intro h0; apply hm; change alphaSeq z z₀ j e c m / alphaNorm e c = 0; rw [h0, zero_div]
    obtain ⟨h1, h2, -⟩ := alpha_support z z₀ j e c this
    exact ⟨h1, by rw [pow_succ] at h2; omega⟩
  have hsw : SWCondition (alphaNormed z z₀ j e c) (((2 ^ e c : ℕ) : ℝ) - 1 / 2) (b : ℝ)
      (fun A => 2 * cSW A) := alphaSeq_swCondition z j e c hN h1 hμ
  have hdiv : ∀ m, |alphaNormed z z₀ j e c m| ≤ tau m ^ (b : ℝ) :=
    fun m => alphaSeq_abs_le_tau (by positivity) z z₀ j e c hN m
  exact hC P hP Bf hBf hkb Ξ hΞ S hS δ N K n n0 (2 ^ e c) (2 ^ k) K' F hKn
    (alphaNormed z z₀ j e c) (dy k (betaSeq z z₀ j e c)) hα (dy_support k _) hK'k hF
    (betaEnergy (2 ^ k)) (betaSeq_dy_sq_le z z₀ j e c k) hl0 hN hsw hdiv hcut

end Erdos287.Physical.TypeII.UremFamily
