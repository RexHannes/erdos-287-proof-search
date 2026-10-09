import RequestProject.Erdos287.SourceChain.Physical.Factorization.Atoms

/-!
# Erdős #287 — exact source decomposition of `ℓ_X` into legal three-factor atoms

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

An atom is `λ = (J, P, χ)` with `P ∈ 𝐃_J^+` and a prime colouring `χ`; its coefficient is
`(-1)^J w_{J,P}` and its three factors are

* `a₁ = κ_J * γ_{0,χ}` (`lowFactor`: low sieve weight times the colour-0 high primes),
* `a₂ = γ_{1,χ}`, `a₃ = γ_{2,χ}`,

all built from the Pascadi colouring of the sector (or any colouring rule `col`).

* `ellX_tensor` — exact identity `ℓ_X(d) = ∑_λ (-1)^J w_{J,P} (a₁ * a₂ * a₃)(d)` for every `d`;
* `abs_lowFactor_le`, `abs_colFactor_le` — all three factors are one-bounded;
* `lowFactor_support`, `colFactor_support` — size ranges `a₁ : n ≤ D_low E₀`, `a_k : m ≤ E_k`;
* `lowFactor_coprime_high`, `colFactor_coprime` — disjoint prime supports of the three factors;
* `atomWeight_nonneg`, `atomWeight_mul_le`, `total_variation_le` — total atom variation
  `∑_λ |(-1)^J w_{J,P}| ≤ ∑_{J ≤ T²} H^J 3^J`, and `H_eq_of_T`: `H` depends only on `T`
  (so the bound is independent of `X`).
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.Sieve.ScalarParams

open Erdos287.Physical.Factor

variable {S : ScalarParams}

variable (S) in
/-- **The first (low) factor** `a₁ = κ_J * γ_{0,χ}`. -/
noncomputable def lowFactor (J : ℕ) (P : Fin J → Fin S.H) (c : ℕ → Fin 3)
    (χ : Fin S.Kc → Fin 3) : ArithmeticFunction ℝ :=
  S.kappaAF J * S.colFactor J P c χ 0

lemma kappaAF_apply {J b : ℕ} (hb : b ≠ 0) : S.kappaAF J b = S.kappa J b := by
  simp [kappaAF, hb]

lemma lowFactor_term_ne {J n : ℕ} {P : Fin J → Fin S.H} {c : ℕ → Fin 3} {χ : Fin S.Kc → Fin 3}
    (h : S.lowFactor J P c χ n ≠ 0) :
    ∃ x ∈ n.divisorsAntidiagonal, S.kappa J x.1 ≠ 0 ∧ S.colFactor J P c χ 0 x.2 ≠ 0 := by
  unfold lowFactor at h
  rw [ArithmeticFunction.mul_apply] at h
  obtain ⟨x, hx, hne⟩ := exists_ne_zero_of_sum_ne_zero h
  have hx1 : x.1 ≠ 0 := Nat.pos_iff_ne_zero.1 (Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx))
  rw [kappaAF_apply hx1] at hne
  exact ⟨x, hx, left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩

/-- **The low factor is one-bounded** (unique low/high split). -/
theorem abs_lowFactor_le (hS : S.Good) {J : ℕ} (P : Fin J → Fin S.H) (c : ℕ → Fin 3)
    (χ : Fin S.Kc → Fin 3) (n : ℕ) : |S.lowFactor J P c χ n| ≤ 1 := by
  classical
  unfold lowFactor
  rw [ArithmeticFunction.mul_apply]
  refine abs_sum_le_one_of_unique _ _ ?_ ?_
  · have key : ∀ z ∈ n.divisorsAntidiagonal,
        S.kappaAF J z.1 * S.colFactor J P c χ 0 z.2 ≠ 0 →
        z.1 = ∏ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) < S.u0), p := by
      intro z hz hf
      obtain ⟨hzm, hn0⟩ := Nat.mem_divisorsAntidiagonal.1 hz
      have hz1 : z.1 ≠ 0 := fun h => hn0 (by rw [← hzm, h, zero_mul])
      rw [kappaAF_apply hz1] at hf
      obtain ⟨hsq, hlow⟩ := kappa_support (left_ne_zero_of_mul hf)
      obtain ⟨hz2, hhigh, -⟩ := colFactor_support hS (right_ne_zero_of_mul hf)
      have hpf : z.1.primeFactors = n.primeFactors.filter (fun p : ℕ => (p : ℝ) < S.u0) := by
        rw [← hzm, Nat.primeFactors_mul hz1 hz2]
        ext p
        simp only [mem_filter, mem_union]
        constructor
        · intro hp; exact ⟨Or.inl hp, hlow p hp⟩
        · rintro ⟨hp | hp, hlt⟩
          · exact hp
          · exact absurd hlt (not_low_of_high hS (hhigh p (Nat.prime_of_mem_primeFactors hp)
              (Nat.dvd_of_mem_primeFactors hp)).1)
      rw [← hpf, Nat.prod_primeFactors_of_squarefree hsq]
    intro x hx y hy hfx hfy
    have h1 := key x hx hfx
    have h2 := key y hy hfy
    obtain ⟨hxm, hn0⟩ := Nat.mem_divisorsAntidiagonal.1 hx
    obtain ⟨hym, -⟩ := Nat.mem_divisorsAntidiagonal.1 hy
    have hx1 : x.1 ≠ 0 := fun h => hn0 (by rw [← hxm, h, zero_mul])
    have heq1 : x.1 = y.1 := h1.trans h2.symm
    have heq2 : x.2 = y.2 := by
      have : x.1 * x.2 = x.1 * y.2 := by rw [hxm, heq1, hym]
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hx1) this
    exact Prod.ext heq1 heq2
  · intro x hx
    obtain ⟨hxm, hn0⟩ := Nat.mem_divisorsAntidiagonal.1 hx
    have hx1 : x.1 ≠ 0 := fun h => hn0 (by rw [← hxm, h, zero_mul])
    rw [kappaAF_apply hx1, abs_mul]
    exact mul_le_one₀ (abs_kappa_le J x.1) (abs_nonneg _) (abs_colFactor_le hS P c χ 0 x.2)

/-- **Size range of the low factor**: `a₁(n) ≠ 0 ⇒ n ≤ D_low E₀`. -/
theorem lowFactor_support (hS : S.Good) {J n : ℕ} {P : Fin J → Fin S.H} {c : ℕ → Fin 3}
    {χ : Fin S.Kc → Fin 3} (h : S.lowFactor J P c χ n ≠ 0) :
    (n : ℝ) ≤ S.Dlow * cprod (S.boxVec J P) c 0 J := by
  obtain ⟨x, hx, hk, hc⟩ := lowFactor_term_ne h
  obtain ⟨hxm, -⟩ := Nat.mem_divisorsAntidiagonal.1 hx
  have h1 := kappa_level hS hk
  obtain ⟨-, -, h2⟩ := colFactor_support hS hc
  rw [← hxm]; push_cast
  exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (by linarith [Dlow_ge_one hS])

/-- **Disjoint prime support**: colours 1 and 2 are coprime. -/
theorem colFactor_coprime (hS : S.Good) {J : ℕ} {P : Fin J → Fin S.H} {c : ℕ → Fin 3}
    {χ : Fin S.Kc → Fin 3} {k k' : Fin 3} (hkk : k ≠ k') {a a' : ℕ}
    (ha : S.colFactor J P c χ k a ≠ 0) (ha' : S.colFactor J P c χ k' a' ≠ 0) :
    Nat.Coprime a a' := by
  obtain ⟨-, h1, -⟩ := colFactor_support hS ha
  obtain ⟨-, h2, -⟩ := colFactor_support hS ha'
  refine Nat.coprime_of_dvd (fun p hp hpa hpa' => hkk ?_)
  rw [← (h1 p hp hpa).2, ← (h2 p hp hpa').2]

/-- **Disjoint prime support**: the low factor is coprime to `a₂ * a₃`. -/
theorem lowFactor_coprime_high (hS : S.Good) {J : ℕ} {P : Fin J → Fin S.H} {c : ℕ → Fin 3}
    {χ : Fin S.Kc → Fin 3} {l r : ℕ} (hl : S.lowFactor J P c χ l ≠ 0)
    (hr : (S.colFactor J P c χ 1 * S.colFactor J P c χ 2) r ≠ 0) : Nat.Coprime l r := by
  obtain ⟨x, hx, hk, hc⟩ := lowFactor_term_ne hl
  rw [ArithmeticFunction.mul_apply] at hr
  obtain ⟨y, hy, hne⟩ := exists_ne_zero_of_sum_ne_zero hr
  have hy1 := left_ne_zero_of_mul hne
  have hy2 := right_ne_zero_of_mul hne
  obtain ⟨hxm, -⟩ := Nat.mem_divisorsAntidiagonal.1 hx
  obtain ⟨hym, -⟩ := Nat.mem_divisorsAntidiagonal.1 hy
  obtain ⟨hsqb, hlow⟩ := kappa_support hk
  obtain ⟨-, h0, -⟩ := colFactor_support hS hc
  obtain ⟨-, h1, -⟩ := colFactor_support hS hy1
  obtain ⟨-, h2, -⟩ := colFactor_support hS hy2
  have hx1 : x.1 ≠ 0 := hsqb.ne_zero
  refine Nat.coprime_of_dvd (fun p hp hpl hpr => ?_)
  have hpr' : p ∣ y.1 ∨ p ∣ y.2 := by rw [← hym] at hpr; exact (Nat.Prime.dvd_mul hp).1 hpr
  have hhigh : S.IsHigh p ∧ (S.chiAt χ p = 1 ∨ S.chiAt χ p = 2) := by
    rcases hpr' with h | h
    · exact ⟨(h1 p hp h).1, Or.inl (h1 p hp h).2⟩
    · exact ⟨(h2 p hp h).1, Or.inr (h2 p hp h).2⟩
  rw [← hxm] at hpl
  rcases (Nat.Prime.dvd_mul hp).1 hpl with h | h
  · exact not_low_of_high hS hhigh.1 (hlow p (Nat.mem_primeFactors.2 ⟨hp, h, hx1⟩))
  · have := (h0 p hp h).2
    rcases hhigh.2 with h' | h' <;> rw [this] at h' <;> exact absurd h' (by decide)

/-! ### The exact decomposition of `ℓ_X` -/

lemma mul_scaleAF (f g : ArithmeticFunction ℝ) (r : ℝ) :
    f * scaleAF r g = scaleAF r (f * g) := by
  ext m
  simp only [ArithmeticFunction.mul_apply, scaleAF_apply, mul_sum]
  exact sum_congr rfl (fun x _ => by ring)

open Classical in
/-- **Exact decomposition of the actual scalar coefficient into legal three-factor atoms**,
for every modulus `d` and any colouring rule `col` (e.g. the Pascadi colouring). -/
theorem ellX_tensor (hS : S.Good) (col : (J : ℕ) → (Fin J → Fin S.H) → ℕ → Fin 3) (d : ℕ) :
    S.ellX d = ∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H,
      if S.BoxAdm J P then
        (-1 : ℝ) ^ J * S.atomWeight J P (col J P) * ∑ χ : Fin S.Kc → Fin 3,
          (S.lowFactor J P (col J P) χ * S.colFactor J P (col J P) χ 1 *
            S.colFactor J P (col J P) χ 2) d
      else 0 := by
  unfold ellX
  refine sum_congr rfl (fun J _ => sum_congr rfl (fun P _ => ?_))
  split_ifs with hP
  · have hA : ∑ x ∈ d.divisorsAntidiagonal, S.kappa J x.1 * S.Bcoef J P x.2 =
        (S.kappaAF J * S.bcoefAF J P) d := by
      rw [ArithmeticFunction.mul_apply]
      refine sum_congr rfl (fun x hx => ?_)
      obtain ⟨hxm, hd0⟩ := Nat.mem_divisorsAntidiagonal.1 hx
      have hx1 : x.1 ≠ 0 := fun h => hd0 (by rw [← hxm, h, zero_mul])
      have hx2 : x.2 ≠ 0 := fun h => hd0 (by rw [← hxm, h, mul_zero])
      simp [kappaAF, bcoefAF, hx1, hx2]
    rw [hA, bcoef_tensor hS P (col J P), mul_scaleAF, scaleAF_apply, mul_sum, af_sum_apply]
    rw [mul_assoc]
    congr 1; congr 1
    refine sum_congr rfl (fun χ _ => ?_)
    unfold lowFactor
    rw [← mul_assoc, ← mul_assoc]
  · rfl

/-! ### Weights and total variation -/

theorem atomWeight_nonneg {J : ℕ} (P : Fin J → Fin S.H) (c : ℕ → Fin 3) :
    0 ≤ S.atomWeight J P c := by
  unfold atomWeight; positivity

lemma prod_gammaCol_le {J : ℕ} (P : Fin J → Fin S.H) (c : ℕ → Fin 3) :
    ∏ k : Fin 3, S.gammaCol J P c k ≤ S.gammaP J P := by
  classical
  unfold gammaCol gammaP
  rw [prod_comm]
  refine prod_le_prod' (fun b _ => ?_)
  have hcard : (univ.filter (fun i : Fin J => P i = b)).card =
      ∑ k : Fin 3, (univ.filter (fun i : Fin J => c i.val = k ∧ P i = b)).card := by
    rw [card_eq_sum_card_fiberwise (f := fun i : Fin J => c i.val) (t := univ)
      (fun _ _ => mem_coe.2 (mem_univ _))]
    refine sum_congr rfl (fun k _ => ?_)
    rw [filter_filter]; congr 1; ext i; simp [and_comm]
  rw [hcard, Fin.prod_univ_three, Fin.sum_univ_three]
  set a := (univ.filter (fun i : Fin J => c i.val = 0 ∧ P i = b)).card
  set b' := (univ.filter (fun i : Fin J => c i.val = 1 ∧ P i = b)).card
  set e := (univ.filter (fun i : Fin J => c i.val = 2 ∧ P i = b)).card
  refine Nat.le_of_dvd (Nat.factorial_pos _) ?_
  calc a.factorial * b'.factorial * e.factorial ∣ (a + b').factorial * e.factorial :=
        Nat.mul_dvd_mul_right (Nat.factorial_mul_factorial_dvd_factorial_add a b') _
    _ ∣ (a + b' + e).factorial := Nat.factorial_mul_factorial_dvd_factorial_add _ _

/-- `3^K w_{J,P} ≤ 3^J`. -/
theorem atomWeight_mul_le {J : ℕ} (P : Fin J → Fin S.H) (c : ℕ → Fin 3) :
    S.atomWeight J P c * 3 ^ S.Kc ≤ 3 ^ J := by
  unfold atomWeight
  have hγP : (0 : ℝ) < S.gammaP J P := by exact_mod_cast gammaP_pos P
  have h3 : (0 : ℝ) < 3 ^ S.Kc := by positivity
  have hle : (∏ k : Fin 3, (S.gammaCol J P c k : ℝ)) ≤ S.gammaP J P := by
    exact_mod_cast prod_gammaCol_le P c
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have : (3 : ℝ) ^ J * (∏ k : Fin 3, (S.gammaCol J P c k : ℝ)) ≤ 3 ^ J * S.gammaP J P :=
    mul_le_mul_of_nonneg_left hle (by positivity)
  nlinarith

open Classical in
/-- **Total atom variation**: `∑_{J,P,χ} |(-1)^J w_{J,P}| ≤ ∑_{J ≤ T²} H^J 3^J`. -/
theorem total_variation_le (col : (J : ℕ) → (Fin J → Fin S.H) → ℕ → Fin 3) :
    ∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H,
      (if S.BoxAdm J P then ∑ _χ : Fin S.Kc → Fin 3, |(-1 : ℝ) ^ J * S.atomWeight J P (col J P)|
        else 0) ≤ ∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J := by
  refine sum_le_sum (fun J _ => ?_)
  have hcard : ∑ _P : Fin J → Fin S.H, (3 : ℝ) ^ J = (S.H : ℝ) ^ J * 3 ^ J := by
    rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    simp
  rw [← hcard]
  refine sum_le_sum (fun P _ => ?_)
  split_ifs
  · rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, abs_mul,
      abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (atomWeight_nonneg P _),
      nsmul_eq_mul]
    push_cast
    rw [mul_comm]; exact atomWeight_mul_le P _
  · positivity

/-- `D_j ≤ √D_int ↔ ε₀² (1+τ)^j ≤ 1/2`: the box count is determined by `T` alone. -/
lemma boxEnd_le_sqrt_iff (hS : S.Good) (j : ℕ) :
    S.boxEnd j ≤ Real.sqrt S.Dint ↔ S.eps0 ^ 2 * (1 + S.tau) ^ j ≤ 1 / 2 := by
  have hD := Dint_gt_one hS
  unfold boxEnd u0
  rw [← Real.rpow_mul (by linarith), Real.sqrt_eq_rpow, Real.rpow_le_rpow_left_iff hD]

/-- **The number of boxes `H` depends only on `T`** (not on `X`). -/
theorem H_eq_of_T {S' : ScalarParams} (hS : S.Good) (hS' : S'.Good) (hT : S.T = S'.T) :
    S.H = S'.H := by
  have he : S.eps0 = S'.eps0 := by unfold eps0; rw [hT]
  have ht : S.tau = S'.tau := by unfold tau; rw [he]
  have key : ∀ j, j < S.H ↔ j < S'.H := by
    intro j
    rw [lt_H_iff hS, lt_H_iff hS', boxEnd_le_sqrt_iff hS, boxEnd_le_sqrt_iff hS', he, ht]
  exact le_antisymm (not_lt.1 (fun h => lt_irrefl _ ((key _).1 h)))
    (not_lt.1 (fun h => lt_irrefl _ ((key _).2 h)))

end Erdos287.Physical.Sieve.ScalarParams
