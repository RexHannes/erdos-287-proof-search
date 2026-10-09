import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilyMaynard

/-!
# Erdős #287 — the Siegel–Walfisz condition (6.1) for the actual coefficients `alphaSeq`

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

The actual common sequence of a Type-II Heath–Brown cell is
`alphaSeq z z₀ j e c = dy (e c) (roughVar z₀ (hbVar z j c))`, i.e. one of

* the rough logarithm `1_{P^-(n) ≥ z₀} log n` (`c = 0`),
* the rough constant `1_{P^-(n) ≥ z₀}` (`c ∈ {1,2}`, when the variable is `ζ`),
* the rough truncated Möbius function `1_{P^-(n) ≥ z₀} μ(n) 1_{n ≤ z}` (`c ∈ {3,4,5}`),
* the Dirichlet unit `δ` (an unused variable),

restricted to the dyadic block `2^{e_c} ≤ n < 2^{e_c+1}`, which is Maynard's `n ∼ N` with
`N = 2^{e_c} - 1/2` (`simN_half`).

**External analytic input (paper level only, never assumed as an axiom).**  `IntervalSWAt g N B₀ c`
is Maynard's condition (6.1) for the *base* sequence `g` on every initial segment `(N, t]` of
`(N, 2N]`.  It is needed only for the two base sequences `roughOne z₀ = 1_{P^-(n) ≥ z₀}` and
`roughMu z₀ = μ · 1_{P^-(n) ≥ z₀}`.  For `μ` this is the Siegel–Walfisz theorem (it is a
consequence of Siegel's theorem and is not in Mathlib); see the accompanying report for the
paper-level discussion and the regime of `z₀`.

**Proved here (no further hypothesis):**

* `swCondition_iff_weight` — (6.1) rewritten with the weight
  `w(n) = 1_{n ≡ a (q), (n,d) = 1} - φ(q)⁻¹ 1_{(n, dq) = 1}`;
* `swCondition_of_intervalSW` — the full interval is an initial segment;
* `intervalSW_trunc` — truncation `n ≤ z` preserves interval-SW (the truncated Möbius case);
* `abel_bound` — discrete partial summation;
* `swCondition_log_of_intervalSW` — **logarithmic normalisation**: from interval-SW for `g`, the
  sequence `g(n) log n / (1 + log 2N)` satisfies (6.1) with constants `2 c_A`;
* `alphaSeq_swCondition` — (6.1) for every actual component `alphaSeq z z₀ j e c / alphaNorm e c`
  with constants `2 c_A`, uniformly in `z`, `j`, `e`, `c`;
* `alphaSeq_abs_le_tau` — the divisor-power bound `|alphaSeq / alphaNorm| ≤ τ(n)^{B₀}`.

The additional mask `(n, r) = 1` and its `τ(r)^{B₀}` loss are handled by the previously proved
`swCondition_masked`, which is applied inside `bdhEnergy_masked_le`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

set_option autoImplicit false

namespace Erdos287.Physical.TypeII.UremFamily

open Erdos287.Physical.TypeII

/-- The Siegel–Walfisz weight `w(n) = 1_{n ≡ a (q), (n,d)=1} - φ(q)⁻¹ 1_{(n,dq)=1}`. -/
noncomputable def swW (d q a n : ℕ) : ℝ :=
  (if n ≡ a [MOD q] ∧ Nat.Coprime n d then 1 else 0) -
    (1 / (Nat.totient q : ℝ)) * (if Nat.Coprime n (d * q) then 1 else 0)

lemma swExpr_eq (α : ℕ → ℝ) (N : ℝ) (d q a : ℕ) :
    (∑ n ∈ simN N with n ≡ a [MOD q] ∧ Nat.Coprime n d, α n -
      (1 / (Nat.totient q : ℝ)) * ∑ n ∈ simN N with Nat.Coprime n (d * q), α n) =
      ∑ n ∈ simN N, α n * swW d q a n := by
  simp only [sum_filter, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl (fun n _ => ?_)
  unfold swW
  split_ifs <;> ring

/-- (6.1) in weight form. -/
theorem swCondition_iff_weight (α : ℕ → ℝ) (N B0 : ℝ) (cSW : ℝ → ℝ) :
    SWCondition α N B0 cSW ↔ ∀ d q a : ℕ, 1 ≤ d → 1 ≤ q → Nat.Coprime a q → ∀ A : ℝ, 1 < A →
      |∑ n ∈ simN N, α n * swW d q a n| ≤ cSW A * N * tau d ^ B0 / Real.log N ^ A := by
  unfold SWCondition
  simp only [swExpr_eq]

/-- (6.1) depends only on the values on `n ∼ N`. -/
theorem swCondition_congr {α α' : ℕ → ℝ} {N B0 : ℝ} {cSW : ℝ → ℝ}
    (h : ∀ n ∈ simN N, α n = α' n) (hα : SWCondition α N B0 cSW) : SWCondition α' N B0 cSW := by
  rw [swCondition_iff_weight] at hα ⊢
  intro d q a hd hq haq A hA
  have e : ∑ n ∈ simN N, α' n * swW d q a n = ∑ n ∈ simN N, α n * swW d q a n :=
    sum_congr rfl (fun n hn => by rw [h n hn])
  rw [e]
  exact hα d q a hd hq haq A hA

/-- **Interval Siegel–Walfisz condition** at scale `N`: (6.1) for `g` on every initial segment
`(N, t]` of `(N, 2N]`. -/
def IntervalSWAt (g : ℕ → ℝ) (N B0 : ℝ) (cSW : ℝ → ℝ) : Prop :=
  ∀ t : ℕ, ∀ d q a : ℕ, 1 ≤ d → 1 ≤ q → Nat.Coprime a q → ∀ A : ℝ, 1 < A →
    |∑ n ∈ simN N with n ≤ t, g n * swW d q a n| ≤ cSW A * N * tau d ^ B0 / Real.log N ^ A

lemma simN_filter_le_floor (N : ℝ) : (simN N).filter (fun n => n ≤ ⌊2 * N⌋₊) = simN N := by
  ext n
  simp only [simN, mem_filter, mem_range]
  constructor
  · rintro ⟨h, -⟩; exact h
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, by omega⟩

/-- The whole interval is an initial segment. -/
theorem swCondition_of_intervalSW {g : ℕ → ℝ} {N B0 : ℝ} {cSW : ℝ → ℝ}
    (h : IntervalSWAt g N B0 cSW) : SWCondition g N B0 cSW := by
  rw [swCondition_iff_weight]
  intro d q a hd hq haq A hA
  have := h ⌊2 * N⌋₊ d q a hd hq haq A hA
  rwa [simN_filter_le_floor] at this

/-- The right-hand side of interval-SW is nonnegative (take the empty segment). -/
lemma intervalSW_rhs_nonneg {g : ℕ → ℝ} {N B0 : ℝ} {cSW : ℝ → ℝ} (hN : 0 ≤ N)
    (h : IntervalSWAt g N B0 cSW) {d : ℕ} (hd : 1 ≤ d) {A : ℝ} (hA : 1 < A) :
    0 ≤ cSW A * N * tau d ^ B0 / Real.log N ^ A := by
  have h0 := h 0 d 1 0 hd le_rfl (Nat.coprime_one_right 0) A hA
  have hempty : (simN N).filter (fun n => n ≤ 0) = ∅ := by
    ext n
    simp only [simN, mem_filter, mem_range, Finset.notMem_empty, iff_false, not_and]
    rintro ⟨_, h1⟩ h2
    have : n = 0 := by omega
    subst this
    simp at h1
    linarith
  rw [hempty, sum_empty, abs_zero] at h0
  exact h0

/-- **Truncation** `n ≤ z` preserves interval-SW. -/
theorem intervalSW_trunc {g : ℕ → ℝ} {N B0 : ℝ} {cSW : ℝ → ℝ} (h : IntervalSWAt g N B0 cSW)
    (z : ℕ) : IntervalSWAt (fun n => if n ≤ z then g n else 0) N B0 cSW := by
  intro t d q a hd hq haq A hA
  have := h (min t z) d q a hd hq haq A hA
  convert this using 2
  rw [sum_filter, sum_filter]
  refine sum_congr rfl (fun n _ => ?_)
  by_cases h1 : n ≤ t <;> by_cases h2 : n ≤ z <;> simp [h1, h2]

/-- A sequence vanishing on `n ∼ N` satisfies (6.1) as soon as the right-hand side is
nonnegative. -/
theorem swCondition_of_vanish {α g : ℕ → ℝ} {N B0 : ℝ} {cSW : ℝ → ℝ} (hN : 0 ≤ N)
    (h : IntervalSWAt g N B0 cSW) (hα : ∀ n ∈ simN N, α n = 0) {k : ℝ} (hk : 0 ≤ k) :
    SWCondition α N B0 (fun A => k * cSW A) := by
  rw [swCondition_iff_weight]
  intro d q a hd hq haq A hA
  rw [sum_eq_zero (fun n hn => by rw [hα n hn, zero_mul]), abs_zero]
  have := intervalSW_rhs_nonneg hN h hd hA
  have e : k * cSW A * N * tau d ^ B0 / Real.log N ^ A =
      k * (cSW A * N * tau d ^ B0 / Real.log N ^ A) := by ring
  rw [e]; positivity

/-- Enlarging the constant by a factor `k ≥ 1`. -/
theorem swCondition_const_mono {α g : ℕ → ℝ} {N B0 : ℝ} {cSW : ℝ → ℝ} (hN : 0 ≤ N)
    (h : IntervalSWAt g N B0 cSW) (hα : SWCondition α N B0 cSW) {k : ℝ} (hk : 1 ≤ k) :
    SWCondition α N B0 (fun A => k * cSW A) := by
  rw [swCondition_iff_weight] at hα ⊢
  intro d q a hd hq haq A hA
  refine (hα d q a hd hq haq A hA).trans ?_
  have := intervalSW_rhs_nonneg hN h hd hA
  have e : k * cSW A * N * tau d ^ B0 / Real.log N ^ A =
      k * (cSW A * N * tau d ^ B0 / Real.log N ^ A) := by ring
  rw [e]; nlinarith

/-- **Discrete partial summation.**  If every initial partial sum of `c` over `(a, t]`
(`a ≤ t ≤ b`) is at most `E` in absolute value and `L` is nonnegative and nondecreasing on
`[a, b]`, then `|∑_{a < n ≤ b} c(n) L(n)| ≤ 2 E L(b)`. -/
theorem abel_bound (a m : ℕ) (c L : ℕ → ℝ) (E : ℝ)
    (hL : ∀ t, a ≤ t → t < a + m → L t ≤ L (t + 1)) (hL0 : 0 ≤ L a)
    (hS : ∀ t, a ≤ t → t ≤ a + m → |∑ n ∈ Ioc a t, c n| ≤ E) :
    |∑ n ∈ Ioc a (a + m), c n * L n| ≤ 2 * E * L (a + m) := by
  set S : ℕ → ℝ := fun t => ∑ n ∈ Ioc a t, c n with hSdef
  -- Abel identity
  have abel : ∀ k ≤ m, ∑ n ∈ Ioc a (a + k), c n * L n =
      S (a + k) * L (a + k) - ∑ t ∈ Ico a (a + k), S t * (L (t + 1) - L t) := by
    intro k hk
    induction k with
    | zero => simp [hSdef]
    | succ k ih =>
      have hk' : k ≤ m := by omega
      rw [show a + (k + 1) = a + k + 1 by ring, sum_Ioc_succ_top (by omega),
        ih hk', sum_Ico_succ_top (by omega)]
      have hS1 : S (a + k + 1) = S (a + k) + c (a + k + 1) := by
        simp only [hSdef]; rw [sum_Ioc_succ_top (by omega)]
      rw [hS1]; ring
  -- the correction sum
  have hE : 0 ≤ E := (abs_nonneg _).trans (hS a le_rfl (by omega))
  have corr : ∀ k ≤ m, |∑ t ∈ Ico a (a + k), S t * (L (t + 1) - L t)| ≤ E * (L (a + k) - L a) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show a + (k + 1) = a + k + 1 by ring, sum_Ico_succ_top (by omega)]
      have hmono : 0 ≤ L (a + k + 1) - L (a + k) := by
        have := hL (a + k) (by omega) (by omega); linarith
      have h1 := ih (by omega)
      have h2 : |S (a + k) * (L (a + k + 1) - L (a + k))| ≤ E * (L (a + k + 1) - L (a + k)) := by
        rw [abs_mul, abs_of_nonneg hmono]
        exact mul_le_mul_of_nonneg_right (hS (a + k) (by omega) (by omega)) hmono
      calc _ ≤ |∑ t ∈ Ico a (a + k), S t * (L (t + 1) - L t)| +
            |S (a + k) * (L (a + k + 1) - L (a + k))| := abs_add_le _ _
        _ ≤ E * (L (a + k) - L a) + E * (L (a + k + 1) - L (a + k)) := add_le_add h1 h2
        _ = E * (L (a + k + 1) - L a) := by ring
  rw [abel m le_rfl]
  have hLm : L a ≤ L (a + m) := by
    have : ∀ k ≤ m, L a ≤ L (a + k) := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        have := hL (a + k) (by omega) (by omega)
        rw [show a + (k + 1) = a + k + 1 by ring]; linarith [ih (by omega)]
    exact this m le_rfl
  have h1 : |S (a + m) * L (a + m)| ≤ E * L (a + m) := by
    rw [abs_mul, abs_of_nonneg (hL0.trans hLm)]
    exact mul_le_mul_of_nonneg_right (hS (a + m) (by omega) le_rfl) (hL0.trans hLm)
  calc _ ≤ |S (a + m) * L (a + m)| + |∑ t ∈ Ico a (a + m), S t * (L (t + 1) - L t)| :=
        abs_sub _ _
    _ ≤ E * L (a + m) + E * (L (a + m) - L a) := add_le_add h1 (corr m le_rfl)
    _ ≤ 2 * E * L (a + m) := by nlinarith

/-- `n ∼ N` as an `Ioc` of naturals (`N ≥ 0`). -/
lemma simN_eq_Ioc {N : ℝ} (hN : 0 ≤ N) : simN N = Ioc ⌊N⌋₊ ⌊2 * N⌋₊ := by
  ext n
  simp only [simN, mem_filter, mem_range, mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨Nat.floor_lt hN |>.2 h2, by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, (Nat.floor_lt hN).1 h1⟩

lemma simN_filter_eq_Ioc {N : ℝ} (hN : 0 ≤ N) (t : ℕ) :
    (simN N).filter (fun n => n ≤ t) = Ioc ⌊N⌋₊ t ∩ simN N := by
  ext n; simp only [mem_filter, mem_inter, mem_Ioc, simN_eq_Ioc hN]; omega

/-- **Logarithmic normalisation.**  From interval-SW for `g`, the normalised logarithmic
sequence `g(n) log n / (1 + log 2N)` satisfies (6.1) with constants `2 c_A`. -/
theorem swCondition_log_of_intervalSW {g : ℕ → ℝ} {N B0 : ℝ} {cSW : ℝ → ℝ} (hN : 2 ≤ N)
    (h : IntervalSWAt g N B0 cSW) :
    SWCondition (fun n => g n * Real.log n / (1 + Real.log (2 * N))) N B0
      (fun A => 2 * cSW A) := by
  have hN0 : 0 ≤ N := by linarith
  rw [swCondition_iff_weight]
  intro d q a hd hq haq A hA
  set E := cSW A * N * tau d ^ B0 / Real.log N ^ A with hEdef
  set W := 1 + Real.log (2 * N) with hW
  have hlog2N : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
  have hW0 : 0 < W := by linarith
  set a0 := ⌊N⌋₊
  set b0 := ⌊2 * N⌋₊
  have hab : a0 ≤ b0 := Nat.floor_le_floor (by linarith)
  obtain ⟨m, hm⟩ : ∃ m, b0 = a0 + m := ⟨b0 - a0, by omega⟩
  have e1 : ∑ n ∈ simN N, g n * Real.log n / W * swW d q a n =
      (1 / W) * ∑ n ∈ Ioc a0 (a0 + m), (g n * swW d q a n) * Real.log n := by
    rw [simN_eq_Ioc hN0, ← hm, mul_sum]
    refine sum_congr rfl (fun n _ => ?_)
    field_simp
  rw [e1, abs_mul, abs_of_pos (by positivity)]
  have hsegs : ∀ t, a0 ≤ t → t ≤ a0 + m → |∑ n ∈ Ioc a0 t, g n * swW d q a n| ≤ E := by
    intro t _ ht
    have := h t d q a hd hq haq A hA
    rw [sum_filter] at this
    have e : ∑ n ∈ simN N, (if n ≤ t then g n * swW d q a n else 0) =
        ∑ n ∈ Ioc a0 t, g n * swW d q a n := by
      rw [simN_eq_Ioc hN0, ← sum_filter]
      congr 1
      ext n; simp only [mem_filter, mem_Ioc]; omega
    rw [e] at this
    exact this
  have hLmono : ∀ t, a0 ≤ t → t < a0 + m → Real.log (t : ℕ) ≤ Real.log ((t + 1 : ℕ)) := by
    intro t _ _
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    · exact Real.log_le_log (by exact_mod_cast ht) (by push_cast; linarith)
  have hab' := abel_bound a0 m (fun n => g n * swW d q a n) (fun n => Real.log (n : ℕ)) E hLmono
    (Real.log_natCast_nonneg _) hsegs
  have hlogb : Real.log ((a0 + m : ℕ) : ℝ) ≤ W := by
    rw [← hm]
    rcases Nat.eq_zero_or_pos b0 with h0 | h0
    · rw [h0]; simp; linarith
    · have : ((b0 : ℕ) : ℝ) ≤ 2 * N := Nat.floor_le (by linarith)
      have := Real.log_le_log (by exact_mod_cast h0) this
      linarith
  have hE0 : 0 ≤ E := intervalSW_rhs_nonneg hN0 h hd hA
  calc 1 / W * |∑ n ∈ Ioc a0 (a0 + m), g n * swW d q a n * Real.log n|
      ≤ 1 / W * (2 * E * Real.log ((a0 + m : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hab' (by positivity)
    _ ≤ 1 / W * (2 * E * W) := by gcongr
    _ = 2 * cSW A * N * tau d ^ B0 / Real.log N ^ A := by
        rw [hEdef]; field_simp

/-! ### The actual coefficients -/

/-- The rough constant `1_{P^-(n) ≥ z₀}`. -/
noncomputable def roughOne (z₀ : ℕ) (n : ℕ) : ℝ := if Rough z₀ n then 1 else 0

/-- The rough Möbius function `μ(n) 1_{P^-(n) ≥ z₀}`. -/
noncomputable def roughMu (z₀ : ℕ) (n : ℕ) : ℝ := if Rough z₀ n then (μ n : ℝ) else 0

/-- Maynard's scale of the actual coefficient: `N = 2^{e_c} - 1/2`, so that `n ∼ N` is the dyadic
block `2^{e_c} ≤ n < 2^{e_c + 1}`. -/
noncomputable def alphaScale (e : Fin 6 → ℕ) (c : Fin 6) : ℝ := ((2 ^ e c : ℕ) : ℝ) - 1 / 2

/-- Normalisation of the actual coefficient: `1 + log 2N` for the logarithmic variable (`c = 0`),
`1` otherwise. -/
noncomputable def alphaNorm (e : Fin 6 → ℕ) (c : Fin 6) : ℝ :=
  if c = 0 then 1 + Real.log (2 * alphaScale e c) else 1

lemma alphaSeq_eq_on_simN (z z₀ j : ℕ) (e : Fin 6 → ℕ) (c : Fin 6) {n : ℕ}
    (hn : n ∈ simN (alphaScale e c)) :
    alphaSeq z z₀ j e c n = roughVar z₀ (hbVar z j c) n ∧ 2 ^ e c ≤ n := by
  unfold alphaScale at hn
  rw [simN_half Nat.one_le_two_pow, mem_Ico] at hn
  refine ⟨?_, hn.1⟩
  unfold alphaSeq
  rw [dy_apply, if_pos ⟨hn.1, by rw [pow_succ]; omega⟩]

lemma two_le_of_alphaScale {e : Fin 6 → ℕ} {c : Fin 6} (hN : 2 ≤ alphaScale e c) {n : ℕ}
    (hn : 2 ^ e c ≤ n) : 2 ≤ n := by
  unfold alphaScale at hN
  have : (2 : ℝ) < ((2 ^ e c : ℕ) : ℝ) := by linarith
  have : 2 < 2 ^ e c := by exact_mod_cast this
  omega

lemma roughVar_zeta_apply (z₀ : ℕ) {n : ℕ} (hn : n ≠ 0) :
    roughVar z₀ (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n = roughOne z₀ n := by
  rw [roughVar_apply, roughOne, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
    if_neg hn]
  simp

lemma roughVar_one_apply (z₀ : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    roughVar z₀ (1 : ArithmeticFunction ℝ) n = 0 := by
  simp [roughVar_apply, show n ≠ 1 by omega]

lemma roughVar_Mz_apply (z₀ z n : ℕ) :
    roughVar z₀ (Mz z) n = if n ≤ z then roughMu z₀ n else 0 := by
  rw [roughVar_apply, Mz_apply, roughMu]
  split_ifs <;> rfl

/-- (6.1) for the rough constant on `n ∼ N` (constant `2 c_A`). -/
lemma sw_zeta_case {z₀ : ℕ} {B0 : ℝ} {cSW : ℝ → ℝ} {α : ℕ → ℝ} {N : ℝ} (hN : 2 ≤ N)
    (h1 : IntervalSWAt (roughOne z₀) N B0 cSW) (hα : ∀ n ∈ simN N, roughOne z₀ n = α n) :
    SWCondition α N B0 (fun A => 2 * cSW A) :=
  swCondition_congr hα (swCondition_const_mono (by linarith) h1 (swCondition_of_intervalSW h1)
    (by norm_num))

/-- (6.1) for the rough truncated Möbius function on `n ∼ N` (constant `2 c_A`). -/
lemma sw_Mz_case {z₀ z : ℕ} {B0 : ℝ} {cSW : ℝ → ℝ} {α : ℕ → ℝ} {N : ℝ} (hN : 2 ≤ N)
    (hμ : IntervalSWAt (roughMu z₀) N B0 cSW)
    (hα : ∀ n ∈ simN N, (if n ≤ z then roughMu z₀ n else 0) = α n) :
    SWCondition α N B0 (fun A => 2 * cSW A) :=
  swCondition_congr hα (swCondition_const_mono (by linarith) (intervalSW_trunc hμ z)
    (swCondition_of_intervalSW (intervalSW_trunc hμ z)) (by norm_num))

/-- **Siegel–Walfisz condition (6.1) for every actual component of `alphaSeq`.**
Given Maynard's condition (6.1) on initial segments (`IntervalSWAt`) for the two base sequences
`1_{P^-(n) ≥ z₀}` and `μ(n) 1_{P^-(n) ≥ z₀}` at the scale `N = 2^{e_c} - 1/2`, the normalised actual
coefficient `alphaSeq z z₀ j e c / alphaNorm e c` satisfies (6.1) at the same scale with constants
`2 c_A`, uniformly in `z`, `j`, `e` and `c`. -/
theorem alphaSeq_swCondition {z₀ : ℕ} {B0 : ℝ} {cSW : ℝ → ℝ} (z j : ℕ) (e : Fin 6 → ℕ)
    (c : Fin 6) (hN : 2 ≤ alphaScale e c)
    (h1 : IntervalSWAt (roughOne z₀) (alphaScale e c) B0 cSW)
    (hμ : IntervalSWAt (roughMu z₀) (alphaScale e c) B0 cSW) :
    SWCondition (fun n => alphaSeq z z₀ j e c n / alphaNorm e c) (alphaScale e c) B0
      (fun A => 2 * cSW A) := by
  have hN0 : (0 : ℝ) ≤ alphaScale e c := by linarith
  have hsim := fun n (hn : n ∈ simN (alphaScale e c)) => alphaSeq_eq_on_simN z z₀ j e c hn
  have hn2 : ∀ n ∈ simN (alphaScale e c), 2 ≤ n :=
    fun n hn => two_le_of_alphaScale hN (hsim n hn).2
  by_cases hc0 : c = 0
  · subst hc0
    refine swCondition_congr (fun n hn => ?_) (swCondition_log_of_intervalSW hN h1)
    rw [(hsim n hn).1, alphaNorm, if_pos rfl, roughVar_apply, roughOne]
    simp only [hbVar, ArithmeticFunction.log_apply]
    split_ifs <;> simp
  have hnorm : alphaNorm e c = 1 := by rw [alphaNorm, if_neg hc0]
  simp only [hnorm, div_one]
  fin_cases c
  · exact absurd rfl hc0
  · by_cases hj : 2 ≤ j
    · refine sw_zeta_case hN h1 (fun n hn => ?_)
      rw [(hsim n hn).1]; simp only [hbVar, if_pos hj]
      rw [roughVar_zeta_apply z₀ (by have := hn2 n hn; omega)]
    · refine swCondition_of_vanish hN0 h1 (fun n hn => ?_) (by norm_num)
      rw [(hsim n hn).1]; simp only [hbVar, if_neg hj]
      exact roughVar_one_apply z₀ (hn2 n hn)
  · by_cases hj : 3 ≤ j
    · refine sw_zeta_case hN h1 (fun n hn => ?_)
      rw [(hsim n hn).1]; simp only [hbVar, if_pos hj]
      rw [roughVar_zeta_apply z₀ (by have := hn2 n hn; omega)]
    · refine swCondition_of_vanish hN0 h1 (fun n hn => ?_) (by norm_num)
      rw [(hsim n hn).1]; simp only [hbVar, if_neg hj]
      exact roughVar_one_apply z₀ (hn2 n hn)
  · refine sw_Mz_case (z := z) hN hμ (fun n hn => ?_)
    rw [(hsim n hn).1]; simp only [hbVar]
    rw [roughVar_Mz_apply]
  · by_cases hj : 2 ≤ j
    · refine sw_Mz_case (z := z) hN hμ (fun n hn => ?_)
      rw [(hsim n hn).1]; simp only [hbVar, if_pos hj]
      rw [roughVar_Mz_apply]
    · refine swCondition_of_vanish hN0 h1 (fun n hn => ?_) (by norm_num)
      rw [(hsim n hn).1]; simp only [hbVar, if_neg hj]
      exact roughVar_one_apply z₀ (hn2 n hn)
  · by_cases hj : 3 ≤ j
    · refine sw_Mz_case (z := z) hN hμ (fun n hn => ?_)
      rw [(hsim n hn).1]; simp only [hbVar, if_pos hj]
      rw [roughVar_Mz_apply]
    · refine swCondition_of_vanish hN0 h1 (fun n hn => ?_) (by norm_num)
      rw [(hsim n hn).1]; simp only [hbVar, if_neg hj]
      exact roughVar_one_apply z₀ (hn2 n hn)

/-- **Divisor-power bound for the normalised actual coefficient**:
`|alphaSeq z z₀ j e c n / alphaNorm e c| ≤ 1 ≤ τ(n)^{B₀}` on its support. -/
theorem alphaSeq_abs_le_tau {B0 : ℝ} (hB0 : 0 ≤ B0) (z z₀ j : ℕ) (e : Fin 6 → ℕ) (c : Fin 6)
    (hN : 2 ≤ alphaScale e c) (n : ℕ) :
    |alphaSeq z z₀ j e c n / alphaNorm e c| ≤ tau n ^ B0 := by
  by_cases h0 : alphaSeq z z₀ j e c n = 0
  · rw [h0, zero_div, abs_zero]; unfold tau; positivity
  obtain ⟨hlo, hhi, -⟩ := alpha_support z z₀ j e c h0
  have hn1 : 1 ≤ n := le_trans Nat.one_le_two_pow hlo
  have htau : 1 ≤ tau n ^ B0 := Real.one_le_rpow (one_le_tau hn1) hB0
  refine le_trans ?_ htau
  have hsim : n ∈ simN (alphaScale e c) := by
    unfold alphaScale; rw [simN_half Nat.one_le_two_pow, mem_Ico]
    exact ⟨hlo, by rw [pow_succ] at hhi; omega⟩
  have hval := (alphaSeq_eq_on_simN z z₀ j e c hsim).1
  have hn2 := two_le_of_alphaScale hN hlo
  by_cases hc0 : c = 0
  · subst hc0
    have hW : 0 < alphaNorm e 0 := by
      rw [alphaNorm, if_pos rfl]
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * alphaScale e 0 by linarith); linarith
    rw [abs_div, abs_of_pos hW, div_le_one hW, hval, roughVar_apply]
    simp only [hbVar, ArithmeticFunction.log_apply]
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hle : Real.log n ≤ Real.log (2 * alphaScale e 0) := by
      apply Real.log_le_log (by exact_mod_cast hn1)
      unfold alphaScale
      have : n + 1 ≤ 2 * 2 ^ e 0 := by rw [pow_succ] at hhi; omega
      have : ((n : ℕ) : ℝ) + 1 ≤ 2 * ((2 ^ e 0 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    rw [alphaNorm, if_pos rfl]
    split_ifs
    · rw [abs_of_nonneg hlog]; linarith
    · simp; linarith
  · rw [alphaNorm, if_neg hc0, div_one, hval, roughVar_apply]
    split_ifs
    · have hM : |Mz z n| ≤ 1 := by
        rw [Mz_apply]; split_ifs
        · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        · simp
      have hζ : |(ArithmeticFunction.zeta : ArithmeticFunction ℝ) n| ≤ 1 := by
        rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply]; split_ifs <;> simp
      have h1 : |(1 : ArithmeticFunction ℝ) n| ≤ 1 := by
        rw [ArithmeticFunction.one_apply]; split_ifs <;> simp
      fin_cases c
      · exact absurd rfl hc0
      all_goals simp only [hbVar]; (try split_ifs) <;> assumption
    · simp

end Erdos287.Physical.TypeII.UremFamily
