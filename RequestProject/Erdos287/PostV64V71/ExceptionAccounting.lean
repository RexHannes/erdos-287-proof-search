import RequestProject.Erdos287.PostV64V71.DeterminantBox
import Mathlib.NumberTheory.Chebyshev

/-!
# Erdős #287 — V71 weighted determinant counts, exception loss, prime-power contamination

**Status: BANK (LEAN PROVED).**  Everything here is exact finite accounting over `detBox M H`.

* `thetaStar n = log n` if `n` is prime, `0` otherwise;
* `Dw w M H = ∑_{x ∈ detBox M H} w(q) w(r)`; `Dtheta = Dw thetaStar`, `DLambda = Dw Λ`
  (Mathlib's `ArithmeticFunction.vonMangoldt`, no local re-definition);
* `Dgg M H E` — the `θ*`-weighted count over tuples whose two owners avoid `E`;
* `fiber_sum_le` — abstract fibre lemma: grouping by a key with `≤ #K` values, each fibre
  carries `∑ Λ(d) ≤ ∑_{d ∣ n} Λ(d) = log n ≤ log M`;
* `fiber_q_le`, `fiber_r_le` — for a fixed owner, the partner weights sum to `≤ 2H log M`;
* `exception_weight_loss` — **V71**: `0 ≤ D_θ - D_θ^{gg}(E) ≤ 4 H (log M) B_E` with
  `B_E = ∑_{p∈E} log p`;
* `mangoldt_prime_power_error_exact` — `0 ≤ D_Λ - D_θ ≤ 4 H (log M) · PPW` where
  `PPW = ∑_{M/H < n ≤ M, n not prime} Λ(n)`;
* `PPW_le` — `PPW ≤ ψ(M) - θ(M) ≤ 2 √M log M` (Mathlib, `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`);
* `mangoldt_prime_power_error` — `0 ≤ D_Λ - D_θ ≤ 8 H √M (log M)²`.

**Audit note.**  The research text states the contamination bound with constant `4`
(`4 H √M L²`), which needs `ψ(M) - θ(M) ≤ √M log M`.  Mathlib's proved constant is `2`
(`ψ - θ ≤ 2 √x log x`), so the Lean-proved bound is `8 H √M L²`.  The tail closure margin
(`< M/L³` for `M ≥ 2^1500`) holds with the Lean constant, so nothing downstream changes.
-/

open scoped BigOperators

namespace Erdos287.PostV64V71

open Erdos287

/-- `θ*(n) = log n` if `n` is prime and `0` otherwise. -/
noncomputable def thetaStar (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

/-- The von Mangoldt weight (Mathlib's `ArithmeticFunction.vonMangoldt`, as a function `ℕ → ℝ`). -/
noncomputable def LambdaW (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n

theorem LambdaW_nonneg (n : ℕ) : 0 ≤ LambdaW n := ArithmeticFunction.vonMangoldt_nonneg

theorem thetaStar_nonneg (n : ℕ) : 0 ≤ thetaStar n := by
  unfold thetaStar; split_ifs
  · exact Real.log_natCast_nonneg n
  · exact le_rfl

theorem thetaStar_le_LambdaW (n : ℕ) : thetaStar n ≤ LambdaW n := by
  unfold thetaStar LambdaW; split_ifs with h
  · rw [ArithmeticFunction.vonMangoldt_apply_prime h]
  · exact ArithmeticFunction.vonMangoldt_nonneg

theorem thetaStar_le_log (n : ℕ) : thetaStar n ≤ Real.log n := by
  unfold thetaStar; split_ifs
  · exact le_rfl
  · exact Real.log_natCast_nonneg n

theorem thetaStar_of_prime {n : ℕ} (h : n.Prime) : thetaStar n = LambdaW n := by
  unfold thetaStar LambdaW; rw [if_pos h, ArithmeticFunction.vonMangoldt_apply_prime h]

theorem thetaStar_of_not_prime {n : ℕ} (h : ¬ n.Prime) : thetaStar n = 0 := by
  unfold thetaStar; rw [if_neg h]

/-- Weighted determinant count `∑_{x∈box} w(q) w(r)`. -/
noncomputable def Dw (w : ℕ → ℝ) (M H : ℕ) : ℝ := ∑ x ∈ detBox M H, w x.q * w x.r

/-- `D_θ(M)`. -/
noncomputable def Dtheta (M H : ℕ) : ℝ := Dw thetaStar M H

/-- `D_Λ(M)` (V71 von Mangoldt determinant count). -/
noncomputable def DLambda (M H : ℕ) : ℝ := Dw LambdaW M H

/-- `D_θ^{gg}(M, E)`: only tuples whose two owners avoid `E`. -/
noncomputable def Dgg (M H : ℕ) (E : Finset ℕ) : ℝ :=
  ∑ x ∈ (detBox M H).filter (fun x => x.q ∉ E ∧ x.r ∉ E), thetaStar x.q * thetaStar x.r

/-! ## The abstract fibre lemma -/

/-- **Abstract fibre lemma.**  Group a finite family `s` by a key with values in `K`.  If in
each fibre the "other owner" `o x` determines `x` and divides a common nonzero `n ≤ M`, then for
any weight `0 ≤ w ≤ Λ`, `∑_{x∈s} w(o x) ≤ #K · log M`. -/
theorem fiber_sum_le {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (K : Finset κ)
    (key : ι → κ) (o : ι → ℕ) (n : κ → ℕ) (M : ℕ)
    (hK : ∀ x ∈ s, key x ∈ K) (hdvd : ∀ x ∈ s, o x ∣ n (key x))
    (hn0 : ∀ x ∈ s, n (key x) ≠ 0) (hle : ∀ x ∈ s, n (key x) ≤ M)
    (hinj : ∀ x ∈ s, ∀ x' ∈ s, key x = key x' → o x = o x' → x = x')
    (w : ℕ → ℝ) (hwΛ : ∀ m, w m ≤ LambdaW m) :
    ∑ x ∈ s, w (o x) ≤ K.card * Real.log M := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hK]
  have hlogM : 0 ≤ Real.log M := Real.log_natCast_nonneg M
  calc ∑ c ∈ K, ∑ x ∈ s with key x = c, w (o x) ≤ ∑ _c ∈ K, Real.log M := by
        refine Finset.sum_le_sum fun c _ => ?_
        set s' := s.filter (fun x => key x = c)
        rcases s'.eq_empty_or_nonempty with he | ⟨x0, hx0⟩
        · rw [he, Finset.sum_empty]; exact hlogM
        have hx0' := Finset.mem_filter.1 hx0
        have hkey : ∀ x ∈ s', key x = c := fun x hx => (Finset.mem_filter.1 hx).2
        have hn0' : n c ≠ 0 := hx0'.2 ▸ hn0 x0 hx0'.1
        have hle' : n c ≤ M := hx0'.2 ▸ hle x0 hx0'.1
        have hinj' : Set.InjOn o s' := by
          intro x hx x' hx' hoo
          exact hinj x (Finset.mem_filter.1 hx).1 x' (Finset.mem_filter.1 hx').1
            ((hkey x hx).trans (hkey x' hx').symm) hoo
        rw [← Finset.sum_image (f := w) hinj']
        have hsub : s'.image o ⊆ (n c).divisors := by
          intro d hd
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hd
          rw [Nat.mem_divisors]
          exact ⟨hkey x hx ▸ hdvd x (Finset.mem_filter.1 hx).1, hn0'⟩
        calc ∑ d ∈ s'.image o, w d ≤ ∑ d ∈ s'.image o, LambdaW d :=
              Finset.sum_le_sum fun d _ => hwΛ d
          _ ≤ ∑ d ∈ (n c).divisors, LambdaW d :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => LambdaW_nonneg d
          _ = Real.log (n c) := ArithmeticFunction.vonMangoldt_sum
          _ ≤ Real.log M := by
              apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn0')
              exact_mod_cast hle'
    _ = K.card * Real.log M := by rw [Finset.sum_const, nsmul_eq_mul]

theorem toNat_q_eq {M H : ℕ} {x : DTup} (hx : x ∈ detBox M H) :
    ((x.k * x.q : ℕ) - x.eps : ℤ).toNat = x.t * x.r := by
  rw [← (detBox_facts hx).2.2.2.2, Int.toNat_natCast]

theorem toNat_r_eq {M H : ℕ} {x : DTup} (hx : x ∈ detBox M H) :
    ((x.t * x.r : ℕ) + x.eps : ℤ).toNat = x.k * x.q := by
  have h' : ((x.t * x.r : ℕ) : ℤ) + x.eps = ((x.k * x.q : ℕ) : ℤ) := by
    linarith [(detBox_facts hx).2.2.2.2]
  rw [h', Int.toNat_natCast]

theorem card_key_set (H : ℕ) : (Finset.Icc 1 H ×ˢ ({1, -1} : Finset ℤ)).card ≤ 2 * H := by
  rw [Finset.card_product]; simp only [Nat.card_Icc, add_tsub_cancel_right]
  rw [mul_comm]; exact Nat.mul_le_mul_right _ Finset.card_le_two

/-- **Fixed first owner**: `∑_{x ∈ box, q = q₀} w(r) ≤ 2 H log M` for `w ≤ Λ`. -/
theorem fiber_q_le (M H q₀ : ℕ) (w : ℕ → ℝ)
    (hwΛ : ∀ m, w m ≤ LambdaW m) :
    ∑ x ∈ (detBox M H).filter (fun x => x.q = q₀), w x.r ≤ 2 * H * Real.log M := by
  set s := (detBox M H).filter (fun x => x.q = q₀)
  have h := fiber_sum_le s (Finset.Icc 1 H ×ˢ ({1, -1} : Finset ℤ)) (fun x => (x.k, x.eps))
    (fun x => x.r) (fun c => ((c.1 * q₀ : ℕ) - c.2 : ℤ).toNat) M ?_ ?_ ?_ ?_ ?_ w hwΛ
  · refine le_trans h ?_
    have := card_key_set H
    have hl := Real.log_natCast_nonneg M
    have : ((Finset.Icc 1 H ×ˢ ({1, -1} : Finset ℤ)).card : ℝ) ≤ 2 * H := by exact_mod_cast this
    nlinarith
  all_goals intro x hx
  all_goals have hxs := Finset.mem_filter.1 hx
  all_goals have m := mem_detBox.1 hxs.1
  all_goals have f := detBox_facts hxs.1
  all_goals have hq : x.q = q₀ := hxs.2
  all_goals have e : ((x.k * q₀ : ℕ) - x.eps : ℤ).toNat = x.t * x.r := by rw [← hq]; exact toNat_q_eq hxs.1
  · simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨m.1, m.2.2.2.2.1⟩
  · show x.r ∣ ((x.k * q₀ : ℕ) - x.eps : ℤ).toNat
    rw [e]; exact dvd_mul_left _ _
  · show ((x.k * q₀ : ℕ) - x.eps : ℤ).toNat ≠ 0
    rw [e]; omega
  · show ((x.k * q₀ : ℕ) - x.eps : ℤ).toNat ≤ M
    rw [e]; exact f.2.1
  · intro x' hx' hkey hrr
    have hxs' := Finset.mem_filter.1 hx'
    have m' := mem_detBox.1 hxs'.1
    have f' := detBox_facts hxs'.1
    simp only [Prod.mk.injEq] at hkey
    obtain ⟨hkk, hee⟩ := hkey
    have hqq : x.q = x'.q := hq.trans hxs'.2.symm
    have htr : x.t * x.r = x'.t * x'.r := by
      have e1 := f.2.2.2.2; have e2 := f'.2.2.2.2
      rw [← hkk, ← hqq, ← hee] at e2
      have : ((x.t * x.r : ℕ) : ℤ) = ((x'.t * x'.r : ℕ) : ℤ) := by linarith
      exact_mod_cast this
    have htt : x.t = x'.t := by
      simp only at hrr
      rw [hrr] at htr
      exact Nat.eq_of_mul_eq_mul_right (lt_of_le_of_lt (Nat.zero_le _) m'.2.2.2.1.1) htr
    obtain ⟨k, q, t, r, e⟩ := x
    obtain ⟨k', q', t', r', e'⟩ := x'
    simp only at hkk hqq htt hrr hee
    subst hkk hqq htt hrr hee
    rfl

/-- **Fixed second owner**: `∑_{x ∈ box, r = r₀} w(q) ≤ 2 H log M` for `w ≤ Λ`. -/
theorem fiber_r_le (M H r₀ : ℕ) (w : ℕ → ℝ)
    (hwΛ : ∀ m, w m ≤ LambdaW m) :
    ∑ x ∈ (detBox M H).filter (fun x => x.r = r₀), w x.q ≤ 2 * H * Real.log M := by
  set s := (detBox M H).filter (fun x => x.r = r₀)
  have h := fiber_sum_le s (Finset.Icc 1 H ×ˢ ({1, -1} : Finset ℤ)) (fun x => (x.t, x.eps))
    (fun x => x.q) (fun c => ((c.1 * r₀ : ℕ) + c.2 : ℤ).toNat) M ?_ ?_ ?_ ?_ ?_ w hwΛ
  · refine le_trans h ?_
    have := card_key_set H
    have hl := Real.log_natCast_nonneg M
    have : ((Finset.Icc 1 H ×ˢ ({1, -1} : Finset ℤ)).card : ℝ) ≤ 2 * H := by exact_mod_cast this
    nlinarith
  all_goals intro x hx
  all_goals have hxs := Finset.mem_filter.1 hx
  all_goals have m := mem_detBox.1 hxs.1
  all_goals have f := detBox_facts hxs.1
  all_goals have hr : x.r = r₀ := hxs.2
  all_goals have e : ((x.t * r₀ : ℕ) + x.eps : ℤ).toNat = x.k * x.q := by rw [← hr]; exact toNat_r_eq hxs.1
  · simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨m.2.2.1, m.2.2.2.2.1⟩
  · show x.q ∣ ((x.t * r₀ : ℕ) + x.eps : ℤ).toNat
    rw [e]; exact dvd_mul_left _ _
  · show ((x.t * r₀ : ℕ) + x.eps : ℤ).toNat ≠ 0
    rw [e]; omega
  · show ((x.t * r₀ : ℕ) + x.eps : ℤ).toNat ≤ M
    rw [e]; omega
  · intro x' hx' hkey hqq
    have hxs' := Finset.mem_filter.1 hx'
    have m' := mem_detBox.1 hxs'.1
    have f' := detBox_facts hxs'.1
    simp only [Prod.mk.injEq] at hkey
    obtain ⟨htt, hee⟩ := hkey
    have hrr : x.r = x'.r := hr.trans hxs'.2.symm
    have hkq : x.k * x.q = x'.k * x'.q := by
      have e1 := f.2.2.2.2; have e2 := f'.2.2.2.2
      rw [← htt, ← hrr, ← hee] at e2
      have : ((x.k * x.q : ℕ) : ℤ) = ((x'.k * x'.q : ℕ) : ℤ) := by linarith
      exact_mod_cast this
    have hkk : x.k = x'.k := by
      simp only at hqq
      rw [hqq] at hkq
      exact Nat.eq_of_mul_eq_mul_right (lt_of_le_of_lt (Nat.zero_le _) m'.2.1.1) hkq
    obtain ⟨k, q, t, r, e⟩ := x
    obtain ⟨k', q', t', r', e'⟩ := x'
    simp only at hkk hqq htt hrr hee
    subst hkk hqq htt hrr hee
    rfl

/-! ## Owner-restricted sums -/

/-- `∑_{x∈box, q∈S} u(q) w(r) ≤ (∑_{p∈S} u p) · 2H log M` for `u ≥ 0` and `w ≤ Λ`. -/
theorem sum_q_mem_le (M H : ℕ) (S : Finset ℕ) (u w : ℕ → ℝ) (hu : ∀ m, 0 ≤ u m)
    (hwΛ : ∀ m, w m ≤ LambdaW m) :
    ∑ x ∈ (detBox M H).filter (fun x => x.q ∈ S), u x.q * w x.r ≤
      (∑ p ∈ S, u p) * (2 * H * Real.log M) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : DTup => x.q) (t := S)
    (fun x hx => (Finset.mem_filter.1 hx).2), Finset.sum_mul]
  refine Finset.sum_le_sum fun p hp => ?_
  have hfil : ((detBox M H).filter (fun x => x.q ∈ S)).filter (fun x => x.q = p) =
      (detBox M H).filter (fun x => x.q = p) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun x _ => ⟨fun h => h.2, fun h => ⟨h ▸ hp, h⟩⟩
  rw [hfil]
  calc ∑ x ∈ (detBox M H).filter (fun x => x.q = p), u x.q * w x.r
      = ∑ x ∈ (detBox M H).filter (fun x => x.q = p), u p * w x.r :=
        Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.1 hx).2]
    _ = u p * ∑ x ∈ (detBox M H).filter (fun x => x.q = p), w x.r := by rw [Finset.mul_sum]
    _ ≤ u p * (2 * H * Real.log M) :=
        mul_le_mul_of_nonneg_left (fiber_q_le M H p w hwΛ) (hu p)

/-- `∑_{x∈box, r∈S} w(q) u(r) ≤ (∑_{p∈S} u p) · 2H log M` for `u ≥ 0` and `w ≤ Λ`. -/
theorem sum_r_mem_le (M H : ℕ) (S : Finset ℕ) (u w : ℕ → ℝ) (hu : ∀ m, 0 ≤ u m)
    (hwΛ : ∀ m, w m ≤ LambdaW m) :
    ∑ x ∈ (detBox M H).filter (fun x => x.r ∈ S), w x.q * u x.r ≤
      (∑ p ∈ S, u p) * (2 * H * Real.log M) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : DTup => x.r) (t := S)
    (fun x hx => (Finset.mem_filter.1 hx).2), Finset.sum_mul]
  refine Finset.sum_le_sum fun p hp => ?_
  have hfil : ((detBox M H).filter (fun x => x.r ∈ S)).filter (fun x => x.r = p) =
      (detBox M H).filter (fun x => x.r = p) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun x _ => ⟨fun h => h.2, fun h => ⟨h ▸ hp, h⟩⟩
  rw [hfil]
  calc ∑ x ∈ (detBox M H).filter (fun x => x.r = p), w x.q * u x.r
      = ∑ x ∈ (detBox M H).filter (fun x => x.r = p), u p * w x.q :=
        Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.1 hx).2, mul_comm]
    _ = u p * ∑ x ∈ (detBox M H).filter (fun x => x.r = p), w x.q := by rw [Finset.mul_sum]
    _ ≤ u p * (2 * H * Real.log M) :=
        mul_le_mul_of_nonneg_left (fiber_r_le M H p w hwΛ) (hu p)

/-! ## V71 exception deletion loss -/

/-- **V71 exception deletion loss**: `0 ≤ D_θ - D_θ^{gg}(E) ≤ 4 H (log M) ∑_{p∈E} log p`. -/
theorem exception_weight_loss (M H : ℕ) (E : Finset ℕ) :
    0 ≤ Dtheta M H - Dgg M H E ∧
      Dtheta M H - Dgg M H E ≤ 4 * H * Real.log M * ∑ p ∈ E, Real.log p := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (detBox M H)
    (fun x => x.q ∉ E ∧ x.r ∉ E) (fun x => thetaStar x.q * thetaStar x.r)
  have hdiff : Dtheta M H - Dgg M H E =
      ∑ x ∈ (detBox M H).filter (fun x => ¬ (x.q ∉ E ∧ x.r ∉ E)),
        thetaStar x.q * thetaStar x.r := by
    unfold Dtheta Dw Dgg; linarith
  have hnn : ∀ x : DTup, 0 ≤ thetaStar x.q * thetaStar x.r :=
    fun x => mul_nonneg (thetaStar_nonneg _) (thetaStar_nonneg _)
  constructor
  · rw [hdiff]; exact Finset.sum_nonneg fun x _ => hnn x
  rw [hdiff]
  have hle : ∑ x ∈ (detBox M H).filter (fun x => ¬ (x.q ∉ E ∧ x.r ∉ E)),
        thetaStar x.q * thetaStar x.r ≤
      ∑ x ∈ (detBox M H).filter (fun x => x.q ∈ E), thetaStar x.q * thetaStar x.r +
      ∑ x ∈ (detBox M H).filter (fun x => x.r ∈ E), thetaStar x.q * thetaStar x.r := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    have := hnn x
    by_cases h1 : x.q ∈ E <;> by_cases h2 : x.r ∈ E <;> (simp [h1, h2]; try linarith)
  have hq := sum_q_mem_le M H E thetaStar thetaStar thetaStar_nonneg
    thetaStar_le_LambdaW
  have hr := sum_r_mem_le M H E thetaStar thetaStar thetaStar_nonneg
    thetaStar_le_LambdaW
  have hlog : ∑ p ∈ E, thetaStar p ≤ ∑ p ∈ E, Real.log p :=
    Finset.sum_le_sum fun p _ => thetaStar_le_log p
  have hc : 0 ≤ 2 * (H : ℝ) * Real.log M := by
    have := Real.log_natCast_nonneg M; positivity
  have h3 := mul_le_mul_of_nonneg_right hlog hc
  nlinarith

/-! ## V71 prime-power contamination -/

/-- Prime-power (non-prime) von Mangoldt mass on `(M/H, M]`. -/
noncomputable def PPW (M H : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc (M / H) M).filter (fun n => ¬ n.Prime), LambdaW n

/-- **Exact V71 contamination**: `0 ≤ D_Λ - D_θ ≤ 4 H (log M) · PPW`. -/
theorem mangoldt_prime_power_error_exact (M H : ℕ) :
    0 ≤ DLambda M H - Dtheta M H ∧
      DLambda M H - Dtheta M H ≤ 4 * H * Real.log M * PPW M H := by
  classical
  have hLL : ∀ x : DTup, 0 ≤ LambdaW x.q * LambdaW x.r :=
    fun x => mul_nonneg (LambdaW_nonneg _) (LambdaW_nonneg _)
  have hdiff : DLambda M H - Dtheta M H =
      ∑ x ∈ detBox M H, (LambdaW x.q * LambdaW x.r - thetaStar x.q * thetaStar x.r) := by
    unfold DLambda Dtheta Dw; rw [Finset.sum_sub_distrib]
  constructor
  · rw [hdiff]
    refine Finset.sum_nonneg fun x _ => ?_
    have := mul_le_mul (thetaStar_le_LambdaW x.q) (thetaStar_le_LambdaW x.r)
      (thetaStar_nonneg _) (LambdaW_nonneg _)
    linarith
  set NP := (Finset.Ioc (M / H) M).filter (fun n => ¬ n.Prime)
  have hle : ∑ x ∈ detBox M H, (LambdaW x.q * LambdaW x.r - thetaStar x.q * thetaStar x.r) ≤
      ∑ x ∈ (detBox M H).filter (fun x => x.q ∈ NP), LambdaW x.q * LambdaW x.r +
      ∑ x ∈ (detBox M H).filter (fun x => x.r ∈ NP), LambdaW x.q * LambdaW x.r := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x hx => ?_
    have m := mem_detBox.1 hx
    have hqI : x.q ∈ Finset.Ioc (M / H) M := Finset.mem_Ioc.2 m.2.1
    have hrI : x.r ∈ Finset.Ioc (M / H) M := Finset.mem_Ioc.2 m.2.2.2.1
    have := hLL x
    have hθθ : 0 ≤ thetaStar x.q * thetaStar x.r :=
      mul_nonneg (thetaStar_nonneg _) (thetaStar_nonneg _)
    by_cases h1 : x.q.Prime <;> by_cases h2 : x.r.Prime
    · have hq1 : x.q ∉ NP := fun h => (Finset.mem_filter.1 h).2 h1
      have hr1 : x.r ∉ NP := fun h => (Finset.mem_filter.1 h).2 h2
      rw [if_neg hq1, if_neg hr1, thetaStar_of_prime h1, thetaStar_of_prime h2]; simp
    · have hr1 : x.r ∈ NP := Finset.mem_filter.2 ⟨hrI, h2⟩
      rw [if_pos hr1, thetaStar_of_not_prime h2]
      split_ifs <;> (simp; try linarith)
    · have hq1 : x.q ∈ NP := Finset.mem_filter.2 ⟨hqI, h1⟩
      rw [if_pos hq1, thetaStar_of_not_prime h1]
      split_ifs <;> (simp; try linarith)
    · have hq1 : x.q ∈ NP := Finset.mem_filter.2 ⟨hqI, h1⟩
      rw [if_pos hq1, thetaStar_of_not_prime h1]
      split_ifs <;> (simp; try linarith)
  have hq := sum_q_mem_le M H NP LambdaW LambdaW LambdaW_nonneg (fun _ => le_rfl)
  have hr := sum_r_mem_le M H NP LambdaW LambdaW LambdaW_nonneg (fun _ => le_rfl)
  rw [hdiff]
  unfold PPW
  nlinarith

/-- `PPW ≤ ψ(M) - θ(M) ≤ 2 √M log M` (Mathlib Chebyshev bound). -/
theorem PPW_le (M H : ℕ) (hM : 1 ≤ M) :
    PPW M H ≤ 2 * Real.sqrt M * Real.log M := by
  have hsub : (Finset.Ioc (M / H) M).filter (fun n => ¬ n.Prime) ⊆
      (Finset.Ioc 0 ⌊(M : ℝ)⌋₊).filter (fun n => ¬ n.Prime) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.floor_natCast] at hn ⊢
    exact ⟨⟨lt_of_le_of_lt (Nat.zero_le _) hn.1.1, hn.1.2⟩, hn.2⟩
  have h1 : PPW M H ≤ Chebyshev.psi M - Chebyshev.theta M := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => LambdaW_nonneg n
  have h2 := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := (M : ℝ)) (by exact_mod_cast hM)
  exact le_trans h1 (le_trans (le_abs_self _) h2)

/-- **V71 prime-power contamination (Lean constant)**: `0 ≤ D_Λ - D_θ ≤ 8 H √M (log M)²`. -/
theorem mangoldt_prime_power_error (M H : ℕ) (hM : 1 ≤ M) :
    0 ≤ DLambda M H - Dtheta M H ∧
      DLambda M H - Dtheta M H ≤ 8 * H * Real.sqrt M * Real.log M ^ 2 := by
  obtain ⟨h0, h1⟩ := mangoldt_prime_power_error_exact M H
  refine ⟨h0, le_trans h1 ?_⟩
  have h2 := PPW_le M H hM
  have hc : 0 ≤ 4 * (H : ℝ) * Real.log M := by
    have := Real.log_natCast_nonneg M; positivity
  have := mul_le_mul_of_nonneg_left h2 hc
  nlinarith

end Erdos287.PostV64V71
