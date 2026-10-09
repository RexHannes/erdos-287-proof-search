import Mathlib
import RequestProject.Erdos287.Early4490BernoulliJet

/-!
# Erdős #287 effectivity — exact finite `q`-DFT and the Bernoulli zero modes (§46)

```
FINITE FOURIER INVERSION            : KERNEL-PROVED (no asymptotic Fourier series)
ZERO MODE  mean(f1) = 0             : KERNEL-PROVED (q > 1)
ZERO MODE  mean(f3) = 0             : KERNEL-PROVED (q > 1)
ZERO MODE  mean(f2) = μ(q)φ(q)/6q²  : KERNEL-PROVED (squarefree q ≥ 1)
COPRIMALITY-MASK FIREWALL           : KERNEL-PROVED (explicit q = 3 witness)
ERDŐS #287                          : OPEN
```

For a fixed positive modulus `q` the coprimality-masked periodic functions are

    f₁,q(r) = 1_{(r,q)=1} ψ(r/q),   f₂,q(r) = 1_{(r,q)=1} B₂(r/q),
    f₃,q(r) = 1_{(r,q)=1} B₃(r/q),

with exact finite Fourier coefficients `c_j(q,h) = (1/q) Σ_{r mod q} f_j,q(r) e_q(−hr)` and the
kernel-proved inversion `f(r) = Σ_h c(q,h) e_q(hr)` (`finite_dft_inversion`), taken with respect
to Mathlib's standard additive character `ZMod.stdAddChar`.  Everything is a finite sum; no
asymptotic Fourier series occurs.

The zero modes are computed exactly.  `f₁` and `f₃` vanish in mean by the reflection
`r ↦ q − r`.  The hypothesis actually needed turned out to be only `q > 1` (the odd squarefree
source moduli are a special case): for `q = 1` the strict endpoint convention gives
`mean(f₁) = −1/2 ≠ 0`, recorded as `f1_zeroMode_needs_q_gt_one`.  The `f₂` zero mode is the
Ramanujan-type evaluation

    (1/q) Σ_{r mod q, (r,q)=1} B₂(r/q) = μ(q) φ(q) / (6 q²)     (q squarefree),

proved from the exact period sum `Σ_{r<m} B₂(r/m) = 1/(6m)`, Möbius inversion over the
coprimality mask, and `Σ_{d ∣ q} μ(d) d = μ(q) φ(q)` for squarefree `q`.

`f2_zeroMode_mask_firewall` shows that the zero-mode subtraction must keep the coprimality
mask: subtracting the same constant *without* the mask leaves a nonzero mean already at
`q = 3`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos287
namespace Effectivity

/-! ## §46.1  The coprimality-masked period functions -/

/-- `f₁,q(r) = 1_{(r,q)=1} ψ(r/q)`. -/
def fMask1 (q r : ℕ) : ℚ := if Nat.gcd r q = 1 then psiSaw ((r : ℚ) / q) else 0

/-- `f₂,q(r) = 1_{(r,q)=1} B₂(r/q)`. -/
def fMask2 (q r : ℕ) : ℚ := if Nat.gcd r q = 1 then bern2 ((r : ℚ) / q) else 0

/-- `f₃,q(r) = 1_{(r,q)=1} B₃(r/q)`. -/
def fMask3 (q r : ℕ) : ℚ := if Nat.gcd r q = 1 then bern3 ((r : ℚ) / q) else 0

/-- The mean (zero mode) of a `q`-periodic rational function. -/
def zeroMode (q : ℕ) (F : ℕ → ℚ) : ℚ := (1 / q) * ∑ r ∈ Finset.range q, F r

/-! ## §46.2  Exact finite Fourier coefficients and inversion -/

/-- A rational `q`-periodic function as a complex function on `ZMod q`. -/
noncomputable def toZModFun (q : ℕ) (F : ℕ → ℚ) : ZMod q → ℂ := fun x => ((F x.val : ℚ) : ℂ)

/-- The exact finite Fourier coefficient `c(q,h) = (1/q) Σ_{r mod q} f(r) e_q(−hr)`. -/
noncomputable def dftCoef (q : ℕ) [NeZero q] (f : ZMod q → ℂ) (h : ZMod q) : ℂ :=
  (q : ℂ)⁻¹ * ZMod.dft f h

/-- **`dftCoef_eq`.**  `KERNEL-PROVED`.  The coefficient is the stated finite sum. -/
theorem dftCoef_eq (q : ℕ) [NeZero q] (f : ZMod q → ℂ) (h : ZMod q) :
    dftCoef q f h = (q : ℂ)⁻¹ * ∑ j : ZMod q, ZMod.stdAddChar (-(j * h)) * f j := by
  rw [dftCoef, ZMod.dft_apply]
  simp

/-- **`finite_dft_inversion`.**  `KERNEL-PROVED`.  Exact finite Fourier inversion:

    f(r) = Σ_{h mod q} c(q,h) e_q(h r). -/
theorem finite_dft_inversion (q : ℕ) [NeZero q] (f : ZMod q → ℂ) (r : ZMod q) :
    f r = ∑ h : ZMod q, dftCoef q f h * ZMod.stdAddChar (h * r) := by
  have h1 : (ZMod.dft.symm (ZMod.dft f)) r = f r := by simp
  rw [← h1, ZMod.invDFT_apply]
  simp only [smul_eq_mul, Finset.mul_sum, dftCoef]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **`sum_zmod_eq_sum_range`.**  `KERNEL-PROVED`.  Summation over `ZMod q` is summation over
the residues `0, …, q−1`. -/
theorem sum_zmod_eq_sum_range (q : ℕ) [NeZero q] (F : ℕ → ℚ) :
    ∑ x : ZMod q, F x.val = ∑ r ∈ Finset.range q, F r := by
  refine Finset.sum_nbij' (i := fun x => ZMod.val x) (j := fun r => ((r : ℕ) : ZMod q))
    ?_ ?_ ?_ ?_ ?_
  · intro x _; simp [Finset.mem_range, ZMod.val_lt]
  · intro r _; simp
  · intro x _; simp [ZMod.natCast_val, ZMod.cast_id]
  · intro r hr; simp only [Finset.mem_range] at hr; exact ZMod.val_cast_of_lt hr
  · intro x _; rfl

/-- **`dftCoef_zero_eq_zeroMode`.**  `KERNEL-PROVED`.  The `h = 0` Fourier coefficient is
exactly the zero mode. -/
theorem dftCoef_zero_eq_zeroMode (q : ℕ) [NeZero q] (F : ℕ → ℚ) :
    dftCoef q (toZModFun q F) 0 = ((zeroMode q F : ℚ) : ℂ) := by
  rw [dftCoef_eq, zeroMode]
  have hchar : ∀ j : ZMod q, ZMod.stdAddChar (-(j * 0)) = 1 := by
    intro j; simp
  simp only [hchar, one_mul, toZModFun]
  have hsum : ∑ x : ZMod q, ((F x.val : ℚ) : ℂ) = ((∑ r ∈ Finset.range q, F r : ℚ) : ℂ) := by
    rw [← sum_zmod_eq_sum_range q F]
    push_cast
    rfl
  rw [hsum]
  push_cast
  ring

/-! ## §46.3  The exact zero modes -/

private theorem sum_range_cast (m : ℕ) : ∑ r ∈ Finset.range m, (r : ℚ) = m * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

private theorem sum_range_sq_cast (m : ℕ) :
    ∑ r ∈ Finset.range m, (r : ℚ) ^ 2 = (m - 1) * m * (2 * m - 1) / 6 := by
  induction m with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- **`sum_range_bern2`.**  `KERNEL-PROVED`.  The exact complete-period Bernoulli sum
`Σ_{r<m} B₂(r/m) = 1/(6m)`. -/
theorem sum_range_bern2 {m : ℕ} (hm : 0 < m) :
    ∑ r ∈ Finset.range m, bern2 ((r : ℚ) / m) = 1 / (6 * m) := by
  have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  simp only [bern2, div_pow, sub_add_eq_add_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [sum_range_cast, sum_range_sq_cast]
  field_simp
  ring

private theorem sum_moebius_divisors_rat (n : ℕ) :
    ∑ d ∈ n.divisors, ((moebius d : ℤ) : ℚ) = if n = 1 then 1 else 0 := by
  have h : ∑ d ∈ n.divisors, (moebius d : ℤ) = if n = 1 then 1 else 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
      ArithmeticFunction.one_apply]
  have := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at this
  exact this

/-- **`sum_multiples_reindex`.**  `KERNEL-PROVED`.  Reindexing the multiples of `d` inside a
complete period. -/
theorem sum_multiples_reindex {q d : ℕ} (hd : d ∣ q) (hd0 : 0 < d) (F : ℕ → ℚ) :
    ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), F r
      = ∑ s ∈ Finset.range (q / d), F (s * d) := by
  refine (Finset.sum_nbij' (i := fun s => s * d) (j := fun r => r / d) ?_ ?_ ?_ ?_ ?_).symm
  · intro s hs
    simp only [Finset.mem_range] at hs
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ⟨s, mul_comm s d⟩⟩
    calc s * d < (q / d) * d := (Nat.mul_lt_mul_right hd0).2 hs
      _ = q := Nat.div_mul_cancel hd
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    simp only [Finset.mem_range]
    exact Nat.div_lt_div_of_lt_of_dvd hd hr.1
  · intro s _; exact Nat.mul_div_cancel s hd0
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    exact Nat.div_mul_cancel hr.2
  · intro s _; rfl

/-- **`coprime_sum_mobius`.**  `KERNEL-PROVED`.  Möbius expansion of the coprimality mask over
a complete period. -/
theorem coprime_sum_mobius {q : ℕ} (hq : 0 < q) (F : ℕ → ℚ) :
    ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), F r
      = ∑ d ∈ q.divisors, ((moebius d : ℤ) : ℚ)
          * ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), F r := by
  have hswap : ∑ d ∈ q.divisors, ((moebius d : ℤ) : ℚ)
        * ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), F r
      = ∑ r ∈ Finset.range q,
          (∑ d ∈ q.divisors.filter (fun d => d ∣ r), ((moebius d : ℤ) : ℚ)) * F r := by
    simp only [Finset.sum_filter, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
    by_cases h : d ∣ a <;> simp [h]
  rw [hswap, Finset.sum_filter]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hfil : q.divisors.filter (fun d => d ∣ r) = (Nat.gcd r q).divisors := by
    ext d
    simp [Nat.mem_divisors, Nat.dvd_gcd_iff, hq.ne', Nat.gcd_eq_zero_iff]
    tauto
  rw [hfil, sum_moebius_divisors_rat]
  split <;> simp_all

/-- **`mobius_id_divisors_squarefree`.**  `KERNEL-PROVED`.  `Σ_{d ∣ q} μ(d) d = μ(q) φ(q)` for
squarefree `q`. -/
theorem mobius_id_divisors_squarefree {q : ℕ} (hq : 0 < q) (hsq : Squarefree q) :
    ∑ d ∈ q.divisors, (moebius d : ℤ) * (d : ℤ) = (moebius q : ℤ) * (Nat.totient q : ℤ) := by
  have hphi : ∑ i ∈ q.divisors, (moebius i : ℤ) * ((q / i : ℕ) : ℤ) = (Nat.totient q : ℤ) := by
    have h := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq (R := ℤ)
        (f := fun d => (Nat.totient d : ℤ)) (g := fun n => (n : ℤ))).1
      (by intro n _; exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) (Nat.sum_totient n)) q hq
    simpa [smul_eq_mul, Nat.sum_divisorsAntidiagonal (f := fun a b => (moebius a : ℤ) * (b : ℤ))]
      using h
  have hre : ∑ i ∈ q.divisors, (moebius i : ℤ) * ((q / i : ℕ) : ℤ)
      = ∑ d ∈ q.divisors, (moebius (q / d) : ℤ) * (d : ℤ) := by
    rw [← Nat.sum_div_divisors q (fun d => (moebius d : ℤ) * ((q / d : ℕ) : ℤ))]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Nat.div_div_self (Nat.mem_divisors.1 hd).1 hq.ne']
  rw [hre] at hphi
  rw [← hphi, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdvd : d ∣ q := (Nat.mem_divisors.1 hd).1
  have hmul : (moebius q : ℤ) * (moebius (q / d) : ℤ) = (moebius d : ℤ) := by
    obtain ⟨e, rfl⟩ := hdvd
    have hcop : Nat.Coprime d e := (Nat.squarefree_mul_iff.1 hsq).1
    have hd0 : 0 < d := Nat.pos_of_ne_zero (fun h => by simp [h] at hq)
    have hde : d * e / d = e := Nat.mul_div_cancel_left e hd0
    have hsqe : (moebius e : ℤ) ^ 2 = 1 :=
      ArithmeticFunction.moebius_sq_eq_one_of_squarefree ((Nat.squarefree_mul_iff.1 hsq).2.2)
    rw [hde, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
    calc (moebius d : ℤ) * (moebius e : ℤ) * (moebius e : ℤ)
        = (moebius d : ℤ) * (moebius e : ℤ) ^ 2 := by ring
      _ = (moebius d : ℤ) := by rw [hsqe, mul_one]
  rw [← hmul]; ring

/-- **`reflect_zero_mode`.**  `KERNEL-PROVED`.  A masked period function built from a function
odd about `1/2` has vanishing coprime sum, by the reflection `r ↦ q − r`. -/
theorem reflect_zero_mode (q : ℕ) (hq : 1 < q) (g : ℚ → ℚ) (hg : ∀ x, g (1 - x) = -g x) :
    ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1),
      (if Nat.gcd r q = 1 then g ((r : ℚ) / q) else 0) = 0 := by
  set S := (Finset.range q).filter (fun r => Nat.gcd r q = 1) with hS
  have hmem : ∀ r ∈ S, 0 < r ∧ r < q ∧ Nat.gcd r q = 1 := by
    intro r hr
    simp only [hS, Finset.mem_filter, Finset.mem_range] at hr
    refine ⟨?_, hr.1, hr.2⟩
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; simp at hr; omega
    · exact h
  have hbij : ∑ r ∈ S, (if Nat.gcd r q = 1 then g ((r : ℚ) / q) else 0)
      = ∑ r ∈ S, (if Nat.gcd (q - r) q = 1 then g (((q - r : ℕ) : ℚ) / q) else 0) := by
    refine (Finset.sum_nbij' (i := fun r => q - r) (j := fun r => q - r) ?_ ?_ ?_ ?_ ?_).symm
    · intro r hr
      obtain ⟨h0, hlt, hcop⟩ := hmem r hr
      simp only [hS, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by rw [Nat.gcd_self_sub_left hlt.le]; exact hcop⟩
    · intro r hr
      obtain ⟨h0, hlt, hcop⟩ := hmem r hr
      simp only [hS, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by rw [Nat.gcd_self_sub_left hlt.le]; exact hcop⟩
    · intro r hr; obtain ⟨h0, hlt, -⟩ := hmem r hr; show q - (q - r) = r; omega
    · intro r hr; obtain ⟨h0, hlt, -⟩ := hmem r hr; show q - (q - r) = r; omega
    · intro r _; rfl
  have hval : ∀ r ∈ S, (if Nat.gcd (q - r) q = 1 then g (((q - r : ℕ) : ℚ) / q) else 0)
      = -(if Nat.gcd r q = 1 then g ((r : ℚ) / q) else 0) := by
    intro r hr
    obtain ⟨h0, hlt, hcop⟩ := hmem r hr
    have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hcop' : Nat.gcd (q - r) q = 1 := by rw [Nat.gcd_self_sub_left hlt.le]; exact hcop
    rw [if_pos hcop', if_pos hcop]
    have hcast : ((q - r : ℕ) : ℚ) = (q : ℚ) - r := by push_cast [Nat.cast_sub hlt.le]; ring
    rw [hcast, show ((q : ℚ) - r) / q = 1 - (r : ℚ) / q by field_simp, hg]
  rw [Finset.sum_congr rfl hval, Finset.sum_neg_distrib] at hbij
  linarith [hbij]

/-- **`f1_zero_mode`.**  `KERNEL-PROVED`.  `mean(f₁,q) = 0` for `q > 1` (in particular for the
odd squarefree source moduli). -/
theorem f1_zero_mode {q : ℕ} (hq : 1 < q) : zeroMode q (fMask1 q) = 0 := by
  rw [zeroMode, ← Finset.sum_filter_add_sum_filter_not (Finset.range q)
      (fun r => Nat.gcd r q = 1) (fMask1 q)]
  have h2 : ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.gcd r q = 1), fMask1 q r = 0 :=
    Finset.sum_eq_zero fun r hr => by
      simp only [Finset.mem_filter] at hr
      simp [fMask1, hr.2]
  have h1 : ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), fMask1 q r = 0 :=
    reflect_zero_mode q hq psiSaw psiSaw_reflect
  rw [h1, h2]
  ring

/-- **`f3_zero_mode`.**  `KERNEL-PROVED`.  `mean(f₃,q) = 0` for `q > 1` (in particular for the
odd squarefree source moduli). -/
theorem f3_zero_mode {q : ℕ} (hq : 1 < q) : zeroMode q (fMask3 q) = 0 := by
  rw [zeroMode, ← Finset.sum_filter_add_sum_filter_not (Finset.range q)
      (fun r => Nat.gcd r q = 1) (fMask3 q)]
  have h2 : ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.gcd r q = 1), fMask3 q r = 0 :=
    Finset.sum_eq_zero fun r hr => by
      simp only [Finset.mem_filter] at hr
      simp [fMask3, hr.2]
  have h1 : ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), fMask3 q r = 0 :=
    reflect_zero_mode q hq bern3 bern3_reflect
  rw [h1, h2]
  ring

/-- **`f1_zeroMode_needs_q_gt_one`.**  `KERNEL-PROVED`.  The hypothesis `q > 1` is necessary:
with the repository's strict endpoint convention `mean(f₁,₁) = −1/2 ≠ 0`. -/
theorem f1_zeroMode_needs_q_gt_one : zeroMode 1 (fMask1 1) = -1 / 2 := by
  norm_num [zeroMode, fMask1, psiSaw]

/-- **`f2_zero_mode`.**  `KERNEL-PROVED`.  The exact `f₂` zero mode for squarefree `q`:

    mean(f₂,q) = μ(q) φ(q) / (6 q²). -/
theorem f2_zero_mode {q : ℕ} (hq : 0 < q) (hsq : Squarefree q) :
    zeroMode q (fMask2 q)
      = ((moebius q : ℤ) : ℚ) * (Nat.totient q : ℚ) / (6 * (q : ℚ) ^ 2) := by
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  -- restrict to the coprime residues
  have hsplit : ∑ r ∈ Finset.range q, fMask2 q r
      = ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), bern2 ((r : ℚ) / q) := by
    rw [Finset.sum_filter]
    rfl
  -- Möbius expansion and the exact period sums
  have hmob := coprime_sum_mobius hq (fun r => bern2 ((r : ℚ) / q))
  have hinner : ∀ d ∈ q.divisors,
      ((moebius d : ℤ) : ℚ) * ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r),
          bern2 ((r : ℚ) / q)
        = ((moebius d : ℤ) : ℚ) * (d : ℚ) / (6 * q) := by
    intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.1 hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd hq
    have hd0' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hd0.ne'
    have hqd : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdvd) hd0
    have hcast : ((q / d : ℕ) : ℚ) = (q : ℚ) / d := by
      rw [Nat.cast_div hdvd hd0']
    rw [sum_multiples_reindex hdvd hd0 (fun r => bern2 ((r : ℚ) / q))]
    have hterm : ∀ s ∈ Finset.range (q / d),
        bern2 (((s * d : ℕ) : ℚ) / q) = bern2 ((s : ℚ) / ((q / d : ℕ) : ℚ)) := by
      intro s _
      congr 1
      rw [hcast]
      push_cast
      field_simp
    rw [Finset.sum_congr rfl hterm, sum_range_bern2 hqd, hcast]
    field_simp
  rw [zeroMode, hsplit, hmob, Finset.sum_congr rfl hinner]
  -- resum the divisor sum
  have hfac : ∑ d ∈ q.divisors, ((moebius d : ℤ) : ℚ) * (d : ℚ) / (6 * q)
      = (∑ d ∈ q.divisors, ((moebius d : ℤ) : ℚ) * (d : ℚ)) / (6 * q) := by
    rw [Finset.sum_div]
  rw [hfac]
  have hsum : ∑ d ∈ q.divisors, ((moebius d : ℤ) : ℚ) * (d : ℚ)
      = ((moebius q : ℤ) : ℚ) * (Nat.totient q : ℚ) := by
    have := congrArg (fun z : ℤ => (z : ℚ)) (mobius_id_divisors_squarefree hq hsq)
    push_cast at this
    exact this
  rw [hsum]
  field_simp

/-! ## §46.4  The coprimality-mask firewall -/

/-- The zero-mode-corrected function, **with** the coprimality mask retained. -/
def maskedCorrection (q : ℕ) (F : ℕ → ℚ) (K : ℚ) (r : ℕ) : ℚ :=
  if Nat.gcd r q = 1 then F r - K else 0

/-- The **illegal** correction: the same constant subtracted without the mask. -/
def unmaskedCorrection (F : ℕ → ℚ) (K : ℚ) (r : ℕ) : ℚ := F r - K

/-- **`maskedCorrection_zero_mean`.**  `KERNEL-PROVED`.  Subtracting the correct constant
`K = (Σ_{(r,q)=1} F)/φ(q)` **with** the mask kills the mean. -/
theorem maskedCorrection_zero_mean {q : ℕ} (hq : 0 < q) (F : ℕ → ℚ) :
    ∑ r ∈ Finset.range q,
        maskedCorrection q F
          ((∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), F r)
            / ((Finset.range q).filter (fun r => Nat.gcd r q = 1)).card) r = 0 := by
  set S := (Finset.range q).filter (fun r => Nat.gcd r q = 1) with hS
  set K := (∑ r ∈ S, F r) / (S.card : ℚ) with hK
  have hmem1 : ∃ r, r ∈ S := by
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 hq.ne') with h1 | h1
    · refine ⟨0, ?_⟩
      simp only [hS, Finset.mem_filter, Finset.mem_range]
      exact ⟨hq, by rw [← h1]; rfl⟩
    · refine ⟨1, ?_⟩
      simp only [hS, Finset.mem_filter, Finset.mem_range]
      exact ⟨h1, Nat.gcd_one_left q⟩
  obtain ⟨r0, hr0⟩ := hmem1
  have hcard : (S.card : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hr0)
  have hzero : ∑ r ∈ Finset.range q, maskedCorrection q F K r = ∑ r ∈ S, (F r - K) := by
    rw [hS, Finset.sum_filter]
    rfl
  rw [hzero, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hK]
  field_simp
  ring

/-- **`f2_zeroMode_mask_firewall`.**  `KERNEL-PROVED`.  The zero-mode subtraction must preserve
the coprimality mask.  Explicit witness at `q = 3`: with the correct constant `K = −1/18` the
masked correction has mean `0`, while subtracting the same constant *without* the mask leaves
mean `1/54 ≠ 0`. -/
theorem f2_zeroMode_mask_firewall :
    (∑ r ∈ Finset.range 3, maskedCorrection 3 (fMask2 3) (-1 / 18) r) = 0 ∧
      zeroMode 3 (unmaskedCorrection (fMask2 3) (-1 / 18)) = 1 / 54 ∧
      zeroMode 3 (unmaskedCorrection (fMask2 3) (-1 / 18)) ≠ 0 := by
  have h0 : fMask2 3 0 = 0 := by unfold fMask2; norm_num
  have h1 : fMask2 3 1 = -1 / 18 := by unfold fMask2 bern2; norm_num
  have h2 : fMask2 3 2 = -1 / 18 := by unfold fMask2 bern2; norm_num
  have hg0 : Nat.gcd 0 3 ≠ 1 := by decide
  have hg1 : Nat.gcd 1 3 = 1 := by decide
  have hg2 : Nat.gcd 2 3 = 1 := by decide
  have hmask : (∑ r ∈ Finset.range 3, maskedCorrection 3 (fMask2 3) (-1 / 18) r) = 0 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp only [maskedCorrection, if_neg hg0, if_pos hg1, if_pos hg2, h1, h2]
    norm_num
  have hun : zeroMode 3 (unmaskedCorrection (fMask2 3) (-1 / 18)) = 1 / 54 := by
    unfold zeroMode
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp only [unmaskedCorrection, h0, h1, h2]
    norm_num
  exact ⟨hmask, hun, by rw [hun]; norm_num⟩

end Effectivity
end Erdos287
