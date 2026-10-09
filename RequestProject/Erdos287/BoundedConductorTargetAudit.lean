import Mathlib
import RequestProject.Erdos287.FixedConductorCharacterRepair
import RequestProject.Erdos287.SmallEllMeanCovariance

/-!
# Erdős #287 effectivity — audit of the bounded-conductor `k = 1` target (§62)

```
LONG-WINDOW PERIOD LAW                       : KERNEL-PROVED
returnedKernel 0 (P·n) 1 = n·P·meanSum       : KERNEL-PROVED
meanSum ≠ 0  (4999-adic valuation)           : KERNEL-PROVED
BoundedConductorK1Target AS STATED           : KERNEL-REFUTED
```

`BoundedConductorFrontier` states the `k = 1` frontier target as

    BoundedConductorK1Target b : ∀ A B z, |returnedKernel A B z| ≤ b,

i.e. a *uniform* bound on the returned finite-conductor kernel over **all** half-open
windows `[A,B)`.  This module audits that statement.

The returned kernel is a window sum of the `ℓ`-periodic local kernels
`K_ℓ (1000 < ℓ ≤ 5000)`, so on a window whose length is a common multiple `P` of all those
periods it is exactly `P · meanSum`, where

    meanSum = ∑_{1000 < ℓ ≤ 5000} meanK ℓ = − ∑_{1000 < ℓ ≤ 5000} μ(ℓ)β(ℓ)/ℓ

is the aggregate complete-period mean already banked in `SmallEllMeanCovariance`.  Taking
`n` consecutive periods multiplies this by `n`, so the target is bounded **iff** the
aggregate mean vanishes.  It does not: the conductor `ℓ = 4999` is prime, contributes
`1/(4999·4997)`, and no other term of the sum has `4999` in its denominator, so the
`4999`-adic valuation of `meanSum` is exactly `−1`.

Consequently `BoundedConductorK1Target b` is **false for every budget `b`**, and — via
`characterMeanBound_iff_boundedConductorTarget` — so is the repaired normalised character
interface.  The bounded-conductor frontier therefore has to be restated over the *physical*
hyperbola windows (a bounded family of windows), not over all half-open windows: an
unrestricted window family carries the nonzero density term `P·meanSum`, which is exactly
the density (`D_X`) owner that `DensityCompensationRestoration.DX_term_not_removable`
already shows cannot be dropped.

Nothing here closes any owner: this is a *negative* audit result about the current
formalisation of the frontier target.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §62.1  Generic periodic window algebra -/

/-- Shift-invariance by a multiple of the period. -/
lemma periodic_shift_nat {f : ℤ → ℚ} {m : ℕ} (hper : ∀ s, f (s + m) = f s) :
    ∀ (k : ℕ) (s : ℤ), f (s + (m : ℤ) * (k : ℤ)) = f s := by
  intro k
  induction k with
  | zero => intro s; simp
  | succ n ih =>
      intro s
      have h1 : s + (m : ℤ) * ((n : ℤ) + 1) = (s + (m : ℤ) * (n : ℤ)) + (m : ℤ) := by ring
      push_cast
      rw [h1, hper, ih]

/-- A sum over `[0, m·n)` of an `m`-periodic function is `n` copies of the period sum. -/
lemma sum_Ico_period_multiple {f : ℤ → ℚ} {m : ℕ} (hper : ∀ s, f (s + m) = f s) (n : ℕ) :
    ∑ s ∈ Finset.Ico (0 : ℤ) ((m : ℤ) * (n : ℤ)), f s
      = (n : ℚ) * ∑ s ∈ Finset.Ico (0 : ℤ) (m : ℤ), f s := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hsplit : Finset.Ico (0 : ℤ) ((m : ℤ) * ((n : ℤ) + 1))
          = Finset.Ico (0 : ℤ) ((m : ℤ) * (n : ℤ)) ∪
              Finset.Ico ((m : ℤ) * (n : ℤ)) ((m : ℤ) * ((n : ℤ) + 1)) := by
        rw [Finset.Ico_union_Ico_eq_Ico] <;> nlinarith [Int.natCast_nonneg m, Int.natCast_nonneg n]
      have hdisj : Disjoint (Finset.Ico (0 : ℤ) ((m : ℤ) * (n : ℤ)))
          (Finset.Ico ((m : ℤ) * (n : ℤ)) ((m : ℤ) * ((n : ℤ) + 1))) :=
        Finset.Ico_disjoint_Ico_consecutive _ _ _
      have htail : ∑ s ∈ Finset.Ico ((m : ℤ) * (n : ℤ)) ((m : ℤ) * ((n : ℤ) + 1)), f s
          = ∑ s ∈ Finset.Ico (0 : ℤ) (m : ℤ), f s := by
        have hmap : Finset.Ico ((m : ℤ) * (n : ℤ)) ((m : ℤ) * ((n : ℤ) + 1))
            = (Finset.Ico (0 : ℤ) (m : ℤ)).map
                (addLeftEmbedding ((m : ℤ) * (n : ℤ))) := by
          rw [Finset.map_add_left_Ico]
          congr 1
        rw [hmap, Finset.sum_map]
        refine Finset.sum_congr rfl fun s _ => ?_
        have : (addLeftEmbedding ((m : ℤ) * (n : ℤ))) s = s + (m : ℤ) * (n : ℤ) := by
          simp [addLeftEmbedding, add_comm]
        rw [this, periodic_shift_nat hper n s]
      push_cast
      rw [hsplit, Finset.sum_union hdisj, htail, ih]
      ring

/-- The `ℤ`-window `[0, n)` sum equals the `range n` sum. -/
lemma sum_Ico_eq_sum_range (f : ℤ → ℚ) (n : ℕ) :
    ∑ s ∈ Finset.Ico (0 : ℤ) (n : ℤ), f s = ∑ i ∈ Finset.range n, f (i : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
      have hins : Finset.Ico (0 : ℤ) ((n : ℤ) + 1) = insert (n : ℤ) (Finset.Ico (0 : ℤ) (n : ℤ)) := by
        ext s
        simp only [Finset.mem_Ico, Finset.mem_insert]
        omega
      have hnot : (n : ℤ) ∉ Finset.Ico (0 : ℤ) (n : ℤ) := by simp
      rw [h1, hins, Finset.sum_insert hnot, ih, Finset.sum_range_succ]
      ring

/-! ## §62.2  The aggregate complete-period mean -/

/-- The conductor range of the returned finite-conductor kernel. -/
def conductorRange : Finset ℕ := Finset.Icc 1001 5000

/-- The complete-period mean of the local kernel `K_ℓ` at the outer point `z = 1`. -/
def meanTerm (ell : ℕ) : ℚ :=
  - ((ArithmeticFunction.moebius ell : ℤ) : ℚ) * beta ell / (ell : ℚ)

/-- The aggregate complete-period mean of the returned finite-conductor kernel. -/
def meanSum : ℚ := ∑ ell ∈ conductorRange, meanTerm ell

/-- Non-squarefree conductors contribute nothing: `μ(ℓ) = 0` kills the whole local kernel. -/
lemma Kell_eq_zero_of_not_squarefree {ell : ℕ} (h : ¬ Squarefree ell) (s z : ℤ) :
    Kell ell s z = 0 := by
  have hmu : ((ArithmeticFunction.moebius ell : ℤ) : ℚ) = 0 := by
    have := (ArithmeticFunction.moebius_eq_zero_of_not_squarefree h)
    exact_mod_cast congrArg (fun x : ℤ => (x : ℚ)) this
  have hc : cEll ell = 0 := by rw [cEll, hmu]; simp
  rw [Kell, hc]; ring

/-- **`meanK_eq_meanTerm`.**  `KERNEL-PROVED`.  For every conductor `ℓ > 1` the complete-period
mean at `z = 1` is `−μ(ℓ)β(ℓ)/ℓ` (both sides vanish when `ℓ` is not squarefree). -/
theorem meanK_eq_meanTerm {ell : ℕ} (hell : 1 < ell) : meanK ell 1 = meanTerm ell := by
  by_cases hsq : Squarefree ell
  · have hz : ∀ p ∈ ell.primeFactors, ¬ p ∣ 1 := by
      intro p hp hdvd
      have := (Nat.prime_of_mem_primeFactors hp).one_lt
      have := Nat.le_of_dvd one_pos hdvd
      omega
    rw [smallEll_local_mean hsq hell hz, meanTerm]
  · have hzero : periodSum ell 1 = 0 :=
      Finset.sum_eq_zero fun s _ => Kell_eq_zero_of_not_squarefree hsq _ _
    have hmu : ((ArithmeticFunction.moebius ell : ℤ) : ℚ) = 0 := by
      have := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
      exact_mod_cast congrArg (fun x : ℤ => (x : ℚ)) this
    rw [meanK, hzero, meanTerm, hmu]
    simp

/-- **`periodSum_eq_mul_meanTerm`.**  `KERNEL-PROVED`. -/
theorem periodSum_eq_mul_meanTerm {ell : ℕ} (hell : 1 < ell) :
    periodSum ell 1 = (ell : ℚ) * meanTerm ell := by
  have h := meanK_eq_meanTerm hell
  rw [meanK] at h
  have hne : (ell : ℚ) ≠ 0 := by positivity
  field_simp at h
  linarith [h]

/-! ## §62.3  The long-window period law -/

/-- The common period used for the returned kernel: every conductor `ℓ ≤ 5000` divides it. -/
def bigPeriod : ℕ := Nat.factorial 5000

lemma conductor_dvd_bigPeriod {ell : ℕ} (h1 : 1 ≤ ell) (h2 : ell ≤ 5000) : ell ∣ bigPeriod :=
  Nat.dvd_factorial h1 h2

lemma bigPeriod_pos : 0 < bigPeriod := Nat.factorial_pos 5000

/-- **`Kell_long_window`.**  `KERNEL-PROVED`.  The window sum of `K_ℓ` over `n` full periods
`[0, P·n)` is `P·n·meanTerm ℓ`. -/
theorem Kell_long_window {ell : ℕ} (h1 : 1001 ≤ ell) (h2 : ell ≤ 5000) (n : ℕ) :
    ∑ s ∈ Finset.Ico (0 : ℤ) ((bigPeriod : ℤ) * (n : ℤ)), Kell ell s 1
      = (bigPeriod : ℚ) * (n : ℚ) * meanTerm ell := by
  obtain ⟨c, hc⟩ := conductor_dvd_bigPeriod (by omega) h2
  have hper : ∀ s : ℤ, Kell ell (s + ell) 1 = Kell ell s 1 := fun s => Kell_periodic ell s 1
  have hrw : (bigPeriod : ℤ) * (n : ℤ) = (ell : ℤ) * ((c * n : ℕ) : ℤ) := by
    rw [hc]; push_cast; ring
  rw [hrw, sum_Ico_period_multiple hper (c * n), sum_Ico_eq_sum_range]
  have hps : ∑ i ∈ Finset.range ell, Kell ell (i : ℤ) 1 = periodSum ell 1 := by
    rw [periodSum]; norm_num
  rw [hps, periodSum_eq_mul_meanTerm (by omega)]
  rw [hc]; push_cast; ring

/-- **`returnedKernel_long_window`.**  `KERNEL-PROVED`.  Over `n` full periods the returned
finite-conductor kernel is exactly `P·n·meanSum`. -/
theorem returnedKernel_long_window (n : ℕ) :
    returnedKernel 0 ((bigPeriod : ℤ) * (n : ℤ)) 1
      = (bigPeriod : ℚ) * (n : ℚ) * meanSum := by
  have hstep : ∀ ell ∈ conductorRange,
      Qell ell 0 ((bigPeriod : ℤ) * (n : ℤ)) 1 = (bigPeriod : ℚ) * (n : ℚ) * meanTerm ell := by
    intro ell hell
    rw [conductorRange, Finset.mem_Icc] at hell
    rw [← Qell_compiler (by omega : 0 < ell)]
    exact Kell_long_window hell.1 hell.2 n
  rw [returnedKernel, show Finset.Icc 1001 5000 = conductorRange from rfl,
    Finset.sum_congr rfl hstep, meanSum, Finset.mul_sum]

/-! ## §62.4  The aggregate mean does not vanish -/

/-- The natural-number denominator of the term at a squarefree odd conductor. -/
def meanDen (ell : ℕ) : ℕ := ell * ∏ p ∈ ell.primeFactors, (p - 2)

lemma prod_sub_two_cast (ell : ℕ) :
    ((∏ p ∈ ell.primeFactors, (p - 2) : ℕ) : ℚ) = ∏ p ∈ ell.primeFactors, ((p : ℚ) - 2) := by
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  rw [Nat.cast_sub hp2]
  norm_num

/-- Away from squarefree odd conductors the term vanishes. -/
lemma meanTerm_eq_zero {ell : ℕ} (h : ¬ (Squarefree ell ∧ ¬ 2 ∣ ell)) : meanTerm ell = 0 := by
  rw [meanTerm, beta, if_neg h]
  simp

/-- At a squarefree odd conductor the term is `−μ(ℓ)` over the natural denominator
`ℓ·∏_{p∣ℓ}(p−2)`. -/
lemma meanTerm_eq_div {ell : ℕ} (hsq : Squarefree ell) (hodd : ¬ 2 ∣ ell) :
    meanTerm ell = ((- (ArithmeticFunction.moebius ell) : ℤ) : ℚ) / ((meanDen ell : ℕ) : ℚ) := by
  rw [meanTerm, beta, if_pos ⟨hsq, hodd⟩, meanDen, Nat.cast_mul, prod_sub_two_cast]
  push_cast
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv, one_mul]
  ring

lemma meanDen_ne_zero {ell : ℕ} (hell : 0 < ell) (hodd : ¬ 2 ∣ ell) : meanDen ell ≠ 0 := by
  rw [meanDen]
  refine Nat.mul_ne_zero hell.ne' (Finset.prod_ne_zero_iff.2 fun p hp => ?_)
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ ell := Nat.dvd_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := fun h => hodd (h ▸ hpd)
  have := hpp.two_le
  omega

/-- The prime `4999` does not divide the denominator of any other term in range. -/
lemma not_dvd_meanDen {ell : ℕ} (h1 : 1001 ≤ ell) (h2 : ell ≤ 5000) (hne : ell ≠ 4999)
    (hodd : ¬ 2 ∣ ell) : ¬ (4999 ∣ meanDen ell) := by
  have hp : Nat.Prime 4999 := by norm_num
  intro hdvd
  rw [meanDen] at hdvd
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with hell | hprod
  · obtain ⟨k, hk⟩ := hell
    clear hdvd hodd hp
    omega
  · obtain ⟨q, hq, hqd⟩ := Prime.exists_mem_finset_dvd hp.prime hprod
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqe : q ∣ ell := Nat.dvd_of_mem_primeFactors hq
    have hq2 : q ≠ 2 := fun h => hodd (h ▸ hqe)
    have hq3 : 3 ≤ q := by have := hqp.two_le; omega
    have hqle : q ≤ ell := Nat.le_of_dvd (by omega) hqe
    have hle2 := Nat.le_of_dvd (by omega) hqd
    clear hdvd hprod hqd hqe hq2 hqp hq hp hodd
    omega

lemma meanDen_4999 : meanDen 4999 = 4999 * 4997 := by
  have hp : Nat.Prime 4999 := by norm_num
  rw [meanDen, hp.primeFactors, Finset.prod_singleton]

/-- **`padicNorm_meanTerm_le_one`.**  `KERNEL-PROVED`.  Every conductor other than `4999`
contributes a `4999`-adic integer. -/
lemma padicNorm_meanTerm_le_one {ell : ℕ} (h1 : 1001 ≤ ell) (h2 : ell ≤ 5000)
    (hne : ell ≠ 4999) : padicNorm 4999 (meanTerm ell) ≤ 1 := by
  haveI : Fact (Nat.Prime 4999) := ⟨by norm_num⟩
  by_cases hgood : Squarefree ell ∧ ¬ 2 ∣ ell
  · obtain ⟨hsq, hodd⟩ := hgood
    have hden : ¬ ((4999 : ℤ) ∣ ((meanDen ell : ℕ) : ℤ)) := by
      intro h
      exact not_dvd_meanDen h1 h2 hne hodd (by exact_mod_cast h)
    have hnorm_den : padicNorm 4999 (((meanDen ell : ℕ) : ℤ) : ℚ) = 1 :=
      (padicNorm.int_eq_one_iff _).2 hden
    rw [meanTerm_eq_div hsq hodd, padicNorm.div]
    have hnum : padicNorm 4999 (((- (ArithmeticFunction.moebius ell) : ℤ)) : ℚ) ≤ 1 :=
      padicNorm.of_int _
    have hcast : (((meanDen ell : ℕ) : ℤ) : ℚ) = ((meanDen ell : ℕ) : ℚ) := by push_cast; ring
    rw [hcast] at hnorm_den
    rw [hnorm_den, div_one]
    exact hnum
  · rw [meanTerm_eq_zero hgood, padicNorm.zero]
    norm_num

/-- **`padicNorm_meanTerm_4999`.**  `KERNEL-PROVED`.  The conductor `4999` contributes a term
of `4999`-adic norm strictly larger than `1` (valuation `−1`). -/
lemma padicNorm_meanTerm_4999 : 1 < padicNorm 4999 (meanTerm 4999) := by
  haveI : Fact (Nat.Prime 4999) := ⟨by norm_num⟩
  have hp : Nat.Prime 4999 := by norm_num
  have hsq : Squarefree (4999 : ℕ) := hp.squarefree
  have hodd : ¬ (2 ∣ (4999 : ℕ)) := by norm_num
  have hmu : ArithmeticFunction.moebius 4999 = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime hp]
  have hnum : ((- (ArithmeticFunction.moebius 4999) : ℤ) : ℚ) = 1 := by
    rw [hmu]; norm_num
  have hDpos : (0 : ℚ) < ((meanDen 4999 : ℕ) : ℚ) := by
    rw [meanDen_4999]; norm_num
  have hDdvd : ((4999 : ℤ)) ∣ (((meanDen 4999 : ℕ)) : ℤ) := by
    rw [meanDen_4999]; norm_num
  have hlt : padicNorm 4999 ((((meanDen 4999 : ℕ)) : ℤ) : ℚ) < 1 :=
    (padicNorm.int_lt_one_iff _).2 hDdvd
  have hne0 : padicNorm 4999 ((((meanDen 4999 : ℕ)) : ℤ) : ℚ) ≠ 0 := by
    refine padicNorm.nonzero ?_
    push_cast
    exact hDpos.ne'
  have hpos : 0 < padicNorm 4999 ((((meanDen 4999 : ℕ)) : ℤ) : ℚ) :=
    lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm hne0)
  rw [meanTerm_eq_div hsq hodd, padicNorm.div, hnum, padicNorm.one]
  have hcast : (((meanDen 4999 : ℕ) : ℤ) : ℚ) = ((meanDen 4999 : ℕ) : ℚ) := by push_cast; ring
  rw [hcast] at hlt hpos
  rw [one_lt_div hpos]
  exact hlt

/-- **`meanSum_ne_zero`.**  `KERNEL-PROVED`.  The aggregate complete-period mean of the
returned finite-conductor kernel is nonzero: its `4999`-adic valuation is `−1`, because the
prime conductor `ℓ = 4999` contributes `1/(4999·4997)` and no other conductor in the range
carries `4999` in its denominator. -/
theorem meanSum_ne_zero : meanSum ≠ 0 := by
  haveI : Fact (Nat.Prime 4999) := ⟨by norm_num⟩
  intro hzero
  have hmem : (4999 : ℕ) ∈ conductorRange := by
    rw [conductorRange, Finset.mem_Icc]; omega
  have hsplit : meanTerm 4999 + ∑ ell ∈ conductorRange.erase 4999, meanTerm ell = meanSum :=
    Finset.add_sum_erase _ _ hmem
  have hrest : padicNorm 4999 (∑ ell ∈ conductorRange.erase 4999, meanTerm ell) ≤ 1 := by
    refine padicNorm.sum_le' (fun ell hell => ?_) (by norm_num)
    have hne : ell ≠ 4999 := Finset.ne_of_mem_erase hell
    have hmem' := Finset.mem_of_mem_erase hell
    rw [conductorRange, Finset.mem_Icc] at hmem'
    exact padicNorm_meanTerm_le_one hmem'.1 hmem'.2 hne
  have heq : meanTerm 4999 = -(∑ ell ∈ conductorRange.erase 4999, meanTerm ell) := by
    rw [hzero] at hsplit; linarith
  have hbig := padicNorm_meanTerm_4999
  rw [heq, padicNorm.neg] at hbig
  linarith

/-! ## §62.5  The frontier target as stated is false -/

/-- **`boundedConductorK1Target_unsatisfiable`.**  `KERNEL-PROVED`.  The `k = 1` frontier
target, as currently formalised (a uniform bound over *all* half-open windows), is false for
every budget `b`. -/
theorem boundedConductorK1Target_unsatisfiable (b : ℚ) : ¬ BoundedConductorK1Target b := by
  intro h
  have hP : (0 : ℚ) < (bigPeriod : ℚ) := Nat.cast_pos.2 bigPeriod_pos
  have hm : 0 < |meanSum| := abs_pos.2 meanSum_ne_zero
  obtain ⟨n, hn⟩ := exists_nat_gt (b / ((bigPeriod : ℚ) * |meanSum|))
  have hpos : 0 < (bigPeriod : ℚ) * |meanSum| := mul_pos hP hm
  have hbig : b < (n : ℚ) * ((bigPeriod : ℚ) * |meanSum|) := by
    rw [div_lt_iff₀ hpos] at hn; linarith
  have hle := h 0 ((bigPeriod : ℤ) * (n : ℤ)) 1
  have habs : |(bigPeriod : ℚ) * (n : ℚ) * meanSum|
      = (n : ℚ) * ((bigPeriod : ℚ) * |meanSum|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hP.le, abs_of_nonneg (Nat.cast_nonneg (α := ℚ) n)]
    ring
  rw [returnedKernel_long_window n, habs] at hle
  linarith

/-- **`characterMeanBound_unsatisfiable`.**  `KERNEL-PROVED`.  Hence even the *normalised*
character interface of §61 is unsatisfiable, since it is equivalent to the target. -/
theorem characterMeanBound_unsatisfiable (b : ℚ) : ¬ FixedConductorCharacterMeanBound b :=
  fun h => boundedConductorK1Target_unsatisfiable b
    ((characterMeanBound_iff_boundedConductorTarget b).1 h)

/-! ## §62.6  The density-centred replacement target -/

/-- The complete-period sum of `K_ℓ` at an arbitrary outer point `z`. -/
def perSum (ell : ℕ) (z : ℤ) : ℚ := ∑ s ∈ Finset.range ell, Kell ell (s : ℤ) z

/-- The complete-period mean of `K_ℓ` at an arbitrary outer point `z`. -/
def perMean (ell : ℕ) (z : ℤ) : ℚ := perSum ell z / (ell : ℚ)

/-- The aggregate complete-period mean of the returned kernel at the outer point `z`. -/
def meanSumAt (z : ℤ) : ℚ := ∑ ell ∈ conductorRange, perMean ell z

lemma perSum_one (ell : ℕ) : perSum ell 1 = periodSum ell 1 := by
  rw [perSum, periodSum]
  norm_num

lemma perMean_one (ell : ℕ) : perMean ell 1 = meanK ell 1 := by
  rw [perMean, meanK, perSum_one]

/-- **`meanSumAt_one`.**  `KERNEL-PROVED`.  At `z = 1` the aggregate mean is `meanSum`. -/
theorem meanSumAt_one : meanSumAt 1 = meanSum := by
  rw [meanSumAt, meanSum]
  refine Finset.sum_congr rfl fun ell hell => ?_
  rw [conductorRange, Finset.mem_Icc] at hell
  rw [perMean_one, meanK_eq_meanTerm (by omega)]

/-- **Repaired frontier target.**  The bounded-conductor `k = 1` target with the exact
density term `(B − A)·meanSumAt z` subtracted, on ordered windows.  This is the statement
that survives the audit of §62.5: the unnormalised target fails only through the density
(`D_X`) owner, which `DensityCompensationRestoration.DX_term_not_removable` already
identifies as non-removable. -/
def CentredBoundedConductorK1Target (b : ℚ) : Prop :=
  ∀ A B z : ℤ, A ≤ B → |returnedKernel A B z - ((B - A : ℤ) : ℚ) * meanSumAt z| ≤ b

/-- **`returnedKernel_of_empty_window`.**  `KERNEL-PROVED`.  On a degenerate window the
returned kernel vanishes. -/
theorem returnedKernel_of_empty_window {A B : ℤ} (h : B ≤ A) (z : ℤ) :
    returnedKernel A B z = 0 := by
  refine Finset.sum_eq_zero fun ell hell => ?_
  rw [Finset.mem_Icc] at hell
  rw [← Qell_compiler (by omega : 0 < ell)]
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [Finset.mem_Ico] at hs
  omega

/-- **`centred_target_needs_ordered_windows`.**  `KERNEL-PROVED`.  The restriction `A ≤ B` in
the centred target is *necessary*: on degenerate windows the kernel is `0` while the density
term is unbounded, so the unrestricted centred statement is false for every budget. -/
theorem centred_target_needs_ordered_windows (b : ℚ) :
    ¬ (∀ A B z : ℤ, |returnedKernel A B z - ((B - A : ℤ) : ℚ) * meanSumAt z| ≤ b) := by
  intro h
  have hm : 0 < |meanSum| := abs_pos.2 meanSum_ne_zero
  obtain ⟨n, hn⟩ := exists_nat_gt (b / |meanSum|)
  have hbig : b < (n : ℚ) * |meanSum| := by
    rw [div_lt_iff₀ hm] at hn; linarith
  have hle := h 0 (-(n : ℤ)) 1
  rw [returnedKernel_of_empty_window (by omega : -(n : ℤ) ≤ 0) 1, meanSumAt_one] at hle
  have hcast : ((-(n : ℤ) - 0 : ℤ) : ℚ) = -(n : ℚ) := by push_cast; ring
  rw [hcast, zero_sub, abs_neg, abs_mul, abs_neg,
    abs_of_nonneg (Nat.cast_nonneg (α := ℚ) n)] at hle
  linarith

/-- **`centred_kernel_vanishes_on_full_periods`.**  `KERNEL-PROVED`.  The long-window
counterexample of §62.5 does *not* refute the centred target: on `n` full periods the centred
kernel is exactly `0`, i.e. the subtracted density term is exactly the obstruction found. -/
theorem centred_kernel_vanishes_on_full_periods (n : ℕ) :
    returnedKernel 0 ((bigPeriod : ℤ) * (n : ℤ)) 1
        - (((bigPeriod : ℤ) * (n : ℤ) - 0 : ℤ) : ℚ) * meanSumAt 1 = 0 := by
  rw [returnedKernel_long_window n, meanSumAt_one]
  push_cast
  ring

/-- **`frontier_repair_summary`.**  `KERNEL-PROVED` bookkeeping.  (i) the unnormalised
character interface is false; (ii) the pointwise `k = 1` target is false; (iii) the normalised
character interface is false; and (iv) the density-centred replacement target is not refuted
by the long-window witness.  Nothing here inhabits an open target. -/
theorem frontier_repair_summary (b : ℚ) :
    (¬ FixedConductorCharacterBound b) ∧ (¬ BoundedConductorK1Target b) ∧
      (¬ FixedConductorCharacterMeanBound b) ∧
      (∀ n : ℕ, returnedKernel 0 ((bigPeriod : ℤ) * (n : ℤ)) 1
        - (((bigPeriod : ℤ) * (n : ℤ) - 0 : ℤ) : ℚ) * meanSumAt 1 = 0) :=
  ⟨fixedConductorCharacterBound_unsatisfiable b, boundedConductorK1Target_unsatisfiable b,
    characterMeanBound_unsatisfiable b, centred_kernel_vanishes_on_full_periods⟩

end Effectivity
end Erdos287
