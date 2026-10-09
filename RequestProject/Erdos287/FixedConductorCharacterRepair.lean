import Mathlib
import RequestProject.Erdos287.BoundedConductorFrontier

/-!
# Erdős #287 effectivity — repair of the fixed-conductor character interface (§61)

```
FixedConductorCharacterBound AS STATED   : KERNEL-REFUTED (unsatisfiable for every budget)
character_bound_implies_k1_owner_bound   : VACUOUS (its hypothesis is never inhabitable)
NORMALISED CHARACTER BOUND               : KERNEL-PROVED EQUIVALENT to the k = 1 target
```

`BoundedConductorFrontier` states the current `k = 1` analytic frontier as

    FixedConductorCharacterBound b :
      ∀ A B (Zset : Finset ℤ) (w : ℤ → ℚ), (∀ z, |w z| ≤ 1) →
        |∑ z ∈ Zset, w z * returnedKernel A B z| ≤ b

i.e. an *unnormalised* signed outer-`z` sum against unit weights over an **arbitrary finite**
set of outer points `Zset`.  This module proves that this statement is **false for every
budget `b`**, so the interface as written can never be inhabited and the conditional bridge
`character_bound_implies_k1_owner_bound` is vacuous.

The obstruction is elementary and purely structural: with the one-point physical window
`[A,B) = [2503, 2504)` only the internal conductor `ℓ = 2503` survives (2503 is prime and
`2·2503 > 5000`, so no other `ℓ ∈ (1000,5000]` shares a prime factor with `s = 2503`), and the
surviving value is *periodic* in the outer variable `z` with period `2503`.  Summing `n`
outer points in one residue class therefore produces exactly `n` copies of a fixed nonzero
rational, which exceeds any prescribed budget.

The repair is to normalise by the number of outer points:

    FixedConductorCharacterMeanBound b :
      ∀ A B Zset w, (∀ z, |w z| ≤ 1) →
        |∑ z ∈ Zset, w z * returnedKernel A B z| ≤ b * Zset.card

and `characterMeanBound_iff_boundedConductorTarget` proves that this normalised statement is
**exactly equivalent** to `BoundedConductorK1Target b`.  In particular the character/DFT
packaging of the frontier carries no content beyond the pointwise bounded-conductor target:
the genuine open analytic problem is `BoundedConductorK1Target`, and no signed gain can be
extracted from the outer sum by unit weights alone.

Nothing here inhabits any open target: `BoundedConductorK1Target` remains OPEN.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §61.1  A one-point physical window isolates a single conductor -/

/-- `2503` is prime. -/
lemma prime_2503 : Nat.Prime 2503 := by norm_num

/-- For `1000 < ℓ ≤ 5000` other than `ℓ = 2503`, the conductor `ℓ` shares no prime factor
with `s = 2503`. -/
lemma gcdFactors_2503_eq_empty {ell : ℕ} (h1 : 1001 ≤ ell) (h2 : ell ≤ 5000)
    (hne : ell ≠ 2503) : gcdFactors ell (2503 : ℤ) = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
  rw [gcdFactors, Finset.mem_filter] at hp
  obtain ⟨hmem, hdvd⟩ := hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hmem
  have hpell : p ∣ ell := Nat.dvd_of_mem_primeFactors hmem
  have hpn : p ∣ 2503 := by exact_mod_cast hdvd
  have hpeq : p = 2503 := (Nat.prime_dvd_prime_iff_eq hpp prime_2503).1 hpn
  subst hpeq
  obtain ⟨k, hk⟩ := hpell
  omega

/-- If `ℓ` has no prime factor in common with `s`, the local kernel vanishes. -/
lemma Kell_eq_zero_of_gcdFactors_empty {ell : ℕ} {s z : ℤ} (h : gcdFactors ell s = ∅) :
    Kell ell s z = 0 := by
  rw [Kell, h, Finset.prod_empty, sub_self, mul_zero]

/-- **`returnedKernel_one_point_window`.**  `KERNEL-PROVED`.  On the one-point physical window
`[2503, 2504)` the whole returned finite-conductor kernel reduces to the single internal
conductor `ℓ = 2503`. -/
theorem returnedKernel_one_point_window (z : ℤ) :
    returnedKernel 2503 2504 z = Kell 2503 (2503 : ℤ) z := by
  classical
  have hwin : Finset.Ico (2503 : ℤ) 2504 = {(2503 : ℤ)} := by
    ext s; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
  have hstep : ∀ ell ∈ Finset.Icc 1001 5000,
      Qell ell 2503 2504 z = Kell ell (2503 : ℤ) z := by
    intro ell hell
    rw [Finset.mem_Icc] at hell
    rw [← Qell_compiler (by omega : 0 < ell), hwin, Finset.sum_singleton]
  rw [returnedKernel, Finset.sum_congr rfl hstep]
  refine Finset.sum_eq_single 2503 (fun ell hell hne => ?_) (fun hmem => ?_)
  · rw [Finset.mem_Icc] at hell
    exact Kell_eq_zero_of_gcdFactors_empty (gcdFactors_2503_eq_empty hell.1 hell.2 hne)
  · exact absurd (Finset.mem_Icc.2 ⟨by norm_num, by norm_num⟩) hmem

/-! ## §61.2  The surviving value is periodic in the outer variable -/

/-- The coprimality mask of the prime conductor `2503` at any `x ≡ 1 (mod 2503)` is `1`. -/
lemma coprimeMask_2503_shift (t : ℤ) : coprimeMask 2503 (1 + 2503 * t) = 1 := by
  have hfac : (2503 : ℕ).primeFactors = {2503} := prime_2503.primeFactors
  rw [coprimeMask, hfac, Finset.prod_singleton]
  have hnd : ¬ ((2503 : ℤ) ∣ 1 + 2503 * t) := by
    intro h
    have h1 : (2503 : ℤ) ∣ 1 := (dvd_add_left ⟨t, rfl⟩).1 h
    have := Int.le_of_dvd one_pos h1
    omega
  rw [if_neg (by exact_mod_cast hnd)]

/-- **`returnedKernel_outer_periodic`.**  `KERNEL-PROVED`.  On the one-point window the
returned kernel takes the *same* value at every outer point `z = 2504 + 2503·t`. -/
theorem returnedKernel_outer_periodic (t : ℤ) :
    returnedKernel 2503 2504 (2504 + 2503 * t) = returnedKernel 2503 2504 2504 := by
  rw [returnedKernel_one_point_window, returnedKernel_one_point_window, Kell, Kell]
  have h1 : (2504 : ℤ) + 2503 * t - 2503 = 1 + 2503 * t := by ring
  have h2 : (2504 : ℤ) - 2503 = 1 + 2503 * 0 := by ring
  rw [h1, h2, coprimeMask_2503_shift, coprimeMask_2503_shift]

/-- **`returnedKernel_one_point_ne_zero`.**  `KERNEL-PROVED`.  The surviving value is a
nonzero rational. -/
theorem returnedKernel_one_point_ne_zero : returnedKernel 2503 2504 2504 ≠ 0 := by
  rw [returnedKernel_one_point_window]
  have hsq : Squarefree (2503 : ℕ) := prime_2503.squarefree
  have hodd : ¬ (2 ∣ (2503 : ℕ)) := by norm_num
  have h := Kell_ne_zero_at_prime_atom (ell := 2503) (p := 2503) hsq hodd prime_2503 dvd_rfl
  norm_num at h
  exact h

/-! ## §61.3  The unnormalised character interface is unsatisfiable -/

/-- The finite set of outer points `{2504 + 2503·t : t < n}`. -/
def outerPoints (n : ℕ) : Finset ℤ := (Finset.range n).image (fun t : ℕ => 2504 + 2503 * (t : ℤ))

lemma outerPoints_card (n : ℕ) : (outerPoints n).card = n := by
  rw [outerPoints, Finset.card_image_of_injective _ (fun a b hab => by omega),
    Finset.card_range]

lemma sum_returnedKernel_outerPoints (n : ℕ) :
    ∑ z ∈ outerPoints n, returnedKernel 2503 2504 z
      = (n : ℚ) * returnedKernel 2503 2504 2504 := by
  have hval : ∀ t ∈ Finset.range n,
      returnedKernel 2503 2504 (2504 + 2503 * (t : ℤ)) = returnedKernel 2503 2504 2504 :=
    fun t _ => returnedKernel_outer_periodic (t : ℤ)
  rw [outerPoints, Finset.sum_image (fun a _ b _ hab => by omega), Finset.sum_congr rfl hval,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **`fixedConductorCharacterBound_unsatisfiable`.**  `KERNEL-PROVED`.  The frontier
interface `FixedConductorCharacterBound` — the *unnormalised* signed outer-`z` sum over an
arbitrary finite set of outer points — is **false for every budget `b`**.  It can therefore
never be inhabited, and its formalisation has to be normalised (see §61.4). -/
theorem fixedConductorCharacterBound_unsatisfiable (b : ℚ) :
    ¬ FixedConductorCharacterBound b := by
  intro h
  set c : ℚ := returnedKernel 2503 2504 2504 with hc
  have hcpos : 0 < |c| := abs_pos.2 returnedKernel_one_point_ne_zero
  obtain ⟨n, hn⟩ := exists_nat_gt (b / |c|)
  have hbig : b < (n : ℚ) * |c| := by
    rw [div_lt_iff₀ hcpos] at hn
    linarith
  have hw : ∀ z : ℤ, |(1 : ℚ)| ≤ 1 := fun _ => by norm_num
  have hle := h 2503 2504 (outerPoints n) (fun _ => (1 : ℚ)) hw
  rw [Finset.sum_congr rfl (fun z _ => one_mul (returnedKernel 2503 2504 z)),
    sum_returnedKernel_outerPoints n, abs_mul, abs_of_nonneg (by positivity : (0:ℚ) ≤ (n:ℚ))]
    at hle
  linarith

/-- **`character_bound_bridge_is_vacuous`.**  `KERNEL-PROVED`.  Consequently the banked
conditional bridge `character_bound_implies_k1_owner_bound` has a hypothesis that is never
satisfiable: it yields no route to the `k = 1` owner bound. -/
theorem character_bound_bridge_is_vacuous :
    ∀ b : ℚ, ¬ FixedConductorCharacterBound b :=
  fixedConductorCharacterBound_unsatisfiable

/-! ## §61.4  The normalised (repaired) character interface -/

/-- **Repaired interface.**  The signed outer-`z` sum against unit weights, normalised by the
number of outer points. -/
def FixedConductorCharacterMeanBound (b : ℚ) : Prop :=
  ∀ (A B : ℤ) (Zset : Finset ℤ) (w : ℤ → ℚ), (∀ z, |w z| ≤ 1) →
    |∑ z ∈ Zset, w z * returnedKernel A B z| ≤ b * (Zset.card : ℚ)

/-- **`characterMeanBound_iff_boundedConductorTarget`.**  `KERNEL-PROVED`.  The normalised
character interface is *exactly equivalent* to the pointwise bounded-conductor `k = 1`
target.  Hence the character/DFT packaging adds nothing: the whole content of the frontier is
the pointwise bound, and no cancellation gain is available from unit weights on the outer
variable. -/
theorem characterMeanBound_iff_boundedConductorTarget (b : ℚ) :
    FixedConductorCharacterMeanBound b ↔ BoundedConductorK1Target b := by
  constructor
  · intro h A B z
    have hw : ∀ y : ℤ, |(1 : ℚ)| ≤ 1 := fun _ => by norm_num
    have := h A B {z} (fun _ => (1 : ℚ)) hw
    simpa using this
  · intro h A B Zset w hw
    have hb : 0 ≤ b := le_trans (abs_nonneg _) (h 0 0 0)
    calc |∑ z ∈ Zset, w z * returnedKernel A B z|
        ≤ ∑ z ∈ Zset, |w z * returnedKernel A B z| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _z ∈ Zset, b := by
            refine Finset.sum_le_sum fun z _ => ?_
            rw [abs_mul]
            calc |w z| * |returnedKernel A B z| ≤ 1 * |returnedKernel A B z| :=
                  mul_le_mul_of_nonneg_right (hw z) (abs_nonneg _)
              _ = |returnedKernel A B z| := one_mul _
              _ ≤ b := h A B z
      _ = b * (Zset.card : ℚ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **`characterMeanBound_implies_k1_owner_bound`.**  `KERNEL-PROVED` (conditional).  The
repaired bridge: the normalised character bound implies the `k = 1` owner bound. -/
theorem characterMeanBound_implies_k1_owner_bound {b : ℚ}
    (h : FixedConductorCharacterMeanBound b) : BoundedConductorK1Target b :=
  (characterMeanBound_iff_boundedConductorTarget b).1 h

/-- **`repaired_target_not_inhabited`.**  `KERNEL-PROVED` bookkeeping.  Nothing in this module
inhabits an open target: the repaired interface is equivalent to `BoundedConductorK1Target`,
which is still OPEN and is not inhabited here. -/
theorem repaired_target_not_inhabited (b : ℚ) :
    (FixedConductorCharacterMeanBound b ↔ BoundedConductorK1Target b) ∧
      ¬ FixedConductorCharacterBound b :=
  ⟨characterMeanBound_iff_boundedConductorTarget b,
    fixedConductorCharacterBound_unsatisfiable b⟩

end Effectivity
end Erdos287
