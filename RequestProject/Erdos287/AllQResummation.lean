import Mathlib
import RequestProject.Erdos287.AllComplement
import RequestProject.Erdos287.MediumLedger

/-!
# Erdős #287 effectivity — the exact all-`q` resummation (§28)

```
FINITE DIVISOR IDENTITY   : KERNEL-PROVED
ALL-q RESUMMATION ALGEBRA : KERNEL-PROVED
DISCREPANCY FORM          : KERNEL-PROVED (exact finite identity)
ANALYTIC DISCREPANCY      : OPEN / NOT ASSERTED
```

With the medium cutoff `K0 = 31` of §7 the long-fibre joined kernel is carried by

    A_b^>(n) = ∑_{q ∣ n, (q,b) = 1, b q > 31} β(q),
    P_b^>(Y) = ∑_{q ≤ Y, (q,b) = 1, b q > 31} β(q)/q.

Three exact finite facts are banked:

* the finite divisor identity `∑_{q ∣ n, (q,b)=1} β(q) = B(bn)/B(b)` (from §3);
* the exact all-`q` resummation `∑_{n ≤ X} A_b^>(n) = ∑_{q ≤ X, …} β(q) ⌊X/q⌋`;
* its exact rewriting in *smooth singular-series discrepancy form*

      ∑_{n ≤ X} A_b^>(n) = X · P_b^>(X) + ∑_{q ≤ X, …} β(q) (⌊X/q⌋ − X/q),

  in which the second term is the exact discrepancy.  **No estimate whatsoever for the
  discrepancy is asserted**: the identity is exact and the analytic smooth singular-series
  discrepancy theorem remains open.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §28.1  The long-fibre `q`-condition -/

/-- The `q`-lane condition of the long-fibre source: `q` coprime to `b` with `b q > K0`. -/
def LongFibreQ (b q : ℕ) : Prop := Nat.Coprime q b ∧ K0 < b * q

instance (b q : ℕ) : Decidable (LongFibreQ b q) := by
  unfold LongFibreQ; infer_instance

/-- `A_b^>(n) = ∑_{q ∣ n, (q,b)=1, b q > 31} β(q)`. -/
def AgtDivisorSum (b n : ℕ) : ℚ := ∑ q ∈ n.divisors with LongFibreQ b q, beta q

/-- `P_b^>(Y) = ∑_{q ≤ Y, (q,b)=1, b q > 31} β(q)/q`, the finite prefix. -/
def PgtPrefix (b Y : ℕ) : ℚ := ∑ q ∈ Finset.Icc 1 Y with LongFibreQ b q, beta q / q

/-! ## §28.2  The finite divisor identity -/

/-- `B0` is strictly positive. -/
theorem B0_pos (n : ℕ) : 0 < B0 n := by
  refine Finset.prod_pos fun p hp => ?_
  have hprime := oddPrimeFactors_prime hp
  have h2 := oddPrimeFactors_ne_two hp
  have h3 : 3 ≤ p := by have := hprime.two_le; omega
  have h3' : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h3
  exact div_pos (by linarith) (by linarith)

/-- `B(B1, n) ≠ 0` for `B1 ≠ 0`. -/
theorem B_ne_zero {B1 : ℚ} (hB1 : B1 ≠ 0) (n : ℕ) : B B1 n ≠ 0 :=
  mul_ne_zero hB1 (B0_pos n).ne'

/-- **`allQ_divisor_identity`.**  `KERNEL-PROVED`.  The finite divisor identity used by the
source:

    ∑_{q ∣ n, (q,b) = 1} β(q) = B_src(b n) / B_src(b). -/
theorem allQ_divisor_identity (B1 : ℚ) (hB1 : B1 ≠ 0) {b n : ℕ} (hb : b ≠ 0) (hn : n ≠ 0) :
    ∑ q ∈ n.divisors with Nat.Coprime q b, beta q = B B1 (b * n) / B B1 b := by
  have hkey := allComplement_discrete B1 hb hn
  have hsum : ∑ q ∈ n.divisors, betaCop b q = ∑ q ∈ n.divisors with Nat.Coprime q b, beta q := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun q _ => by unfold betaCop; split <;> rfl
  rw [hsum] at hkey
  field_simp [B_ne_zero hB1 b] at hkey ⊢
  linarith [hkey]

/-- **`AgtDivisorSum_eq`.**  `KERNEL-PROVED`.  The exact all-`q` split of the joined kernel:
the long-fibre part is the full divisor sum minus the finitely many small-`bq` terms. -/
theorem AgtDivisorSum_eq (B1 : ℚ) (hB1 : B1 ≠ 0) {b n : ℕ} (hb : b ≠ 0) (hn : n ≠ 0) :
    AgtDivisorSum b n
      = B B1 (b * n) / B B1 b
        - ∑ q ∈ n.divisors with (Nat.Coprime q b ∧ ¬ K0 < b * q), beta q := by
  classical
  have hsplit :
      ∑ q ∈ n.divisors with Nat.Coprime q b, beta q
        = (∑ q ∈ n.divisors with (Nat.Coprime q b ∧ K0 < b * q), beta q)
          + ∑ q ∈ n.divisors with (Nat.Coprime q b ∧ ¬ K0 < b * q), beta q := by
    rw [← Finset.filter_filter, ← Finset.filter_filter]
    exact (Finset.sum_filter_add_sum_filter_not
      (n.divisors.filter (fun q => Nat.Coprime q b)) (fun q => K0 < b * q) beta).symm
  have hA : AgtDivisorSum b n = ∑ q ∈ n.divisors with (Nat.Coprime q b ∧ K0 < b * q), beta q := rfl
  rw [hA, ← allQ_divisor_identity B1 hB1 hb hn, hsplit]
  ring

/-! ## §28.3  The exact all-`q` resummation -/

/-- **`allQ_resummation`.**  `KERNEL-PROVED`.  The exact hyperbola interchange:

    ∑_{n ≤ X} A_b^>(n) = ∑_{q ≤ X, (q,b)=1, b q > 31} β(q) ⌊X/q⌋. -/
theorem allQ_resummation (b X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, AgtDivisorSum b n
      = ∑ q ∈ Finset.Icc 1 X with LongFibreQ b q, beta q * ((X / q : ℕ) : ℚ) := by
  classical
  set F : ℕ → ℚ := fun q => if LongFibreQ b q then beta q else 0 with hF
  have hstep1 : ∀ n ∈ Finset.Icc 1 X, AgtDivisorSum b n = ∑ q ∈ n.divisors, F q := by
    intro n _
    rw [AgtDivisorSum, Finset.sum_filter]
  have hcomm : ∑ n ∈ Finset.Icc 1 X, ∑ q ∈ n.divisors, F q
      = ∑ q ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X with q ∣ n, F q := by
    refine Finset.sum_comm' ?_
    intro n q
    simp only [Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hn1, hnX⟩, hqn, _⟩
      have hq1 : 1 ≤ q := Nat.pos_of_dvd_of_pos hqn (by omega)
      have hqn' : q ≤ n := Nat.le_of_dvd (by omega) hqn
      exact ⟨⟨⟨hn1, hnX⟩, hqn⟩, hq1, le_trans hqn' hnX⟩
    · rintro ⟨⟨⟨hn1, hnX⟩, hqn⟩, _⟩
      exact ⟨⟨hn1, hnX⟩, hqn, by omega⟩
  have hcard : ∀ q : ℕ, ((Finset.Icc 1 X).filter (fun n => q ∣ n)).card = X / q := by
    intro q
    rw [show Finset.Icc 1 X = Finset.Ioc 0 X from rfl]
    exact Nat.Ioc_filter_dvd_card_eq_div X q
  calc ∑ n ∈ Finset.Icc 1 X, AgtDivisorSum b n
      = ∑ n ∈ Finset.Icc 1 X, ∑ q ∈ n.divisors, F q := Finset.sum_congr rfl hstep1
    _ = ∑ q ∈ Finset.Icc 1 X, ∑ _n ∈ Finset.Icc 1 X with q ∣ _n, F q := hcomm
    _ = ∑ q ∈ Finset.Icc 1 X, F q * ((X / q : ℕ) : ℚ) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_const, hcard q, nsmul_eq_mul]
        ring
    _ = ∑ q ∈ Finset.Icc 1 X with LongFibreQ b q, beta q * ((X / q : ℕ) : ℚ) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hF]
        by_cases h : LongFibreQ b q <;> simp [h]

/-- **`allQ_discrepancy_form`.**  `KERNEL-PROVED`.  The exact rewriting of the all-`q`
resummation into smooth singular-series discrepancy form: main term plus an *exact* finite
discrepancy sum.  No estimate for the discrepancy term is claimed. -/
theorem allQ_discrepancy_form (b X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, AgtDivisorSum b n
      = (X : ℚ) * PgtPrefix b X
        + ∑ q ∈ Finset.Icc 1 X with LongFibreQ b q,
            beta q * (((X / q : ℕ) : ℚ) - (X : ℚ) / (q : ℚ)) := by
  classical
  rw [allQ_resummation b X, PgtPrefix, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq1 : 1 ≤ q := (Finset.mem_Icc.1 (Finset.mem_filter.1 hq).1).1
  have hq' : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  field_simp
  ring

end Effectivity
end Erdos287
