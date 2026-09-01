import Mathlib
import RequestProject.Erdos287.AggregateEulerLocal3221
import RequestProject.Erdos287.PrincipalQCell3221

/-!
# Semantic repair layer §8–§10 — the repaired finite `B`-source and the V2 comparison
interfaces

`SP2-PHYSICAL-BCOMPARISON-SOURCE45`

## What is preserved

Nothing is deleted or rewritten.  The banked finite identity
`Erdos287.V23Euler.aggregateEuler_H0_eq_twoB` and the old interfaces
`AggregateEulerPrincipal287Input`, `AggregateEulerUniformity287Input`,
`SP2PhysicalTwoBIndependent287Input` stay exactly as they are.

## What is repaired

* **The finite `B` source.**  `Bsrc S2 P = S2 · ∏_{p ∣ P, p > 2} (p−1)/(p−2)` — the banked
  `BofP`, reused, with the singular constant `S₂` kept as an *external parameter*.  Under
  `0 < S₂ < 1` and `ω(P) ≤ 7` the finite consequences `0 < Bsrc` and `Bsrc < 128` are
  proved, together with the sharper `Bsrc < 2` when every odd prime divisor is `≥ 256`.
  The infinite Euler product for `S₂` is **not** formalised, and is not assumed.

* **The rigid error normalisation.**  The old interfaces demand
  `|J(P,z) − 2B(P)| ≤ log(z)^{−A}` for **every** `z ≥ 2` with coefficient exactly `1`.  The
  paper theorem is `O_A(log(z)^{−A})`.  The V2 interfaces carry **both** an explicit
  constant `Cerr > 0` and a threshold `z₀ ≥ 2`.  `old → V2` is proved; the converse is
  refuted at the level of the error shapes (`v2_shape_does_not_imply_old_shape`).

Nothing analytic is proved here, and the external zeta-contour estimate is **not** claimed
to be kernel-proved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace BComparisonV2

open Finset
open Erdos287.V23Euler
open Erdos287.V23Comparison
open Erdos287.V23Principal

/-! ## §1.  The finite physical `B` source with an external singular constant -/

/-- **`Bsrc`** — the corrected finite physical `B` source: the external singular parameter
`S₂` times the finite divisor correction.  This is the banked `BofP`, reused. -/
noncomputable def Bsrc (S2 : ℝ) (P : ℕ) : ℝ := BofP S2 P

theorem Bsrc_eq_BofP (S2 : ℝ) (P : ℕ) : Bsrc S2 P = BofP S2 P := rfl

/-- The finite correction is the product over the odd prime divisors. -/
theorem Bsrc_def (S2 : ℝ) (P : ℕ) :
    Bsrc S2 P = S2 * ∏ p ∈ oddPrimeDivisors P, ((p : ℝ) - 1) / ((p : ℝ) - 2) := rfl

theorem localCorrection_pos {P p : ℕ} (hp : p ∈ oddPrimeDivisors P) :
    0 < ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  have h3 : (3 : ℝ) ≤ (p : ℝ) := three_le_of_mem_oddPrimeDivisors hp
  apply div_pos <;> linarith

theorem localCorrection_le_two {P p : ℕ} (hp : p ∈ oddPrimeDivisors P) :
    ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤ 2 := by
  have h3 : (3 : ℝ) ≤ (p : ℝ) := three_le_of_mem_oddPrimeDivisors hp
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- The finite correction factor is positive. -/
theorem correction_pos (P : ℕ) :
    0 < ∏ p ∈ oddPrimeDivisors P, ((p : ℝ) - 1) / ((p : ℝ) - 2) :=
  Finset.prod_pos fun _ hp => localCorrection_pos hp

/-- The odd prime divisors are among the prime factors. -/
theorem oddPrimeDivisors_card_le {P : ℕ} (h : P.primeFactors.card ≤ 7) :
    (oddPrimeDivisors P).card ≤ 7 :=
  le_trans (Finset.card_le_card (Finset.filter_subset _ _)) h

/-- The finite correction factor is at most `2^{ω(P)} ≤ 128`. -/
theorem correction_le_128 {P : ℕ} (h : P.primeFactors.card ≤ 7) :
    (∏ p ∈ oddPrimeDivisors P, ((p : ℝ) - 1) / ((p : ℝ) - 2)) ≤ 128 := by
  have hle : (∏ p ∈ oddPrimeDivisors P, ((p : ℝ) - 1) / ((p : ℝ) - 2))
      ≤ ∏ _p ∈ oddPrimeDivisors P, (2 : ℝ) :=
    Finset.prod_le_prod (fun p hp => (localCorrection_pos hp).le)
      (fun p hp => localCorrection_le_two hp)
  rw [Finset.prod_const] at hle
  refine le_trans hle ?_
  have hpow : (2 : ℝ) ^ (oddPrimeDivisors P).card ≤ (2 : ℝ) ^ 7 :=
    pow_le_pow_right₀ (by norm_num) (oddPrimeDivisors_card_le h)
  refine le_trans hpow ?_
  norm_num

/-- **`Bsrc_pos`.**  `LEAN_PROVED`.  `0 < S₂ ⟹ 0 < Bsrc(S₂,P)`. -/
theorem Bsrc_pos {S2 : ℝ} (hS2 : 0 < S2) (P : ℕ) : 0 < Bsrc S2 P :=
  mul_pos hS2 (correction_pos P)

/-- **`Bsrc_lt_128`.**  `LEAN_PROVED`.

`0 < S₂ < 1` and `ω(P) ≤ 7` give the finite bound `Bsrc(S₂,P) < 128`. -/
theorem Bsrc_lt_128 {S2 : ℝ} (hS2' : S2 < 1) {P : ℕ}
    (hP : P.primeFactors.card ≤ 7) : Bsrc S2 P < 128 := by
  have hcorr := correction_pos P
  have hlt : S2 * ∏ p ∈ oddPrimeDivisors P, ((p : ℝ) - 1) / ((p : ℝ) - 2)
      < 1 * ∏ p ∈ oddPrimeDivisors P, ((p : ℝ) - 1) / ((p : ℝ) - 2) :=
    mul_lt_mul_of_pos_right hS2' hcorr
  rw [Bsrc_def]
  calc S2 * ∏ p ∈ oddPrimeDivisors P, ((p : ℝ) - 1) / ((p : ℝ) - 2)
      < ∏ p ∈ oddPrimeDivisors P, ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
        simpa using hlt
    _ ≤ 128 := correction_le_128 hP

/-- The sharper finite correction in the physical regime `p ≥ 256`. -/
theorem correction_le_of_large_primes {P : ℕ} (h : P.primeFactors.card ≤ 7)
    (hbig : ∀ p ∈ oddPrimeDivisors P, 256 ≤ p) :
    (∏ p ∈ oddPrimeDivisors P, ((p : ℝ) - 1) / ((p : ℝ) - 2)) ≤ 2 := by
  have hle : (∏ p ∈ oddPrimeDivisors P, ((p : ℝ) - 1) / ((p : ℝ) - 2))
      ≤ ∏ _p ∈ oddPrimeDivisors P, (255 / 254 : ℝ) := by
    refine Finset.prod_le_prod (fun p hp => (localCorrection_pos hp).le) (fun p hp => ?_)
    have h256 : (256 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hbig p hp
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  rw [Finset.prod_const] at hle
  refine le_trans hle ?_
  have hmono : (255 / 254 : ℝ) ^ (oddPrimeDivisors P).card ≤ (255 / 254 : ℝ) ^ 7 :=
    pow_le_pow_right₀ (by norm_num) (oddPrimeDivisors_card_le h)
  refine le_trans hmono ?_
  norm_num

/-- **`Bsrc_lt_two_of_large_primes`.**  `LEAN_PROVED`. -/
theorem Bsrc_lt_two_of_large_primes {S2 : ℝ} (hS2' : S2 < 1) {P : ℕ}
    (hP : P.primeFactors.card ≤ 7) (hbig : ∀ p ∈ oddPrimeDivisors P, 256 ≤ p) :
    Bsrc S2 P < 2 := by
  have hcorr := correction_pos P
  rw [Bsrc_def]
  calc S2 * ∏ p ∈ oddPrimeDivisors P, ((p : ℝ) - 1) / ((p : ℝ) - 2)
      < ∏ p ∈ oddPrimeDivisors P, ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
        simpa using mul_lt_mul_of_pos_right hS2' hcorr
    _ ≤ 2 := correction_le_of_large_primes hP hbig

/-! ## §2.  The two error normalisations, as bare shapes -/

/-- The **old** rigid shape: coefficient exactly `1`, for every `z ≥ 2`. -/
def OldErrShape (E : ℝ → ℝ) (A : ℝ) : Prop :=
  ∀ z : ℝ, 2 ≤ z → |E z| ≤ (Real.log z) ^ (-A)

/-- The **V2** shape: an explicit constant `Cerr > 0` *and* a threshold `z₀ ≥ 2`. -/
structure V2ErrShape (E : ℝ → ℝ) (A Cerr z0 : ℝ) : Prop where
  /-- The implied constant is positive. -/
  Cerr_pos : 0 < Cerr
  /-- The threshold is admissible. -/
  z0_ge_two : 2 ≤ z0
  /-- The asymptotic bound above the threshold. -/
  bound : ∀ z : ℝ, z0 ≤ z → |E z| ≤ Cerr * (Real.log z) ^ (-A)

/-- **`v2_shape_of_old_shape`.**  `LEAN_PROVED`.  The old normalisation is the special case
`Cerr = 1`, `z₀ = 2`. -/
theorem v2_shape_of_old_shape {E : ℝ → ℝ} {A : ℝ} (h : OldErrShape E A) :
    V2ErrShape E A 1 2 :=
  ⟨one_pos, le_refl 2, fun z hz => by simpa using h z hz⟩

/-- **`v2_shape_does_not_imply_old_shape`.**  `LEAN_PROVED`.

The normalisation firewall: the V2 asymptotic shape does **not** propositionally imply the
coefficient-one / all-`z` old shape.  Witness: `E(z) = 3 log(z)^{−1}`. -/
theorem v2_shape_does_not_imply_old_shape :
    ∃ (E : ℝ → ℝ) (A Cerr z0 : ℝ), V2ErrShape E A Cerr z0 ∧ ¬ OldErrShape E A := by
  refine ⟨fun z => 3 * (Real.log z) ^ (-(1 : ℝ)), 1, 3, 2, ⟨by norm_num, le_refl 2, ?_⟩, ?_⟩
  · intro z hz
    have hlog : 0 < Real.log z :=
      Real.log_pos (by linarith)
    have hpow : 0 < (Real.log z) ^ (-(1 : ℝ)) := Real.rpow_pos_of_pos hlog _
    rw [abs_of_pos (by positivity)]
  · intro hold
    have h2 := hold 2 (le_refl 2)
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hpow : 0 < (Real.log 2) ^ (-(1 : ℝ)) := Real.rpow_pos_of_pos hlog _
    rw [abs_of_pos (by positivity)] at h2
    linarith

/-! ## §3.  The V2 aggregate interfaces (uninhabited) -/

/-- **`AggregateEulerPrincipal287InputV2`** — `EXTERNAL / UNINHABITED`.

The corrected normalisation of the aggregate `μ/φ·log` statement: same `q`-partition, same
repeated-prime compatibility, but with an implied constant `Cerr` **and** a threshold `z₀`,
matching `O_A(log^{−A} z)`. -/
structure AggregateEulerPrincipal287InputV2
    (J : ℕ → ℝ → ℝ) (S2 : ℝ) (family : Finset ℕ) (Aexp Cerr z0 : ℝ)
    (effective : Bool) : Prop where
  /-- The `q`-cells summed by `J` are exactly the literal ones. -/
  q_partition_compatible : ∀ P ∈ family, ∀ z : ℝ, 2 ≤ z →
    J P z = ∑ q ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun q => Nat.Coprime q (2 * P)),
      (ArithmeticFunction.moebius q : ℝ) / (q.totient : ℝ) * Real.log (z / q)
  /-- The implied constant. -/
  Cerr_pos : 0 < Cerr
  /-- The threshold. -/
  z0_ge_two : 2 ≤ z0
  /-- The error bound, uniform in `P`, above the threshold, with the implied constant. -/
  uniform_in_P : ∀ P ∈ family, ∀ z : ℝ, z0 ≤ z →
    |J P z - 2 * Bsrc S2 P| ≤ Cerr * (Real.log z) ^ (-Aexp)
  /-- Repeated primes are handled by the same statement. -/
  repeated_primes : ∀ P ∈ family, ∀ z : ℝ, 2 ≤ z → J P z = J (∏ p ∈ P.primeFactors, p) z
  /-- The declared log saving is positive. -/
  saving_positive : 0 < Aexp

/-- **`AggregateEulerUniformity287InputV2`** — `EXTERNAL / UNINHABITED`. -/
structure AggregateEulerUniformity287InputV2
    (F H : ℕ → ℂ → ℂ) (zetaInv : ℂ → ℂ) (J : ℕ → ℝ → ℝ) (S2 : ℝ)
    (family : Finset ℕ) (contour : Set ℂ) (Hbound A0 Cerr z0 : ℝ) : Prop where
  /-- `F_P(w) = H_P(w)/ζ(1+w)` on the contour region. -/
  factorisation : ∀ P ∈ family, ∀ w ∈ contour, F P w = H P w * zetaInv w
  /-- A uniform bound on `H_P(w)`. -/
  uniform_H_bound : ∀ P ∈ family, ∀ w ∈ contour, ‖H P w‖ ≤ Hbound
  /-- The contour is a genuine region. -/
  contour_nonempty : contour.Nonempty
  /-- The fixed sufficient log saving. -/
  saving_positive : 0 < A0
  /-- The implied constant. -/
  Cerr_pos : 0 < Cerr
  /-- The threshold. -/
  z0_ge_two : 2 ≤ z0
  /-- The resulting aggregate bound, in `O_A` shape. -/
  aggregate_bound : ∀ P ∈ family, ∀ z : ℝ, z0 ≤ z →
    |J P z - 2 * Bsrc S2 P| ≤ Cerr * Hbound * (Real.log z) ^ (-A0)

/-- **`SP2PhysicalTwoBIndependent287InputV2`** — `EXTERNAL / UNINHABITED`. -/
structure SP2PhysicalTwoBIndependent287InputV2
    (C : SP2PhysicalCell) (BsrcFun : ℕ → ℝ) (J : ℕ → ℝ → ℝ) (Aexp Cerr z0 : ℝ) : Prop where
  /-- The physical `B`-field of the cell is the SP-2 source function. -/
  physical_B_is_source : ∀ pv ∈ C.cell, C.B (physModulus pv) = BsrcFun (physModulus pv)
  /-- The source function is defined on the whole physical family. -/
  source_total : ∀ pv ∈ C.cell, 0 ≤ BsrcFun (physModulus pv)
  /-- The implied constant. -/
  Cerr_pos : 0 < Cerr
  /-- The threshold. -/
  z0_ge_two : 2 ≤ z0
  /-- The aggregate limit in `O_A` shape. -/
  aggregate_limit : ∀ pv ∈ C.cell, ∀ z : ℝ, z0 ≤ z →
    |J (physModulus pv) z - 2 * BsrcFun (physModulus pv)| ≤ Cerr * (Real.log z) ^ (-Aexp)
  /-- The declared log saving is positive. -/
  saving_positive : 0 < Aexp

/-! ## §4.  `OLD INPUT → V2 INPUT` -/

/-- **`aggregatePrincipalV2_of_old`.**  `LEAN_PROVED`. -/
theorem aggregatePrincipalV2_of_old {J : ℕ → ℝ → ℝ} {S2 : ℝ} {family : Finset ℕ}
    {Aexp : ℝ} {effective : Bool}
    (h : AggregateEulerPrincipal287Input J S2 family Aexp effective) :
    AggregateEulerPrincipal287InputV2 J S2 family Aexp 1 2 effective where
  q_partition_compatible := h.q_partition_compatible
  Cerr_pos := one_pos
  z0_ge_two := le_refl 2
  uniform_in_P := by
    intro P hP z hz
    simpa [Bsrc_eq_BofP] using h.uniform_in_P P hP z hz
  repeated_primes := h.repeated_primes
  saving_positive := h.saving_positive

/-- **`aggregateUniformityV2_of_old`.**  `LEAN_PROVED`. -/
theorem aggregateUniformityV2_of_old {F H : ℕ → ℂ → ℂ} {zetaInv : ℂ → ℂ} {J : ℕ → ℝ → ℝ}
    {S2 : ℝ} {family : Finset ℕ} {contour : Set ℂ} {Hbound A0 : ℝ}
    (h : AggregateEulerUniformity287Input F H zetaInv J S2 family contour Hbound A0) :
    AggregateEulerUniformity287InputV2 F H zetaInv J S2 family contour Hbound A0 1 2 where
  factorisation := h.factorisation
  uniform_H_bound := h.uniform_H_bound
  contour_nonempty := h.contour_nonempty
  saving_positive := h.saving_positive
  Cerr_pos := one_pos
  z0_ge_two := le_refl 2
  aggregate_bound := by
    intro P hP z hz
    simpa [Bsrc_eq_BofP] using h.aggregate_bound P hP z hz

/-- **`twoBIndependentV2_of_old`.**  `LEAN_PROVED`. -/
theorem twoBIndependentV2_of_old {C : SP2PhysicalCell} {BsrcFun : ℕ → ℝ} {J : ℕ → ℝ → ℝ}
    {Aexp : ℝ} (h : SP2PhysicalTwoBIndependent287Input C BsrcFun J Aexp) :
    SP2PhysicalTwoBIndependent287InputV2 C BsrcFun J Aexp 1 2 where
  physical_B_is_source := h.physical_B_is_source
  source_total := h.source_total
  Cerr_pos := one_pos
  z0_ge_two := le_refl 2
  aggregate_limit := by
    intro pv hpv z hz
    simpa using h.aggregate_limit pv hpv z hz
  saving_positive := h.saving_positive

/-! ## §5.  The V2 interfaces are genuine restrictions and are left uninhabited -/

theorem aggregatePrincipalV2_not_automatic :
    ∃ (J : ℕ → ℝ → ℝ) (S2 : ℝ) (family : Finset ℕ) (Aexp Cerr z0 : ℝ) (effective : Bool),
      ¬ AggregateEulerPrincipal287InputV2 J S2 family Aexp Cerr z0 effective := by
  refine ⟨fun _ _ => 0, 0, ∅, -1, 1, 2, true, ?_⟩
  intro h
  exact absurd h.saving_positive (by norm_num)

theorem aggregateUniformityV2_not_automatic :
    ∃ (F H : ℕ → ℂ → ℂ) (zetaInv : ℂ → ℂ) (J : ℕ → ℝ → ℝ) (S2 : ℝ)
      (family : Finset ℕ) (contour : Set ℂ) (Hbound A0 Cerr z0 : ℝ),
      ¬ AggregateEulerUniformity287InputV2 F H zetaInv J S2 family contour Hbound A0
          Cerr z0 := by
  refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ => 0, fun _ _ => 0, 0, ∅, ∅, 0, 1, 1, 2, ?_⟩
  intro h
  exact absurd h.contour_nonempty (by simp)

theorem twoBIndependentV2_not_automatic :
    ∃ (C : SP2PhysicalCell) (BsrcFun : ℕ → ℝ) (J : ℕ → ℝ → ℝ) (Aexp Cerr z0 : ℝ),
      ¬ SP2PhysicalTwoBIndependent287InputV2 C BsrcFun J Aexp Cerr z0 := by
  classical
  refine ⟨⟨{fun _ => 1}, fun _ => 1, fun _ => 0⟩, fun _ => -1, fun _ _ => 0, 1, 1, 2, ?_⟩
  intro h
  have h1 := h.source_total (fun _ => 1) (Finset.mem_singleton_self _)
  norm_num at h1

/-- **`bComparison_analytic_is_not_kernel_proved`.**  `LEAN_PROVED` (status theorem).

The V2 analytic input is a *restriction*, not a theorem of this repository: it is refuted at
explicit data, and no inhabitant is constructed anywhere. -/
theorem bComparison_analytic_is_not_kernel_proved :
    ∃ (C : SP2PhysicalCell) (BsrcFun : ℕ → ℝ) (J : ℕ → ℝ → ℝ) (Aexp Cerr z0 : ℝ),
      ¬ SP2PhysicalTwoBIndependent287InputV2 C BsrcFun J Aexp Cerr z0 :=
  twoBIndependentV2_not_automatic

end BComparisonV2
end Erdos287
