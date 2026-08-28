import Mathlib
import RequestProject.Erdos287.FiveBoxCharacterFactorization3221

/-!
# V20, Phases D / E / G / H — diagonal child, low-quotient child, capacity firewalls, router

`3221-HIGHCOND-DIAGONAL45 : EXTERNAL-ANALYTIC / CONDITIONAL COMPILER`
`3221-LOWQUOTIENT-CONDUCTOR-COLLAPSE45 : CONDITIONAL / EXTERNAL CLOSED`
`3221-POINTWISE-BURGESS45 : EXTERNAL CAPACITY NONCLOSING GLOBALLY`
`3221-BURGESS-CONDUCTOR-PAIR-ROUTER45 : CONDITIONAL EXTERNAL PASS`

**No external analytic theorem is formalised, assumed or axiomatised here.**  The classical
multiplicative large sieve and the Burgess bound appear *only* as uninhabited external
input structures carrying their intended shape; nothing in this repository inhabits them,
and no theorem converts their metadata into a mathematical claim.  Everything actually
proved below is finite algebra, elementary inequality chaining, or exact rational
arithmetic.

## Contents

* **§12.**  `PrimitiveConductorLargeSieve3221Input` — external, uninhabited, with the
  intended shape `E(R) ≤ logC · (Q/R) · (R² + W5) · ‖c‖₂²`, and the explicit conductor
  cutoff `Dcut` and its exponent `B0` recorded as *data of the input*.
  `largeSieve_not_automatic` shows it is a genuine restriction.
* **§13.**  `highCondDiagonal_of_largeSieve` — the conditional diagonal compiler, with the
  cutoff `B0` kept explicit.  `EXTERNAL-ANALYTIC CLOSED / CONDITIONAL COMPILER`, never
  relabelled `LEAN_PROVED` analytic.
* **§14.**  The diagonal exponent ledger: `diagonal_fixed_power_room = 4/35`,
  `diagonal_power_room_rational`, `diagonal_power_room_rpow`.
* **§15.**  `lowConductor_card_le` — the finite conductor count
  `#{ξ : cond ξ ≤ L} ≤ ∑_{r ∣ q, r ≤ L} φ(r)`, **proved**, with no logarithmic asymptotic
  claimed anywhere.
* **§16.**  `lowQuotient_child_le` — the finite low-quotient compiler, and
  `lowQuotient_child_of_diagonal_budget`.
* **§20.**  `PointwiseBurgess3221Input` — external, uninhabited, metadata only; plus the
  rational audit `pointwiseBurgess_capacity_deficit` (`879/560 − 624/560 = 51/112 > 0`).
* **§21–§23.**  Conductor-cell data, the router condition, the router compiler
  `conductorCell_routed`, and the exact rational threshold arithmetic
  `router_case_A`, `router_case_B`, `router_case_C`.

Erdős #287 remains OPEN; Balanced7 remains OPEN.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset DirichletCharacter
open scoped BigOperators

namespace Erdos287
namespace V20Router

/-! ## §12. The primitive-conductor large sieve — external, uninhabited -/

/-- **`PrimitiveConductorLargeSieve3221Input`** — `EXTERNAL_ANALYTIC / UNINHABITED`.

The intended external estimate for the primitive-conductor energy of the source family:

`E(R) ≤ logC · (Q/R) · (R² + W5) · ‖c‖₂²`,

taken at high-conductor cutoff `Dcut = log^{B0} X`, with `B0` recorded explicitly as data
so that no later retuning of the cutoff can be hidden.

**This structure is never inhabited in this repository, and the classical multiplicative
large sieve is *not* formalised or axiomatised anywhere.** -/
structure PrimitiveConductorLargeSieve3221Input (Qmod R W5 logC cL2 energy Dcut B0 : ℝ) :
    Prop where
  /-- The dyadic conductor scale is positive. -/
  R_pos : 0 < R
  /-- The five-box scale is positive. -/
  W5_pos : 0 < W5
  /-- The modulus range is positive. -/
  Qmod_pos : 0 < Qmod
  /-- The logarithmic constant is positive. -/
  logC_pos : 0 < logC
  /-- The source `L²` mass is nonnegative. -/
  cL2_nonneg : 0 ≤ cL2
  /-- The conductor cutoff is positive. -/
  Dcut_pos : 0 < Dcut
  /-- The cutoff exponent is positive. -/
  B0_pos : 0 < B0
  /-- **The external analytic estimate.** -/
  energy_bound : energy ≤ logC * (Qmod / R) * (R ^ 2 + W5) * cL2

/-- **`largeSieve_not_automatic`.**  `LEAN_PROVED`.

The large-sieve input is a genuine restriction: explicit parameters refute it, so no
compiler below can be made unconditional. -/
theorem largeSieve_not_automatic :
    ∃ Qmod R W5 logC cL2 energy Dcut B0 : ℝ,
      ¬ PrimitiveConductorLargeSieve3221Input Qmod R W5 logC cL2 energy Dcut B0 := by
  refine ⟨1, 1, 1, 1, 0, 1, 1, 1, ?_⟩
  intro h
  have := h.energy_bound
  norm_num at this

/-! ## §13. The conditional diagonal compiler -/

/-- **`highCondDiagonal_of_largeSieve`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

External primitive-conductor large-sieve input **+** the five-box `L²` source bound **+**
an explicit budget ⇒ the desired diagonal bound, at the explicit cutoff `Dcut = log^{B0} X`.

Nothing here inhabits the analytic input, so the diagonal child stays
`EXTERNAL-ANALYTIC CLOSED / CONDITIONAL COMPILER`. -/
theorem highCondDiagonal_of_largeSieve {Qmod R W5 logC cL2 energy Dcut B0 srcL2 target : ℝ}
    (hin : PrimitiveConductorLargeSieve3221Input Qmod R W5 logC cL2 energy Dcut B0)
    (hsrc : cL2 ≤ srcL2)
    (hbudget : logC * (Qmod / R) * (R ^ 2 + W5) * srcL2 ≤ target) :
    energy ≤ target := by
  have hfac : 0 ≤ logC * (Qmod / R) * (R ^ 2 + W5) := by
    have h1 : 0 < Qmod / R := div_pos hin.Qmod_pos hin.R_pos
    have h2 : 0 < R ^ 2 + W5 := by nlinarith [hin.R_pos, hin.W5_pos]
    positivity
  have hmono : logC * (Qmod / R) * (R ^ 2 + W5) * cL2
      ≤ logC * (Qmod / R) * (R ^ 2 + W5) * srcL2 :=
    mul_le_mul_of_nonneg_left hsrc hfac
  exact le_trans hin.energy_bound (le_trans hmono hbudget)

/-! ## §14. The diagonal exponent ledger -/

/-- The fixed diagonal power room `4/35`. -/
def diagonal_fixed_power_room : ℚ := 4 / 35

/-- **`diagonal_power_room_rational`.**  `PROVED_ALGEBRAIC / METADATA_ONLY`.

`1 − 39/35 = −4/35`, i.e. the fixed diagonal power room is `4/35 > 0`. -/
theorem diagonal_power_room_rational :
    (1 : ℚ) - 39 / 35 = -diagonal_fixed_power_room ∧ (0 : ℚ) < diagonal_fixed_power_room := by
  rw [diagonal_fixed_power_room]
  constructor <;> norm_num

/-- **`diagonal_power_room_rpow`.**  `PROVED_ALGEBRAIC / METADATA_ONLY`.

With `M · W5 = X` (the natural scale) and `M · W5² / Q = X^{39/35}` (the pre-Poisson
density scale), the ratio of the two is exactly `X^{−4/35}`.  This is rational power
arithmetic; **no asymptotic claim is made**. -/
theorem diagonal_power_room_rpow (X M W5 Qmod : ℝ) (hX : 0 < X) (h1 : M * W5 = X)
    (h2 : M * W5 ^ 2 / Qmod = X ^ (39 / 35 : ℝ)) :
    (M * W5) / (M * W5 ^ 2 / Qmod) = X ^ (-(4 / 35) : ℝ) := by
  rw [h1, h2, show (-(4 / 35) : ℝ) = 1 - 39 / 35 by norm_num, Real.rpow_sub hX,
    Real.rpow_one]

/-! ## §15. The finite low-conductor count -/

/-- **`lowConductor_card_le`.**  `LEAN_PROVED_FINITE`.

`#{ξ mod q : cond(ξ) ≤ L} ≤ ∑_{r ∣ q, r ≤ L} φ(r)`.

Each character is the level-`q` lift of its own primitive character, and at a fixed level
that lift is unique, so the fibre above a conductor `r` injects into the characters mod `r`.
**No logarithmic asymptotic is claimed.** -/
theorem lowConductor_card_le (q L : ℕ) [NeZero q] :
    (Finset.univ.filter (fun xi : DirichletCharacter ℂ q => xi.conductor ≤ L)).card
      ≤ ∑ r ∈ q.divisors.filter (fun r => r ≤ L), r.totient := by
  classical
  set S := Finset.univ.filter (fun xi : DirichletCharacter ℂ q => xi.conductor ≤ L) with hS
  set t := q.divisors.filter (fun r => r ≤ L) with ht
  have hmap : Set.MapsTo (fun χ : DirichletCharacter ℂ q => χ.conductor) (↑S) (↑t) := by
    intro χ hχ
    have hχ' : χ ∈ S := by simpa using hχ
    rw [hS] at hχ'
    have h1 : χ.conductor ≤ L := (Finset.mem_filter.mp hχ').2
    simp only [ht, Finset.coe_filter, Set.mem_setOf_eq, Nat.mem_divisors]
    exact ⟨⟨χ.conductor_dvd_level, NeZero.ne q⟩, h1⟩
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  refine Finset.sum_le_sum ?_
  intro r hr
  rw [ht] at hr
  have hrq : r ∣ q := (Nat.mem_divisors.mp (Finset.mem_filter.mp hr).1).1
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact (NeZero.ne q) (Nat.eq_zero_of_zero_dvd hrq)
  haveI : NeZero r := ⟨hr0⟩
  have hsub : S.filter (fun χ => χ.conductor = r)
      ⊆ Finset.image (fun θ : DirichletCharacter ℂ r => DirichletCharacter.changeLevel hrq θ)
          Finset.univ := by
    intro χ hχ
    have h : χ.conductor = r := (Finset.mem_filter.mp hχ).2
    subst h
    exact Finset.mem_image.mpr ⟨χ.primitiveCharacter, Finset.mem_univ _,
      changeLevel_primitiveCharacter χ⟩
  calc (S.filter (fun χ => χ.conductor = r)).card
      ≤ (Finset.image (fun θ : DirichletCharacter ℂ r => DirichletCharacter.changeLevel hrq θ)
          Finset.univ).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (DirichletCharacter ℂ r)).card := Finset.card_image_le
    _ = r.totient := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
          MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity, Nat.card_eq_fintype_card,
          ZMod.card_units_eq_totient]

/-! ## §16. The low-quotient compiler -/

/-- **`lowQuotient_child_le`.**  `LEAN_PROVED_FINITE`.

If the autocorrelation is bounded by `Eq`, the short-`m` Gram by `Mbound`, the twisting
factor by `1` in modulus, and the low-quotient character multiplicity by `lowMult`, then
the low-quotient Gram child is at most `lowMult · (Mbound · Eq)`.

Pure finite algebra: no asymptotic input, no logarithm. -/
theorem lowQuotient_child_le {ι : Type*} (T : Finset ι) (w G A : ι → ℂ)
    (Eq Mbound lowMult : ℝ) (hcard : (T.card : ℝ) ≤ lowMult)
    (hw : ∀ x ∈ T, ‖w x‖ ≤ 1) (hG : ∀ x ∈ T, ‖G x‖ ≤ Mbound) (hA : ∀ x ∈ T, ‖A x‖ ≤ Eq)
    (hM : 0 ≤ Mbound) (hE : 0 ≤ Eq) :
    ‖∑ x ∈ T, w x * G x * A x‖ ≤ lowMult * (Mbound * Eq) := by
  have hterm : ∀ x ∈ T, ‖w x * G x * A x‖ ≤ Mbound * Eq := by
    intro x hx
    rw [norm_mul, norm_mul]
    have h1 := hw x hx
    have h2 := hG x hx
    have h3 := hA x hx
    nlinarith [norm_nonneg (w x), norm_nonneg (G x), norm_nonneg (A x)]
  calc ‖∑ x ∈ T, w x * G x * A x‖ ≤ ∑ x ∈ T, ‖w x * G x * A x‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ T, Mbound * Eq := Finset.sum_le_sum hterm
    _ = (T.card : ℝ) * (Mbound * Eq) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ lowMult * (Mbound * Eq) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hM hE)

/-- **`lowQuotient_child_of_diagonal_budget`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

The low-quotient child is controlled by the multiplicity times the diagonal energy budget:
combining the finite compiler with an explicit budget hypothesis. -/
theorem lowQuotient_child_of_diagonal_budget {ι : Type*} (T : Finset ι) (w G A : ι → ℂ)
    (Eq Mbound lowMult target : ℝ) (hcard : (T.card : ℝ) ≤ lowMult)
    (hw : ∀ x ∈ T, ‖w x‖ ≤ 1) (hG : ∀ x ∈ T, ‖G x‖ ≤ Mbound) (hA : ∀ x ∈ T, ‖A x‖ ≤ Eq)
    (hM : 0 ≤ Mbound) (hE : 0 ≤ Eq) (hbudget : lowMult * (Mbound * Eq) ≤ target) :
    ‖∑ x ∈ T, w x * G x * A x‖ ≤ target :=
  le_trans (lowQuotient_child_le T w G A Eq Mbound lowMult hcard hw hG hA hM hE) hbudget

/-! ## §20. The pointwise Burgess capacity firewall — external metadata only -/

/-- **`PointwiseBurgess3221Input`** — `EXTERNAL_ANALYTIC / UNINHABITED / METADATA_ONLY`.

The intended pointwise character-sum bound in the shape used by the audit.  **Burgess's
theorem is not formalised, assumed or axiomatised anywhere in this repository**, and this
structure is never inhabited. -/
structure PointwiseBurgess3221Input (Mlen Rcond burgessConst delta value : ℝ) : Prop where
  /-- The summation length is positive. -/
  Mlen_pos : 0 < Mlen
  /-- The conductor is positive. -/
  Rcond_pos : 0 < Rcond
  /-- The implied constant is positive. -/
  const_pos : 0 < burgessConst
  /-- The saving exponent is positive. -/
  delta_pos : 0 < delta
  /-- **The external pointwise estimate.** -/
  pointwise_bound : value ≤ burgessConst * Mlen * Rcond ^ (-delta)

/-- The pointwise-Burgess input is not automatic. -/
theorem pointwiseBurgess_not_automatic :
    ∃ Mlen Rcond burgessConst delta value : ℝ,
      ¬ PointwiseBurgess3221Input Mlen Rcond burgessConst delta value := by
  refine ⟨1, 1, 1, 1, 2, ?_⟩
  intro h
  have := h.pointwise_bound
  norm_num at this

/-- **`pointwiseBurgess_capacity_deficit`.**  `PROVED_ALGEBRAIC / METADATA_ONLY`.

The rational arithmetic generated by the audit of the pointwise route:
`879/560 − 624/560 = 51/112 > 0`, i.e. the global pointwise Burgess route is capacity
nonclosing.  **This is arithmetic about the audit's exponents, not a theorem about
Burgess's bound.** -/
theorem pointwiseBurgess_capacity_deficit :
    (879 : ℚ) / 560 - 624 / 560 = 51 / 112 ∧ (0 : ℚ) < 51 / 112 := by
  constructor <;> norm_num

/-! ## §21. Conductor-cell data and the router condition -/

/-- Explicit dyadic conductor-cell metadata: `R1 ~ cond(χ)`, `R2 ~ cond(ψ)`,
`Rxi ~ cond(χ ψ̄)`, together with the five-box scale `W5`, the `m`-length `M` and a
positive margin. -/
structure ConductorCell where
  /-- Dyadic scale of `cond(χ)`. -/
  R1 : ℝ
  /-- Dyadic scale of `cond(ψ)`. -/
  R2 : ℝ
  /-- Dyadic scale of `cond(χ ψ̄)`. -/
  Rxi : ℝ
  /-- The five-box scale. -/
  W5 : ℝ
  /-- The `m`-box length. -/
  Mlen : ℝ
  /-- The routing margin. -/
  margin : ℝ
  /-- Positivity of the first conductor scale. -/
  R1_pos : 0 < R1
  /-- Positivity of the second conductor scale. -/
  R2_pos : 0 < R2
  /-- Positivity of the quotient conductor scale. -/
  Rxi_pos : 0 < Rxi
  /-- Positivity of the five-box scale. -/
  W5_pos : 0 < W5
  /-- Positivity of the `m`-box length. -/
  Mlen_pos : 0 < Mlen
  /-- Positivity of the margin. -/
  margin_pos : 0 < margin

/-- The router condition, in the exact form used by the audit:
`√((R1²+W5)(R2²+W5)) ≤ W5 · √M · Rxi^{−3/16} · margin`. -/
def RouterCondition (cell : ConductorCell) : Prop :=
  Real.sqrt ((cell.R1 ^ 2 + cell.W5) * (cell.R2 ^ 2 + cell.W5))
    ≤ cell.W5 * Real.sqrt cell.Mlen * cell.Rxi ^ (-(3 / 16) : ℝ) * cell.margin

/-! ## §22. The conditional router compiler -/

/-- **`LargeSieveConductorFactor3221Input`** — `EXTERNAL_ANALYTIC / UNINHABITED`.

The `χ`-side factor bound `‖X‖ ≤ √(R² + W5) · base` intended to come from the
primitive-conductor large sieve.  Never inhabited here. -/
structure LargeSieveConductorFactor3221Input (R W5 base : ℝ) (X : ℂ) : Prop where
  /-- The conductor scale is positive. -/
  R_pos : 0 < R
  /-- The five-box scale is positive. -/
  W5_pos : 0 < W5
  /-- The base factor is nonnegative. -/
  base_nonneg : 0 ≤ base
  /-- **The external factor bound.** -/
  factor_bound : ‖X‖ ≤ Real.sqrt (R ^ 2 + W5) * base

/-- **`BurgessConductorFactor3221Input`** — `EXTERNAL_ANALYTIC / UNINHABITED`.

The `ψ`-side factor bound `‖Y‖ ≤ √(R² + W5) · base` intended to come from the pointwise
Burgess estimate.  Never inhabited here. -/
structure BurgessConductorFactor3221Input (R W5 base : ℝ) (Y : ℂ) : Prop where
  /-- The conductor scale is positive. -/
  R_pos : 0 < R
  /-- The five-box scale is positive. -/
  W5_pos : 0 < W5
  /-- The base factor is nonnegative. -/
  base_nonneg : 0 ≤ base
  /-- **The external factor bound.** -/
  factor_bound : ‖Y‖ ≤ Real.sqrt (R ^ 2 + W5) * base

/-- **`conductorCell_routed`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

External large-sieve factor input **+** external Burgess factor input **+** the router
condition ⇒ the conductor cell is power closed:

`‖X · Y‖ ≤ (W5 · √M · Rxi^{−3/16} · margin) · (base₁ base₂)`.

Neither external input is inhabited, so this compiler concludes nothing unconditionally. -/
theorem conductorCell_routed (cell : ConductorCell) {base1 base2 : ℝ} {X Y : ℂ}
    (hLS : LargeSieveConductorFactor3221Input cell.R1 cell.W5 base1 X)
    (hBu : BurgessConductorFactor3221Input cell.R2 cell.W5 base2 Y)
    (hrouter : RouterCondition cell) :
    ‖X * Y‖
      ≤ (cell.W5 * Real.sqrt cell.Mlen * cell.Rxi ^ (-(3 / 16) : ℝ) * cell.margin) *
        (base1 * base2) := by
  have h1 : (0 : ℝ) ≤ Real.sqrt (cell.R1 ^ 2 + cell.W5) := Real.sqrt_nonneg _
  have h2 : (0 : ℝ) ≤ Real.sqrt (cell.R2 ^ 2 + cell.W5) := Real.sqrt_nonneg _
  have hstep : ‖X * Y‖
      ≤ (Real.sqrt (cell.R1 ^ 2 + cell.W5) * base1) *
        (Real.sqrt (cell.R2 ^ 2 + cell.W5) * base2) := by
    rw [norm_mul]
    exact mul_le_mul hLS.factor_bound hBu.factor_bound (norm_nonneg _)
      (mul_nonneg h1 hLS.base_nonneg)
  have hsqrt : Real.sqrt (cell.R1 ^ 2 + cell.W5) * Real.sqrt (cell.R2 ^ 2 + cell.W5)
      = Real.sqrt ((cell.R1 ^ 2 + cell.W5) * (cell.R2 ^ 2 + cell.W5)) :=
    (Real.sqrt_mul (by nlinarith [cell.R1_pos, cell.W5_pos]) _).symm
  have hbb : 0 ≤ base1 * base2 := mul_nonneg hLS.base_nonneg hBu.base_nonneg
  calc ‖X * Y‖ ≤ (Real.sqrt (cell.R1 ^ 2 + cell.W5) * base1) *
        (Real.sqrt (cell.R2 ^ 2 + cell.W5) * base2) := hstep
    _ = Real.sqrt ((cell.R1 ^ 2 + cell.W5) * (cell.R2 ^ 2 + cell.W5)) * (base1 * base2) := by
        rw [← hsqrt]; ring
    _ ≤ (cell.W5 * Real.sqrt cell.Mlen * cell.Rxi ^ (-(3 / 16) : ℝ) * cell.margin) *
        (base1 * base2) := mul_le_mul_of_nonneg_right hrouter hbb

/-! ## §23. The exact rational router arithmetic -/

/-- The routed region for a conductor pair, in exponent form: the product of the two
conductors is at most `X^{417/560 − ε}`. -/
def RoutedExponentPair (e1 e2 eps : ℚ) : Prop := e1 + e2 ≤ 417 / 560 - eps

instance decidableRoutedExponentPair (e1 e2 eps : ℚ) :
    Decidable (RoutedExponentPair e1 e2 eps) := by
  unfold RoutedExponentPair
  infer_instance

/-- **`router_case_A`.**  `PROVED_ALGEBRAIC`.

Both conductors at most `X^{5/14}` ⇒ routed, for every margin `ε ≤ 17/560`. -/
theorem router_case_A {e1 e2 eps : ℚ} (h1 : e1 ≤ 5 / 14) (h2 : e2 ≤ 5 / 14)
    (heps : eps ≤ 17 / 560) : RoutedExponentPair e1 e2 eps := by
  rw [RoutedExponentPair]
  linarith

/-- **`router_case_B`.**  `PROVED_ALGEBRAIC`.

One conductor at most `X^{5/14}`, the other at most `X^{31/80 − ε}` ⇒ routed, with the
explicit margin `ε`.  Note `5/14 + 31/80 = 417/560` exactly. -/
theorem router_case_B {e1 e2 eps : ℚ} (h1 : e1 ≤ 5 / 14) (h2 : e2 ≤ 31 / 80 - eps) :
    RoutedExponentPair e1 e2 eps := by
  rw [RoutedExponentPair]
  linarith

/-- **`router_case_C`.**  `PROVED_ALGEBRAIC`.

Both conductors larger than `X^{5/14}`, but with product at most `X^{417/560 − ε}`
⇒ routed. -/
theorem router_case_C {e1 e2 eps : ℚ} (h : e1 + e2 ≤ 417 / 560 - eps) :
    RoutedExponentPair e1 e2 eps := h

/-- The exact rational identity behind case B: `5/14 + 31/80 = 417/560`. -/
theorem router_threshold_identity : (5 : ℚ) / 14 + 31 / 80 = 417 / 560 := by norm_num

/-- Case A really has positive slack: `2 · 5/14 = 400/560 < 417/560`. -/
theorem router_case_A_slack : (2 : ℚ) * (5 / 14) = 400 / 560 ∧ (400 : ℚ) / 560 < 417 / 560 := by
  constructor <;> norm_num

end V20Router
end Erdos287
