import Mathlib
import RequestProject.CurrentProgramme.PrimeTupleMultiplicity

/-!
# CurrentProgramme (post-Balanced7 pass) §5 — the conductor-split multiplicative large sieve

This module is **exact finite algebra only**.  It contains no large-sieve inequality and no
prime-density input.

A *character family* is a finite labelled family of arithmetic functions `χ_l : ℕ → ℂ`
together with a declared primitive conductor `cond l`.  The family is supplied as data: no
`Fintype (DirichletCharacter ℂ q)` instance is used, so nothing here depends on the ambient
character API and nothing is silently assumed about completeness of the family.

Banked (all `LEAN_PROVED`):

* `charSum`, the literal finite character sum `∑_{n < N} c n · χ_l n`;
* `condSum F D N c`, the literal finite conductor-restricted `L²` mass;
* nonnegativity `condSum_nonneg`;
* the **exact conductor split** `condSum_add_highCondSum` (low conductor `f ≤ D` plus high
  conductor `f > D` reassembles the full mass, with no double counting);
* monotonicity in the conductor cutoff, and domination by the full mass;
* the Möbius expansion of the coprimality indicator (`sum_moebius_divisors`,
  `coprime_indicator_eq`), which is the step that produces the `q/φ(q)` bookkeeping.

The research estimate

```
    ∑_{q ≤ Q} (q/φ(q)) ∑*_{χ mod q} |∑_{n ≤ N} c n χ(n)|²  ≪  log^16 X · (Q + N/D) · ∑ |c|²
```

is **not** proved here.  It is represented by the uninhabited socket
`BalancedSevenAllCharacterConductorLargeSieveInput`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace PostBalanced7Pro

/-! ## §5.1  Character families as supplied finite data -/

/-- A finite labelled family of arithmetic functions with declared primitive conductors.

Nothing is assumed about the functions `chi`: in the intended instantiation `chi l` is a
Dirichlet character modulo `modulus` induced by a primitive character of conductor `cond l`,
but the finite algebra below is independent of that. -/
structure CharacterFamily where
  /-- The common modulus of the family. -/
  modulus : ℕ
  /-- The finite label set. -/
  labels : Finset ℕ
  /-- The character values, indexed by label. -/
  chi : ℕ → ℕ → ℂ
  /-- The declared primitive conductor of each label. -/
  cond : ℕ → ℕ

/-- The literal finite character sum `∑_{n < N} c n · χ_l(n)`. -/
noncomputable def charSum (F : CharacterFamily) (l N : ℕ) (c : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, c n * F.chi l n

/-- The literal finite `L²` mass over the labels of conductor at most `D`. -/
noncomputable def condSum (F : CharacterFamily) (D N : ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑ l ∈ F.labels.filter (fun l => F.cond l ≤ D), ‖charSum F l N c‖ ^ 2

/-- The literal finite `L²` mass over the labels of conductor exceeding `D`. -/
noncomputable def highCondSum (F : CharacterFamily) (D N : ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑ l ∈ F.labels.filter (fun l => ¬ F.cond l ≤ D), ‖charSum F l N c‖ ^ 2

/-- The literal finite `L²` mass over the whole family. -/
noncomputable def fullCondSum (F : CharacterFamily) (N : ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑ l ∈ F.labels, ‖charSum F l N c‖ ^ 2

/-! ## §5.2  Exact rearrangements -/

/-- **`condSum_nonneg`.**  `LEAN_PROVED`.  Each conductor-restricted mass is nonnegative. -/
theorem condSum_nonneg (F : CharacterFamily) (D N : ℕ) (c : ℕ → ℂ) :
    0 ≤ condSum F D N c :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **`highCondSum_nonneg`.**  `LEAN_PROVED`. -/
theorem highCondSum_nonneg (F : CharacterFamily) (D N : ℕ) (c : ℕ → ℂ) :
    0 ≤ highCondSum F D N c :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **`fullCondSum_nonneg`.**  `LEAN_PROVED`. -/
theorem fullCondSum_nonneg (F : CharacterFamily) (N : ℕ) (c : ℕ → ℂ) :
    0 ≤ fullCondSum F N c :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **`condSum_add_highCondSum`.**  `LEAN_PROVED`.

The **exact conductor split**: the low-conductor part and the high-conductor part reassemble
the full mass.  Every label is owned by exactly one side, so the split neither loses nor
double counts any character. -/
theorem condSum_add_highCondSum (F : CharacterFamily) (D N : ℕ) (c : ℕ → ℂ) :
    condSum F D N c + highCondSum F D N c = fullCondSum F N c :=
  Finset.sum_filter_add_sum_filter_not _ _ _

/-- **`condSplit_disjoint`.**  `LEAN_PROVED`.  The two conductor sectors are disjoint. -/
theorem condSplit_disjoint (F : CharacterFamily) (D : ℕ) :
    Disjoint (F.labels.filter (fun l => F.cond l ≤ D))
      (F.labels.filter (fun l => ¬ F.cond l ≤ D)) :=
  Finset.disjoint_filter_filter_not _ _ _

/-- **`condSum_le_fullCondSum`.**  `LEAN_PROVED`. -/
theorem condSum_le_fullCondSum (F : CharacterFamily) (D N : ℕ) (c : ℕ → ℂ) :
    condSum F D N c ≤ fullCondSum F N c := by
  have h := condSum_add_highCondSum F D N c
  have h2 := highCondSum_nonneg F D N c
  linarith

/-- **`condSum_mono`.**  `LEAN_PROVED`.  Raising the conductor cutoff can only increase the
low-conductor mass. -/
theorem condSum_mono (F : CharacterFamily) {D₁ D₂ : ℕ} (h : D₁ ≤ D₂) (N : ℕ) (c : ℕ → ℂ) :
    condSum F D₁ N c ≤ condSum F D₂ N c := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)
  intro l hl
  simp only [Finset.mem_filter] at hl ⊢
  exact ⟨hl.1, le_trans hl.2 h⟩

/-- **`charSum_zero_coeff`.**  `LEAN_PROVED`.  A sanity check on the literal definition. -/
theorem charSum_zero_coeff (F : CharacterFamily) (l N : ℕ) :
    charSum F l N (fun _ => 0) = 0 := by
  simp [charSum]

/-- **`fullCondSum_eq_zero_of_zero_coeff`.**  `LEAN_PROVED`. -/
theorem fullCondSum_eq_zero_of_zero_coeff (F : CharacterFamily) (N : ℕ) :
    fullCondSum F N (fun _ => 0) = 0 := by
  simp [fullCondSum, charSum]

/-! ## §5.3  The Möbius expansion of the coprimality indicator -/

open ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

/-- **`sum_moebius_divisors`.**  `LEAN_PROVED`.  `∑_{d ∣ n} μ(d) = [n = 1]`. -/
theorem sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, moebius d = if n = 1 then 1 else 0 := by
  have h : ((moebius * ζ : ArithmeticFunction ℤ)) n = (1 : ArithmeticFunction ℤ) n := by
    rw [moebius_mul_coe_zeta]
  rw [coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

/-- **`coprime_indicator_eq`.**  `LEAN_PROVED`.

The coprimality indicator of `(a, b)` is the Möbius sum over the common divisors, i.e. over
the divisors of `gcd a b`.  This is the exact step that introduces the divisor bookkeeping
whose cost is tracked as `q/φ(q)`. -/
theorem coprime_indicator_eq (a b : ℕ) :
    ∑ d ∈ (Nat.gcd a b).divisors, moebius d = if Nat.Coprime a b then 1 else 0 := by
  rw [sum_moebius_divisors]

/-- **`gcd_divisors_nonempty`.**  `LEAN_PROVED`.  For `a > 0` the Möbius sum of the
coprimality expansion runs over a nonempty divisor set. -/
theorem gcd_divisors_nonempty {a b : ℕ} (h : 0 < a) : (Nat.gcd a b).divisors.Nonempty := by
  refine ⟨1, ?_⟩
  have hg : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left h.ne'
  simp [Nat.mem_divisors, hg]

/-! ## §5.4  The analytic source socket (uninhabited) -/

/-- **`BalancedSevenAllCharacterConductorLargeSieveInput`** —
`EXTERNAL / ANALYTIC / SOURCE OPEN / UNINHABITED`.

The literal obligations of the conductor-split multiplicative large sieve used by the
replacement SmallQ provider.  The fields record exactly what the source has to supply:

* the polylogarithmic loss exponent (research value `16`);
* the low-conductor mass bound in terms of the coefficient energy;
* the high-conductor mass bound with the `N / D` gain;
* the requirement that the split reassembles the physical mass.

This structure is **not inhabited** anywhere in the repository. -/
structure BalancedSevenAllCharacterConductorLargeSieveInput
    (F : CharacterFamily) (Q D N polylogExponent : ℕ) (c : ℕ → ℂ) (energy X : ℝ) : Prop where
  /-- The scales are nontrivial. -/
  scale : 3 ≤ X ∧ 0 < D ∧ 0 < N
  /-- The declared coefficient energy really dominates the `ℓ²` norm of `c`. -/
  energy_dominates : ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 ≤ energy
  /-- The research value of the polylogarithmic loss exponent. -/
  polylog_exponent_value : polylogExponent = 16
  /-- The low-conductor mass obeys the large-sieve bound. -/
  low_conductor_bound :
    condSum F D N c ≤ (Real.log X) ^ polylogExponent * ((Q : ℝ) + N) * energy
  /-- The high-conductor mass obeys the sharpened bound with the `N / D` gain. -/
  high_conductor_bound :
    highCondSum F D N c ≤ (Real.log X) ^ polylogExponent * ((Q : ℝ) + (N : ℝ) / D) * energy
  /-- The two sectors reassemble the physical mass (no double spending of characters). -/
  reassembly : condSum F D N c + highCondSum F D N c = fullCondSum F N c

/-- **`conductorLargeSieve_full_bound`.**  `LEAN_PROVED` *conditionally on the socket*.

Given the socket, the full character mass obeys the sum of the two sector bounds.  This is a
pure consequence of the exact reassembly identity; it is **not** an analytic theorem. -/
theorem conductorLargeSieve_full_bound
    {F : CharacterFamily} {Q D N polylogExponent : ℕ} {c : ℕ → ℂ} {energy X : ℝ}
    (h : BalancedSevenAllCharacterConductorLargeSieveInput F Q D N polylogExponent c energy X) :
    fullCondSum F N c ≤
      (Real.log X) ^ polylogExponent * ((Q : ℝ) + N) * energy +
      (Real.log X) ^ polylogExponent * ((Q : ℝ) + (N : ℝ) / D) * energy := by
  rw [← h.reassembly]
  exact add_le_add h.low_conductor_bound h.high_conductor_bound

/-- **`conductorLargeSieve_not_automatic`.**  `LEAN_PROVED`.

The socket is a genuine restriction: it is not inhabited by the finite algebra of this
module. -/
theorem conductorLargeSieve_not_automatic :
    ∃ (F : CharacterFamily) (Q D N polylogExponent : ℕ) (c : ℕ → ℂ) (energy X : ℝ),
      ¬ BalancedSevenAllCharacterConductorLargeSieveInput F Q D N polylogExponent c energy X := by
  refine ⟨⟨1, ∅, fun _ _ => 0, fun _ => 0⟩, 0, 1, 1, 16, (fun _ => 1), -1, 3, ?_⟩
  intro h
  have h2 : ∑ n ∈ Finset.range 1, ‖(1 : ℂ)‖ ^ 2 ≤ (-1 : ℝ) := h.energy_dominates
  simp at h2
  linarith

end PostBalanced7Pro
end Erdos287
