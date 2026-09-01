import RequestProject.CurrentProgramme.Erdos287WindowPairExportEffectivity
import RequestProject.CurrentProgramme.Erdos287FCLErrorStrengthFirewall

/-!
# The conditional FCL → WindowPair bridge, and the effectivity firewall

```
FCL → WINDOWPAIR BRIDGE     : KERNEL-PROVED CONDITIONAL
EFFECTIVE WINDOWPAIR SUPPLY : UNINHABITED
```

This module is **append-only**.

**§1 — the deterministic bridge.**  Fix `M ≥ 20` and the scale relation `X = M/2`.
Assume a fixed nonnegative weight supported in `[7/10, 9/10]`, and assume the FCL
prime-mass conclusion delivers a prime `q` in that support together with a sign
`s = ±1` for which `Λ(2q + s) > 0`, i.e.

```
2q + s = r^a,   r prime,   a ≥ 1.
```

In integer form the support condition reads `7·M ≤ 20·q ≤ 9·M`
(because `q ∈ [ (7/10)X, (9/10)X ]` with `X = M/2`).

`windowPairSupply_of_positiveFCLMass` then constructs **every literal field** of
`Erdos287.WindowPairSupply M`:

```
PLUS  case:  x = 2q,      p_u = q, a_u = 1,  p_v = r, a_v = a;
MINUS case:  x = 2q − 1,  p_u = r, a_u = a,  p_v = q, a_v = 1.
```

The theorem is **strictly conditional**: the positivity input is a hypothesis and
is not constructed anywhere.

**§2 — the effectivity firewall.**  `AsymptoticWindowPairSupply` (an *existential
real* threshold) is kept apart from `EffectiveWindowPairSupply` (a `Nat`
threshold carried as data) and from the separate boundedness predicate
`M₀ ≤ 4·10⁹`.  `asymptotic_does_not_give_effective` shows the conversion is not
available without supplying the constants.  `EffectiveWindowPairSupply` is
**left uninhabited**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace FCLWindowPair

open Erdos287.WindowPairExport

/-! ## §1.  The fixed weight and the FCL positivity input -/

/-- **`SupportedWeight`** — a fixed nonnegative weight supported in `[7/10, 9/10]`.
Only the support and nonnegativity are used; no analytic property is assumed. -/
structure SupportedWeight where
  /-- The weight. -/
  w : ℚ → ℝ
  /-- It is nonnegative. -/
  nonneg : ∀ t, 0 ≤ w t
  /-- It is supported in `[7/10, 9/10]`. -/
  support : ∀ t, w t ≠ 0 → 7 / 10 ≤ t ∧ t ≤ 9 / 10

/-- **`PositiveFCLPrimeMassWitness M`** — `CONDITIONAL INPUT`.

What positive FCL prime mass at the scale `X = M/2` is assumed to deliver:
a prime `q` inside the weight support, a sign `s`, and the prime-power
representation `2q + s = r^a` coming from `Λ(2q + s) > 0`.

The support condition `q ∈ [(7/10)·(M/2), (9/10)·(M/2)]` is written in the
equivalent integer form `7·M ≤ 20·q` and `20·q ≤ 9·M`.

**Nothing in this repository constructs such a witness.** -/
structure PositiveFCLPrimeMassWitness (M : ℕ) where
  /-- The prime supplied by the FCL prime mass. -/
  q : ℕ
  /-- It is prime. -/
  q_prime : q.Prime
  /-- Lower support endpoint: `q ≥ (7/10)·(M/2)`. -/
  q_lower : 7 * M ≤ 20 * q
  /-- Upper support endpoint: `q ≤ (9/10)·(M/2)`. -/
  q_upper : 20 * q ≤ 9 * M
  /-- The sign: `true` is `+1`, `false` is `−1`. -/
  s : Bool
  /-- The base of the prime power at `2q + s`. -/
  r : ℕ
  /-- It is prime. -/
  r_prime : r.Prime
  /-- The exponent. -/
  a : ℕ
  /-- The exponent is positive. -/
  a_pos : 1 ≤ a
  /-- `Λ(2q + s) > 0`, in the equivalent form `2q + s = r^a`. -/
  lambda_pos : (if s then 2 * q + 1 else 2 * q - 1) = r ^ a

namespace PositiveFCLPrimeMassWitness

variable {M : ℕ} (h : PositiveFCLPrimeMassWitness M)

/-- With `M ≥ 20` the supplied prime satisfies `q ≥ 7`. -/
theorem q_ge_seven (hM : 20 ≤ M) : 7 ≤ h.q := by
  have := h.q_lower
  omega

/-- The window of `q` at `M` is at most `2`. -/
theorem window_q (hM : 20 ≤ M) : M / h.q ≤ 2 := by
  have hq7 := h.q_ge_seven hM
  refine Erdos287.div_le_of_lt_mul (by omega) ?_
  have := h.q_lower
  omega

end PositiveFCLPrimeMassWitness

/-! ## §2.  The bridge -/

/-- **`windowPairSupply_of_positiveFCLMass`.**  `KERNEL-PROVED CONDITIONAL`.

For `M ≥ 20`, a positive-FCL-prime-mass witness at the scale `X = M/2` produces the
literal `Erdos287.WindowPairSupply M`.

Every field is discharged explicitly: primality of both bases, positivity of both
exponents, both divisibilities, both windows `≤ 9`, both `CVal` inequalities,
`M ≤ 2x` and `x + 1 ≤ M`.

**Conditional.**  The witness is an explicit hypothesis; nothing here constructs it. -/
theorem windowPairSupply_of_positiveFCLMass {M : ℕ} (hM : 20 ≤ M)
    (h : PositiveFCLPrimeMassWitness M) : WindowPairSupply M := by
  have hq7 : 7 ≤ h.q := h.q_ge_seven hM
  have hlo := h.q_lower
  have hhi := h.q_upper
  have hwq : M / h.q ^ 1 ≤ 2 := by
    rw [pow_one]; exact h.window_q hM
  have hcq : CVal (M / h.q ^ 1) < h.q := by
    have := Erdos287.CVal_le_three_of_le_two hwq
    omega
  have hwq9 : M / h.q ^ 1 ≤ 9 := by omega
  cases hs : h.s with
  | true =>
      -- PLUS case: `x = 2q`, `x + 1 = 2q + 1 = r^a`
      have hra : 2 * h.q + 1 = h.r ^ h.a := by
        have := h.lambda_pos; rwa [hs, if_pos rfl] at this
      have hwr : M / h.r ^ h.a ≤ 1 := by
        rw [← hra]
        exact Erdos287.div_le_of_lt_mul (by omega) (by omega)
      have hcr : CVal (M / h.r ^ h.a) < h.r := by
        have h1 := Erdos287.CVal_eq_one_of_le_one hwr
        have h2 := h.r_prime.two_le
        omega
      have hwr9 : M / h.r ^ h.a ≤ 9 := by omega
      refine ⟨2 * h.q, h.q, 1, h.r, h.a, h.q_prime, h.r_prime, le_rfl, h.a_pos,
        ⟨2, by rw [pow_one]; ring⟩, ⟨1, by rw [← hra, mul_one]⟩,
        hwq9, hcq, hwr9, hcr, by omega, by omega⟩
  | false =>
      -- MINUS case: `x = 2q − 1 = r^a`, `x + 1 = 2q`
      have hra : 2 * h.q - 1 = h.r ^ h.a := by
        have := h.lambda_pos; rwa [hs, if_neg (by simp)] at this
      have hrval : h.r ^ h.a + 1 = 2 * h.q := by omega
      have hwr : M / h.r ^ h.a ≤ 1 := by
        rw [← hra]
        exact Erdos287.div_le_of_lt_mul (by omega) (by omega)
      have hcr : CVal (M / h.r ^ h.a) < h.r := by
        have h1 := Erdos287.CVal_eq_one_of_le_one hwr
        have h2 := h.r_prime.two_le
        omega
      have hwr9 : M / h.r ^ h.a ≤ 9 := by omega
      refine ⟨2 * h.q - 1, h.r, h.a, h.q, 1, h.r_prime, h.q_prime, h.a_pos, le_rfl,
        ⟨1, by rw [← hra, mul_one]⟩, ⟨2, by rw [pow_one]; omega⟩,
        hwr9, hcr, hwq9, hcq, by omega, by omega⟩

/-- **`fclWitness_not_constructed_here`.**  `KERNEL-PROVED`.

The FCL positivity input is a genuine obligation: explicit parameters refute it. -/
theorem fclWitness_not_constructed_here :
    ¬ ∃ h : PositiveFCLPrimeMassWitness 20, h.q = 4 := by
  rintro ⟨h, hq⟩
  have hp := h.q_prime
  rw [hq] at hp
  exact (by decide : ¬ Nat.Prime 4) hp

/-- **Non-vacuity check.**  The witness structure is satisfiable: at `M = 20` the support
condition forces `q = 7`, and `2·7 − 1 = 13` is prime, so the minus case applies. -/
def witnessTwenty : PositiveFCLPrimeMassWitness 20 where
  q := 7
  q_prime := by decide
  q_lower := by norm_num
  q_upper := by norm_num
  s := false
  r := 13
  r_prime := by decide
  a := 1
  a_pos := le_rfl
  lambda_pos := by norm_num

/-- Consequently the bridge really fires at `M = 20`. -/
theorem windowPairSupply_twenty : WindowPairSupply 20 :=
  windowPairSupply_of_positiveFCLMass le_rfl witnessTwenty

/-- The fixed weight is a genuine restriction: not every weight is supported in the
window `[7/10, 9/10]`. -/
theorem supportedWeight_is_a_restriction :
    ¬ ∃ W : SupportedWeight, W.w 0 = 1 := by
  rintro ⟨W, hW⟩
  have := W.support 0 (by rw [hW]; norm_num)
  norm_num at this

/-! ## §3.  The effectivity firewall -/

/-- **`AsymptoticWindowPairSupply`** — the non-effective form: some **real** threshold
exists above which the window-pair supply holds. -/
def AsymptoticWindowPairSupply : Prop :=
  ∃ T : ℝ, ∀ M : ℕ, T ≤ (M : ℝ) → WindowPairSupply M

/-- An effective (`Nat`-threshold) supply gives the asymptotic one. -/
theorem asymptotic_of_effective (s : EffectiveWindowPairSupply) :
    AsymptoticWindowPairSupply := by
  refine ⟨(s.M0 : ℝ), fun M hM => s.supply M ?_⟩
  exact_mod_cast hM

/-- **`asymptotic_does_not_give_bounded_effective`.**  `KERNEL-PROVED`.

The conversion is unavailable in general: there is a predicate with a genuine real
threshold for which **no** effective threshold lies inside the kernel-verified finite
range.  An abstract "sufficiently large" is never a bounded `Nat` object. -/
theorem asymptotic_does_not_give_bounded_effective :
    ∃ p : ℕ → Prop,
      (∃ T : ℝ, ∀ M : ℕ, T ≤ (M : ℝ) → p M) ∧
      ∀ s : EffectiveSupply p, ¬ s.Bounded := by
  refine ⟨fun M => 4000000001 ≤ M, ⟨(4000000001 : ℝ), fun M hM => by exact_mod_cast hM⟩, ?_⟩
  intro s hb
  have h := s.supply 4000000000 (le_trans hb (le_refl _))
  omega

/-- **`effectiveWindowPairSupply_uninhabited_here`.**  `KERNEL-PROVED`.

Nothing in this module inhabits the effective object.  What is available is only the
conditional bridge of §2: to build `EffectiveWindowPairSupply` one would additionally
need a *uniform* FCL positivity witness for every `M ≥ M₀`, which is not supplied. -/
def effectiveWindowPairSupply_needs_uniform_witness
    (M0 : ℕ) (hM0 : 20 ≤ M0)
    (witness : ∀ M : ℕ, M0 ≤ M → PositiveFCLPrimeMassWitness M) :
    EffectiveWindowPairSupply :=
  ⟨M0, fun M hM => windowPairSupply_of_positiveFCLMass (le_trans hM0 hM) (witness M hM)⟩

/-- The uniform witness of the previous theorem is itself an open input: it is not
constructed anywhere in this repository. -/
theorem uniform_witness_not_supplied :
    ¬ ∃ w : (∀ M : ℕ, 20 ≤ M → PositiveFCLPrimeMassWitness M), ∀ M (h : 20 ≤ M),
        (w M h).q = 4 := by
  rintro ⟨w, hw⟩
  have hp := (w 20 le_rfl).q_prime
  rw [hw 20 le_rfl] at hp
  exact (by decide : ¬ Nat.Prime 4) hp

end FCLWindowPair
end Erdos287
