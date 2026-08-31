import Mathlib
import RequestProject.CurrentProgramme.PrimitiveRamanujanReassembly

/-!
# Short-lift local profile — Erdős #287, PRIMITIVE-LOCALPROFILE Δ, §C

**Algebra only.**  The local profile

```
mProfile(g,b,D) = ∑_{gcd(d, 2bg) = 1} μ(d)/d · Ψ(d/D)
```

is formalised in its finite / dyadic form (`mProfile`), consistent with the repository's
finite-sum infrastructure, together with the *sharp-cutoff* and *divisor-restricted*
variants.

What is proved here is exactly the Euler-product algebra that is available formally, at the
**finite prime-product level**:

```
∑_{d ∣ n, gcd(d,H) = 1} μ(d)/d  =  ∏_{p ∣ n, p ∤ H} (1 - 1/p)
                                =  (∏_{p ∣ n} (1 - 1/p)) · ∏_{p ∣ n, p ∣ H} (1 - 1/p)⁻¹,
```

for squarefree `n` (`mProfileDivisor_euler_product`, `shortLift_euler_collapse_finite`).
The second display is the finite-prime-product avatar of `H_H(w) / ζ(1+w)`: the first factor
is the finite surrogate of `1/ζ`, the second is the finite surrogate of `H_H`.

The genuine analytic Dirichlet-series statement is **not** proved: it is recorded as the
**uninhabited** interface `ShortLiftEulerAnalyticInput`, whose only use is the trivial
conditional consumer `shortLift_euler_collapse_of_input`.

No claim of the shape `exp(-c √(log D))`, and no arbitrary-log cancellation, is formalised
anywhere in this file.

Research status: `DET1-SHORTLIFT-EULER-COLLAPSE45 : RESEARCH PASS CANDIDATE; ANALYTIC /
UNINHABITED; NANC PROMOTION AUDIT PENDING.`
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators
open ArithmeticFunction

namespace Erdos287
namespace ShortLift

/-! ## §C.1  The finite / dyadic local profile -/

/-- The finite (dyadic) local profile

```
mProfile g b D Ψ T = ∑_{1 ≤ d ≤ T, gcd(d, 2bg) = 1} μ(d)/d · Ψ(d/D),
```

with `T` the explicit truncation length and `Ψ` an explicit rational weight. -/
def mProfile (g b D : ℕ) (Psi : ℚ → ℚ) (T : ℕ) : ℚ :=
  ∑ d ∈ Finset.Icc 1 T,
    if Nat.Coprime d (2 * b * g) then (moebius d : ℚ) / d * Psi ((d : ℚ) / D) else 0

/-- The sharp-cutoff profile: `Ψ = 1_{(0,1]}` and `T = D`. -/
def mProfileSharp (g b D : ℕ) : ℚ :=
  mProfile g b D (fun x => if 0 < x ∧ x ≤ 1 then 1 else 0) D

/-- The profile is additive in the weight `Ψ`. -/
theorem mProfile_add (g b D : ℕ) (Psi Phi : ℚ → ℚ) (T : ℕ) :
    mProfile g b D (fun x => Psi x + Phi x) T
      = mProfile g b D Psi T + mProfile g b D Phi T := by
  unfold mProfile
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro d _
  split_ifs with h <;> ring

/-- The profile is homogeneous in the weight `Ψ`. -/
theorem mProfile_smul (g b D : ℕ) (c : ℚ) (Psi : ℚ → ℚ) (T : ℕ) :
    mProfile g b D (fun x => c * Psi x) T = c * mProfile g b D Psi T := by
  unfold mProfile
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro d _
  split_ifs with h <;> ring

/-- The zero weight gives the zero profile. -/
@[simp] theorem mProfile_zero_weight (g b D T : ℕ) :
    mProfile g b D (fun _ => 0) T = 0 := by
  simp [mProfile]

/-! ## §C.2  Divisor-restricted profile and the finite Euler product -/

/-- The multiplicative weight `d ↦ 1_{gcd(d,H)=1} / d`. -/
def coprimeInvWeight (H : ℕ) : ArithmeticFunction ℚ where
  toFun d := if Nat.Coprime d H then (1 : ℚ) / d else 0
  map_zero' := by simp

@[simp] theorem coprimeInvWeight_apply (H d : ℕ) :
    coprimeInvWeight H d = if Nat.Coprime d H then (1 : ℚ) / d else 0 := rfl

theorem isMultiplicative_coprimeInvWeight (H : ℕ) :
    (coprimeInvWeight H).IsMultiplicative := by
  constructor
  · show (if Nat.Coprime 1 H then (1 : ℚ) / (1 : ℕ) else 0) = 1
    simp
  · intro m n hmn
    simp only [coprimeInvWeight_apply, Nat.coprime_mul_iff_left]
    by_cases hm : Nat.Coprime m H
    · by_cases hn : Nat.Coprime n H
      · rw [if_pos ⟨hm, hn⟩, if_pos hm, if_pos hn]
        push_cast
        rw [one_div, one_div, one_div, mul_inv]
      · simp [hn]
    · simp [hm]

/-- The divisor-restricted local profile `∑_{d ∣ n, gcd(d,H)=1} μ(d)/d`. -/
def mProfileDivisor (H n : ℕ) : ℚ :=
  ∑ d ∈ n.divisors, if Nat.Coprime d H then (moebius d : ℚ) / d else 0

/-- **Finite Euler product, `LEAN_PROVED`.**

For squarefree `n`,

```
∑_{d ∣ n, gcd(d,H)=1} μ(d)/d = ∏_{p ∣ n, p ∤ H} (1 - 1/p).
```
-/
theorem mProfileDivisor_euler_product {n : ℕ} (hn : Squarefree n) (H : ℕ) :
    mProfileDivisor H n
      = ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ H), (1 - (1 : ℚ) / p) := by
  have hkey := (isMultiplicative_coprimeInvWeight H).prodPrimeFactors_one_sub_of_squarefree
    (f := coprimeInvWeight H) hn
  have hleft : ∏ p ∈ n.primeFactors, (1 - coprimeInvWeight H p)
      = ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ H), (1 - (1 : ℚ) / p) := by
    rw [← Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => ¬ p ∣ H)]
    have h1 : ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ H), (1 - coprimeInvWeight H p)
        = ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ H), (1 - (1 : ℚ) / p) := by
      refine Finset.prod_congr rfl ?_
      intro p hp
      rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
      have hprime : p.Prime := hp.1.1
      have : Nat.Coprime p H := (Nat.Prime.coprime_iff_not_dvd hprime).2 hp.2
      rw [coprimeInvWeight_apply, if_pos this]
    have h2 : ∏ p ∈ n.primeFactors.filter (fun p => ¬ ¬ p ∣ H), (1 - coprimeInvWeight H p)
        = 1 := by
      refine Finset.prod_eq_one ?_
      intro p hp
      rw [Finset.mem_filter, Nat.mem_primeFactors, not_not] at hp
      have hprime : p.Prime := hp.1.1
      have hnc : ¬ Nat.Coprime p H := by
        rw [Nat.Prime.coprime_iff_not_dvd hprime, not_not]
        exact hp.2
      rw [coprimeInvWeight_apply, if_neg hnc, sub_zero]
    rw [h1, h2, mul_one]
  have hright : ∑ d ∈ n.divisors, ((moebius d : ℚ) * coprimeInvWeight H d)
      = mProfileDivisor H n := by
    unfold mProfileDivisor
    refine Finset.sum_congr rfl ?_
    intro d _
    by_cases h : Nat.Coprime d H
    · rw [coprimeInvWeight_apply, if_pos h, if_pos h]
      ring
    · rw [coprimeInvWeight_apply, if_neg h, if_neg h, mul_zero]
  rw [← hright, ← hkey, hleft]

/-- **`DET1-SHORTLIFT-EULER-COLLAPSE45`, finite-prime-product level.**  `LEAN_PROVED`.

The `H_H / ζ` shape at the level of a finite prime product: for squarefree `n`,

```
∑_{d ∣ n, gcd(d,H)=1} μ(d)/d
  = (∏_{p ∣ n} (1 - 1/p)) · ∏_{p ∣ n, p ∣ H} (1 - 1/p)⁻¹,
```

the first factor being the finite surrogate of `1/ζ(1+w)` and the second that of `H_H(w)`.
No analytic statement is asserted. -/
theorem shortLift_euler_collapse_finite {n : ℕ} (hn : Squarefree n) (H : ℕ) :
    mProfileDivisor H n
      = (∏ p ∈ n.primeFactors, (1 - (1 : ℚ) / p))
        * ∏ p ∈ n.primeFactors.filter (fun p => p ∣ H), (1 - (1 : ℚ) / p)⁻¹ := by
  rw [mProfileDivisor_euler_product hn H]
  have hsplit : ∏ p ∈ n.primeFactors, (1 - (1 : ℚ) / p)
      = (∏ p ∈ n.primeFactors.filter (fun p => p ∣ H), (1 - (1 : ℚ) / p))
        * ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ H), (1 - (1 : ℚ) / p) :=
    (Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => p ∣ H) _).symm
  have hne : ∀ p ∈ n.primeFactors.filter (fun p => p ∣ H), (1 - (1 : ℚ) / p) ≠ 0 := by
    intro p hp
    rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
    have hprime : p.Prime := hp.1.1
    have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hprime.two_le
    have hppos : (0 : ℚ) < p := by linarith
    have : (1 : ℚ) / p < 1 := by
      rw [div_lt_one hppos]; linarith
    intro hcon
    rw [sub_eq_zero] at hcon
    linarith [hcon]
  rw [hsplit, mul_comm (∏ p ∈ n.primeFactors.filter (fun p => p ∣ H), (1 - (1 : ℚ) / p)),
    mul_assoc, ← Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl (fun p hp => mul_inv_cancel₀ (hne p hp)), Finset.prod_const_one,
    mul_one]

/-! ## §C.3  The analytic socket — stated, never inhabited -/

/-- **`ShortLiftEulerAnalyticInput` — ANALYTIC / UNINHABITED.**

The literal Dirichlet-series form of the short-lift Euler collapse:

```
∑_{gcd(d,H) = 1} μ(d) d^{-s} = H_H(s) / ζ(s)     (Re s > 1).
```

This is an analytic statement about an infinite series and the Riemann zeta function.  It is
**not** proved anywhere in this repository, and this structure has **no inhabitant**; it is
only ever consumed conditionally. -/
structure ShortLiftEulerAnalyticInput where
  /-- The claimed complementary Euler factor `H_H(s)`. -/
  H_H : ℕ → ℂ → ℂ
  /-- The claimed literal Dirichlet-series identity. -/
  identity : ∀ (H : ℕ) (s : ℂ), 1 < s.re →
    HasSum (fun d : ℕ => if Nat.Coprime d H then (moebius d : ℂ) / (d : ℂ) ^ s else 0)
      (H_H H s / riemannZeta s)

/-- The only use of the analytic socket: a trivial conditional consumer.  Nothing is proved
unconditionally. -/
theorem shortLift_euler_collapse_of_input (inp : ShortLiftEulerAnalyticInput)
    (H : ℕ) (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun d : ℕ => if Nat.Coprime d H then (moebius d : ℂ) / (d : ℂ) ^ s else 0)
      (inp.H_H H s / riemannZeta s) :=
  inp.identity H s hs

end ShortLift
end Erdos287
