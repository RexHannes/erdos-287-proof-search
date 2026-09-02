import RequestProject.CurrentProgramme.Run1BSmallModulusFourier

/-!
# RUN1B / d*wp provider — §7 centering and §8 the source-class router

```
h = 0 cancellation (centering)                  : KERNEL-PROVED
exact retention of the principal term           : KERNEL-PROVED (no term is deleted)
Ramanujan coefficient identity (prime modulus)  : KERNEL-PROVED
seven-class source router: total, exhaustive,
  pairwise distinct, analytics-independent      : KERNEL-PROVED (routing only)
```

All statements here are finite/algebraic.  The router is **metadata**: a kernel-proved
theorem states that it ignores every analytic field of a source datum, so analytic ownership
is never transferred by routing.

This module is **append-only** and project-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Run1B
namespace Centering

open Run1B.Characters Run1B.SmallModulus

/-! ## §7.1  The `h = 0` mode and centering -/

/-- The mean of an `n`-periodic weight over a full period. -/
noncomputable def periodMean (n : ℕ) (f : ℕ → ℂ) : ℂ :=
  (1 / (n : ℂ)) * ∑ u ∈ Finset.range n, f u

/-- The centred weight `f − mean(f)`. -/
noncomputable def centred (n : ℕ) (f : ℕ → ℂ) (u : ℕ) : ℂ := f u - periodMean n f

/-- **`fourierCoeff_zero_eq_mean`.**  `KERNEL-PROVED`.  The `h = 0` Fourier coefficient is
exactly the mean. -/
theorem fourierCoeff_zero_eq_mean (n : ℕ) (f : ℕ → ℂ) :
    SmallModulus.fourierCoeff n f 0 = periodMean n f := by
  unfold SmallModulus.fourierCoeff periodMean
  congr 1
  refine Finset.sum_congr rfl (fun u _ => ?_)
  simp [eAdd]

/-- **`centred_h_zero_cancellation`.**  `KERNEL-PROVED`.  Centering kills exactly the `h = 0`
mode. -/
theorem centred_h_zero_cancellation {n : ℕ} (hn : 0 < n) (f : ℕ → ℂ) :
    SmallModulus.fourierCoeff n (centred n f) 0 = 0 := by
  have hnC : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hmean : (n : ℂ) * periodMean n f = ∑ u ∈ Finset.range n, f u := by
    unfold periodMean
    field_simp
  rw [fourierCoeff_zero_eq_mean]
  unfold periodMean centred
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hmean]
  field_simp
  ring

/-- **`principal_term_is_retained`.**  `KERNEL-PROVED`.  Centering does **not** delete the
principal term: the full-period sum is exactly the principal term plus the centred sum. -/
theorem principal_term_is_retained {n : ℕ} (hn : 0 < n) (f : ℕ → ℂ) :
    ∑ u ∈ Finset.range n, f u
      = (n : ℂ) * periodMean n f + ∑ u ∈ Finset.range n, centred n f u := by
  have hnC : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hmean : (n : ℂ) * periodMean n f = ∑ u ∈ Finset.range n, f u := by
    unfold periodMean
    field_simp
  have hcent : ∑ u ∈ Finset.range n, centred n f u
      = (∑ u ∈ Finset.range n, f u) - (n : ℂ) * periodMean n f := by
    unfold centred
    rw [Finset.sum_sub_distrib]
    simp [nsmul_eq_mul]
  rw [hcent, hmean]
  ring

/-! ## §7.2  The Ramanujan coefficient identity at a prime modulus -/

/-- The Ramanujan sum `c_n(k) = ∑_{u = 1}^{n-1} e_n(u k)` restricted to a prime modulus,
where the summation range is exactly the invertible residues. -/
noncomputable def ramanujanSum (n : ℕ) (k : ℤ) : ℂ :=
  ∑ u ∈ Finset.Ico 1 n, eAdd n (k * (u : ℤ))

/-- **`ramanujanSum_prime`.**  `KERNEL-PROVED`.  For a prime modulus `p`,

```
c_p(k) = p − 1  if p ∣ k,      c_p(k) = −1  otherwise.
```
-/
theorem ramanujanSum_prime {p : ℕ} (hp : 0 < p) (k : ℤ) :
    ramanujanSum p k = (if (p : ℤ) ∣ k then (p : ℂ) else 0) - 1 := by
  have hfull : ∑ u ∈ Finset.range p, eAdd p (k * (u : ℤ))
      = if (p : ℤ) ∣ k then (p : ℂ) else 0 := eAdd_orthogonality hp k
  have hsplit : ∑ u ∈ Finset.range p, eAdd p (k * (u : ℤ))
      = eAdd p (k * ((0 : ℕ) : ℤ)) + ∑ u ∈ Finset.Ico 1 p, eAdd p (k * (u : ℤ)) := by
    rw [Finset.range_eq_Ico]
    exact Finset.sum_eq_sum_Ico_succ_bot hp _
  rw [ramanujanSum]
  have h0 : eAdd p (k * ((0 : ℕ) : ℤ)) = 1 := by simp
  rw [h0] at hsplit
  rw [hfull] at hsplit
  rw [hsplit]
  ring

end Centering

/-! ## §8  The source-class router -/

namespace SourceRouter

/-- The disjoint current 1B source classes. -/
inductive SourceClass
  /-- Pure Möbius sources. -/
  | pureMobius
  /-- Canonical composite sources. -/
  | canonicalComposite
  /-- Canonical singleton-prime sources. -/
  | canonicalSingletonPrime
  /-- Canonical semiprime sources. -/
  | canonicalSemiprime
  /-- Canonical short-core sources. -/
  | canonicalShortCore
  /-- Möbius-free Gamma sources. -/
  | mobiusFreeGamma
  /-- Local sources. -/
  | localSource
  deriving DecidableEq, Fintype, Repr

open SourceClass

/-- The literal finite data on which routing is allowed to depend, together with an analytic
field that routing must ignore. -/
structure SourceDatum where
  /-- Does the source carry a Möbius factor? -/
  hasMobius : Bool
  /-- Is the source in canonical form? -/
  isCanonical : Bool
  /-- Is the source a local (non-canonical, non-Möbius) source? -/
  isLocal : Bool
  /-- Is the canonical core short? -/
  shortCore : Bool
  /-- Number of prime factors of the canonical modulus. -/
  omegaCount : ℕ
  /-- An analytic quantity attached to the source.  Routing must **not** depend on it. -/
  savingExponent : ℝ

/-- The router.  It reads only the literal finite fields. -/
def route (d : SourceDatum) : SourceClass :=
  if d.isLocal then localSource
  else if d.hasMobius then
    (if d.isCanonical then
      (if d.shortCore then canonicalShortCore
        else match d.omegaCount with
          | 1 => canonicalSingletonPrime
          | 2 => canonicalSemiprime
          | _ => canonicalComposite)
      else pureMobius)
  else mobiusFreeGamma

/-- **`sourceClass_exhaustive`.**  `KERNEL-PROVED`.  The seven classes exhaust the type. -/
theorem sourceClass_exhaustive (c : SourceClass) :
    c = pureMobius ∨ c = canonicalComposite ∨ c = canonicalSingletonPrime ∨
      c = canonicalSemiprime ∨ c = canonicalShortCore ∨ c = mobiusFreeGamma ∨
      c = localSource := by
  cases c <;> simp

/-- **`route_total`.**  `KERNEL-PROVED`.  Routing is a total function: every source datum
lands in exactly one of the seven classes. -/
theorem route_total (d : SourceDatum) :
    route d = pureMobius ∨ route d = canonicalComposite ∨
      route d = canonicalSingletonPrime ∨ route d = canonicalSemiprime ∨
      route d = canonicalShortCore ∨ route d = mobiusFreeGamma ∨ route d = localSource :=
  sourceClass_exhaustive (route d)

/-- **`sourceClass_pairwise_distinct`.**  `KERNEL-PROVED`.  The seven classes are pairwise
distinct, so the routing is genuinely disjoint. -/
theorem sourceClass_pairwise_distinct :
    (Finset.univ : Finset SourceClass).card = 7 := by decide

/-- **`route_ignores_analytics`.**  `KERNEL-PROVED` firewall.  The router does not read the
analytic field: analytic ownership is never assigned by routing. -/
theorem route_ignores_analytics (d : SourceDatum) (x : ℝ) :
    route { d with savingExponent := x } = route d := rfl

/-- **`route_is_surjective`.**  `KERNEL-PROVED`.  Every class is actually reachable, so no
class is a vacuous label. -/
theorem route_is_surjective (c : SourceClass) : ∃ d : SourceDatum, route d = c := by
  cases c
  · exact ⟨⟨true, false, false, false, 0, 0⟩, rfl⟩
  · exact ⟨⟨true, true, false, false, 3, 0⟩, rfl⟩
  · exact ⟨⟨true, true, false, false, 1, 0⟩, rfl⟩
  · exact ⟨⟨true, true, false, false, 2, 0⟩, rfl⟩
  · exact ⟨⟨true, true, false, true, 0, 0⟩, rfl⟩
  · exact ⟨⟨false, false, false, false, 0, 0⟩, rfl⟩
  · exact ⟨⟨false, false, true, false, 0, 0⟩, rfl⟩

end SourceRouter
end Run1B
