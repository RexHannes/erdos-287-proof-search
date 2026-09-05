import Mathlib
import RequestProject.Erdos287.AllComplement

/-!
# Erdős #287 effectivity — finite Euler local factors (§4, §15, §16, §18)

```
CONTINUOUS EULER IDENTITY (finite)      : KERNEL-PROVED
CONTINUOUS EULER IDENTITY (infinite)    : CONDITIONAL  (convergence is a hypothesis)
LOCAL NUMERATOR VANISHES AT s = 0       : KERNEL-PROVED
1 − 2^{−s−1} ≠ 0 AT s = 0               : KERNEL-PROVED
G_p LOCAL FACTOR                        : KERNEL-PROVED
FINITE B1·G(u,0) = 1                    : KERNEL-PROVED
G MAJORANT AT v = 0                     : KERNEL-PROVED (partial: the `v = 0` slice)
```

Everything here is a **finite** product identity.  The infinite Euler product is never
postulated: the only global statement (`continuousEuler_conditional`) takes the two
convergence hypotheses as explicit `Tendsto` assumptions and concludes by uniqueness of
limits from the finite identity.

## Missing analytic input (isolated, not assumed)

To upgrade the `v = 0` majorant `|G_p(u,0) − 1| = 1/(p(p−2)) ≤ 3/p²` to absolute
convergence of `∏_p G_p(u,v)` on a compact subset of `{Re u > 0, Re v > −1/2,
Re(u+v) > 0}` one still needs (i) the two-variable uniform bound on such a compact set,
and (ii) a multipliability criterion of the form
`Summable (fun p => ‖G_p − 1‖) → Multipliable G_p` applied along the primes.  Neither is
proved here, and nothing below presupposes them.

Local normalisation:

    B1loc(p) = p(p−2)/(p−1)²,    B1fin(P) = ∏_{p∈P} B1loc(p),
    Pcomp_d(P) = ∏_{p ∈ P \ P(d)} (1 + 1/(p(p−2))).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §4.1  Finite local factors -/

/-- The local factor of the global constant `B1`: `p(p−2)/(p−1)²`. -/
def B1loc (p : ℕ) : ℚ := ((p : ℚ) * ((p : ℚ) - 2)) / ((p : ℚ) - 1) ^ 2

/-- The finite truncation `B1fin(P) = ∏_{p ∈ P} B1loc(p)`. -/
def B1fin (P : Finset ℕ) : ℚ := ∏ p ∈ P, B1loc p

/-- The finite complement product `∏_{p ∈ P \ P(d)} (1 + 1/(p(p−2)))`. -/
def Pcomp (d : ℕ) (P : Finset ℕ) : ℚ :=
  ∏ p ∈ P \ d.primeFactors, (1 + 1 / ((p : ℚ) * ((p : ℚ) - 2)))

lemma cast_ne_zero_of_prime {p : ℕ} (hp : p.Prime) : (p : ℚ) ≠ 0 := by
  exact_mod_cast hp.ne_zero

lemma sub_one_ne_zero_of_prime {p : ℕ} (hp : p.Prime) : ((p : ℚ) - 1) ≠ 0 := by
  have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
  intro h; linarith [sub_eq_zero.1 h]

/-- **`euler_local_identity`.**  `KERNEL-PROVED`.  The exact finite local identity behind §4:

    B1fin(P) · B0(d) · Pcomp_d(P) = d/φ(d)

whenever `P` is a finite set of odd primes containing all prime factors of `d`. -/
theorem euler_local_identity {d : ℕ} (hd0 : d ≠ 0) {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hsub : d.primeFactors ⊆ P) :
    B1fin P * B0 d * Pcomp d P = (d : ℚ) / (d.totient : ℚ) := by
  classical
  have hoddPF : oddPrimeFactors d = d.primeFactors := by
    refine Finset.erase_eq_of_notMem fun h2 => ?_
    exact (hP 2 (hsub h2)).2 rfl
  -- split `P` into the primes of `d` and the complement
  have hsplit : B1fin P = (∏ p ∈ d.primeFactors, B1loc p) * ∏ p ∈ P \ d.primeFactors, B1loc p := by
    rw [B1fin, ← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hsub]
  -- the complement contributes `1`
  have hcomp : (∏ p ∈ P \ d.primeFactors, B1loc p) * Pcomp d P = 1 := by
    rw [Pcomp, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun p hp => ?_
    have hprime : p.Prime := (hP p (Finset.mem_sdiff.1 hp).1).1
    have h2 : p ≠ 2 := (hP p (Finset.mem_sdiff.1 hp).1).2
    have hp0 : (p : ℚ) ≠ 0 := cast_ne_zero_of_prime hprime
    have hp1 : ((p : ℚ) - 1) ≠ 0 := sub_one_ne_zero_of_prime hprime
    have hp2 : ((p : ℚ) - 2) ≠ 0 := sub_two_ne_zero hprime h2
    rw [B1loc]
    field_simp
    ring
  -- the primes of `d` give `∏ p/(p−1) = d/φ(d)`
  have hd : (∏ p ∈ d.primeFactors, B1loc p) * B0 d = ∏ p ∈ d.primeFactors, (p : ℚ) / ((p : ℚ) - 1) := by
    rw [B0, hoddPF, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have h2 : p ≠ 2 := (hP p (hsub hp)).2
    have hp0 : (p : ℚ) ≠ 0 := cast_ne_zero_of_prime hprime
    have hp1 : ((p : ℚ) - 1) ≠ 0 := sub_one_ne_zero_of_prime hprime
    have hp2 : ((p : ℚ) - 2) ≠ 0 := sub_two_ne_zero hprime h2
    rw [B1loc]
    field_simp
  have htot : (d : ℚ) / (d.totient : ℚ) = ∏ p ∈ d.primeFactors, (p : ℚ) / ((p : ℚ) - 1) := by
    have hphi : ((d.totient : ℚ)) = (d : ℚ) * ∏ p ∈ d.primeFactors, (1 - ((p : ℚ))⁻¹) :=
      Nat.totient_eq_mul_prod_factors d
    have hd0' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hd0
    have hprod : (∏ p ∈ d.primeFactors, (1 - ((p : ℚ))⁻¹))
        = ∏ p ∈ d.primeFactors, (((p : ℚ) - 1) / (p : ℚ)) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp0 : (p : ℚ) ≠ 0 := cast_ne_zero_of_prime (Nat.prime_of_mem_primeFactors hp)
      field_simp
    have hne : (∏ p ∈ d.primeFactors, (((p : ℚ) - 1) / (p : ℚ))) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun p hp => ?_
      have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      exact div_ne_zero (sub_one_ne_zero_of_prime hprime) (cast_ne_zero_of_prime hprime)
    have hinv : (∏ p ∈ d.primeFactors, (((p : ℚ) - 1) / (p : ℚ)))⁻¹
        = ∏ p ∈ d.primeFactors, (p : ℚ) / ((p : ℚ) - 1) := by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun p _ => inv_div _ _
    rw [hphi, hprod, ← hinv]
    field_simp
  calc B1fin P * B0 d * Pcomp d P
      = ((∏ p ∈ d.primeFactors, B1loc p) * B0 d) *
          ((∏ p ∈ P \ d.primeFactors, B1loc p) * Pcomp d P) := by rw [hsplit]; ring
    _ = ∏ p ∈ d.primeFactors, (p : ℚ) / ((p : ℚ) - 1) := by rw [hd, hcomp, mul_one]
    _ = (d : ℚ) / (d.totient : ℚ) := htot.symm

/-! ## §4.2  The finite `β(k)/k` sum -/

/-- `β(k)/k` restricted to `k` coprime to `2d`. -/
def betaOverK (d k : ℕ) : ℚ := betaCop (2 * d) k / (k : ℚ)

/-- **`betaOverK_finite_sum`.**  `KERNEL-PROVED`.  The truncated `∑ β(k)/k` over the divisors
of a finite primorial equals the finite complement product. -/
theorem betaOverK_finite_sum {d : ℕ} (hd0 : d ≠ 0) {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) :
    ∑ k ∈ (∏ p ∈ P, p).divisors, betaOverK d k = Pcomp d P := by
  classical
  have hprimes : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have hne : (∏ p ∈ P, p) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p hp => (hprimes p hp).ne_zero
  have hkey : ∑ k ∈ (∏ p ∈ P, p).divisors, betaOverK d k
      = ∏ p ∈ (∏ p ∈ P, p).primeFactors, (1 + betaOverK d p) := by
    refine sum_divisors_of_squarefreeSupported hne _ ?_ ?_
    · intro k hk
      rw [betaOverK, betaCop_eq_zero_of_not_squarefree hk, zero_div]
    · intro t ht
      rw [betaOverK, betaCop_prod_primes (2 * d) ht]
      push_cast
      rw [← Finset.prod_div_distrib]
      rfl
  rw [hkey, Nat.primeFactors_prod hprimes, Pcomp]
  -- only the primes outside `P(d)` contribute
  have hsub : P \ d.primeFactors ⊆ P := Finset.sdiff_subset
  rw [← Finset.prod_subset hsub ?_]
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hmem := Finset.mem_sdiff.1 hp
    have hprime : p.Prime := (hP p hmem.1).1
    have h2 : p ≠ 2 := (hP p hmem.1).2
    have hnd : ¬ p ∣ 2 * d := by
      intro hdvd
      rcases (Nat.Prime.dvd_mul hprime).1 hdvd with h | h
      · exact h2 (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two |>.1 h)
      · exact hmem.2 (Nat.mem_primeFactors.2 ⟨hprime, h, hd0⟩)
    rw [betaOverK, betaCop_prime hprime, if_pos ⟨h2, hnd⟩]
    have hp0 : (p : ℚ) ≠ 0 := cast_ne_zero_of_prime hprime
    have hp2 : ((p : ℚ) - 2) ≠ 0 := sub_two_ne_zero hprime h2
    field_simp
  · intro p hp hpn
    have hprime : p.Prime := (hP p hp).1
    have h2 : p ≠ 2 := (hP p hp).2
    have hdvd : p ∣ d := by
      by_contra hnd
      exact hpn (Finset.mem_sdiff.2 ⟨hp, fun hmem =>
        hnd (Nat.dvd_of_mem_primeFactors hmem)⟩)
    have : p ∣ 2 * d := hdvd.mul_left 2
    rw [betaOverK, betaCop_prime hprime, if_neg (by tauto)]
    simp

/-! ## §4.3  The conditional infinite statement -/

/-- The odd primes below `N`. -/
def oddPrimesBelow (N : ℕ) : Finset ℕ := (Finset.range N).filter (fun p => p.Prime ∧ p ≠ 2)

lemma primeFactors_subset_oddPrimesBelow {d N : ℕ} (hd0 : d ≠ 0) (hodd : ¬ 2 ∣ d) (hN : d < N) :
    d.primeFactors ⊆ oddPrimesBelow N := by
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
  have hple : p ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hdvd
  refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hprime, ?_⟩
  rintro rfl
  exact hodd hdvd

/-- **`continuousEuler_conditional`.**  `KERNEL-PROVED` as an implication.  If the two finite
truncations converge, their limits satisfy the continuous Euler identity

    B1 · B0(d) · Π_d = d/φ(d).

Convergence is **not** postulated: it is the hypothesis. -/
theorem continuousEuler_conditional {d : ℕ} (hd0 : d ≠ 0) (hodd : ¬ 2 ∣ d) (L1 L2 : ℝ)
    (h1 : Filter.Tendsto (fun N => ((B1fin (oddPrimesBelow N) : ℚ) : ℝ)) Filter.atTop (nhds L1))
    (h2 : Filter.Tendsto (fun N => ((Pcomp d (oddPrimesBelow N) : ℚ) : ℝ)) Filter.atTop (nhds L2)) :
    L1 * ((B0 d : ℚ) : ℝ) * L2 = (d : ℝ) / (d.totient : ℝ) := by
  have hconst : ∀ᶠ N in Filter.atTop,
      ((B1fin (oddPrimesBelow N) : ℚ) : ℝ) * ((B0 d : ℚ) : ℝ) * ((Pcomp d (oddPrimesBelow N) : ℚ) : ℝ)
        = (d : ℝ) / (d.totient : ℝ) := by
    filter_upwards [Filter.eventually_gt_atTop d] with N hN
    have hQ := euler_local_identity hd0
      (P := oddPrimesBelow N)
      (fun p hp => ⟨(Finset.mem_filter.1 hp).2.1, (Finset.mem_filter.1 hp).2.2⟩)
      (primeFactors_subset_oddPrimesBelow hd0 hodd hN)
    have hR := congrArg (fun q : ℚ => (q : ℝ)) hQ
    push_cast at hR
    exact hR
  have hlim : Filter.Tendsto
      (fun N => ((B1fin (oddPrimesBelow N) : ℚ) : ℝ) * ((B0 d : ℚ) : ℝ)
        * ((Pcomp d (oddPrimesBelow N) : ℚ) : ℝ)) Filter.atTop
      (nhds (L1 * ((B0 d : ℚ) : ℝ) * L2)) :=
    (h1.mul (tendsto_const_nhds (x := ((B0 d : ℚ) : ℝ)))).mul h2
  have hlim' : Filter.Tendsto
      (fun N => ((B1fin (oddPrimesBelow N) : ℚ) : ℝ) * ((B0 d : ℚ) : ℝ)
        * ((Pcomp d (oddPrimesBelow N) : ℚ) : ℝ)) Filter.atTop (nhds ((d : ℝ) / (d.totient : ℝ))) :=
    Filter.Tendsto.congr' (by filter_upwards [hconst] with N hN using hN.symm) tendsto_const_nhds
  exact tendsto_nhds_unique hlim hlim'

/-! ## §15  The local continuous Dirichlet factor -/

/-- The local ratio `(1 − x/(p−1))/(1 − x/p)` (with `x = p^{-s}`). -/
def localRatio (p : ℕ) (x : ℚ) : ℚ := (1 - x / ((p : ℚ) - 1)) / (1 - x / (p : ℚ))

/-- **`localRatio_closed_form`.**  `KERNEL-PROVED`. -/
theorem localRatio_closed_form {p : ℕ} (hp : p.Prime) {x : ℚ} (hx : x ≠ (p : ℚ)) :
    localRatio p x = ((p : ℚ) * ((p : ℚ) - 1 - x)) / (((p : ℚ) - 1) * ((p : ℚ) - x)) := by
  have hp0 : (p : ℚ) ≠ 0 := cast_ne_zero_of_prime hp
  have hp1 : ((p : ℚ) - 1) ≠ 0 := sub_one_ne_zero_of_prime hp
  have hpx : ((p : ℚ) - x) ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  rw [localRatio]
  field_simp

/-- **`localNumerator_vanishes_at_zero`.**  `KERNEL-PROVED`.  At `s = 0` (i.e. `x = 1`) the
local ratio *is* the local factor of `B1`, so the finite numerator `∏ localRatio − B1fin`
vanishes identically. -/
theorem localRatio_one {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : localRatio p 1 = B1loc p := by
  have hp0 : (p : ℚ) ≠ 0 := cast_ne_zero_of_prime hp
  have hp1 : ((p : ℚ) - 1) ≠ 0 := sub_one_ne_zero_of_prime hp
  have hp2 : ((p : ℚ) - 2) ≠ 0 := sub_two_ne_zero hp h2
  rw [localRatio, B1loc]
  field_simp
  ring

/-- **`localNumerator_vanishes_at_zero`.**  `KERNEL-PROVED`. -/
theorem localNumerator_vanishes_at_zero {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) :
    (∏ p ∈ P, localRatio p 1) - B1fin P = 0 := by
  rw [B1fin, Finset.prod_congr rfl (fun p hp => localRatio_one (hP p hp).1 (hP p hp).2), sub_self]

/-- The `2`-adic factor `1 − 2^{−s−1}` of the shifted zeta function. -/
noncomputable def twoFactor (s : ℂ) : ℂ := 1 - (2 : ℂ) ^ (-s - 1)

/-- **`twoFactor_zero`.**  `KERNEL-PROVED`.  `1 − 2^{−s−1} = 1/2 ≠ 0` at `s = 0`. -/
theorem twoFactor_zero : twoFactor 0 = 1 / 2 := by
  rw [twoFactor]
  norm_num
  rw [show (-1 : ℂ) = ((-1 : ℤ) : ℂ) by norm_num, Complex.cpow_intCast]
  norm_num

theorem twoFactor_zero_ne_zero : twoFactor 0 ≠ 0 := by
  rw [twoFactor_zero]; norm_num

/-! ## §16  The `G_p(u,v)` local factor -/

/-- The local factor `G_p(u,v)` written in the variables `x = p^{-u}`, `y = p^{-v}`. -/
def Gloc (p : ℕ) (x y : ℚ) : ℚ :=
  (1 - y / (p : ℚ)) * (1 + y / ((p : ℚ) - 2) - (((p : ℚ) - 1) / ((p : ℚ) - 2)) * x) / (1 - x)

/-- **`Gloc_at_v_zero`.**  `KERNEL-PROVED`.  At `v = 0` (i.e. `y = 1`),

    G_p(u,0) = (p−1)²/(p(p−2)). -/
theorem Gloc_at_v_zero {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) {x : ℚ} (hx : x ≠ 1) :
    Gloc p x 1 = ((p : ℚ) - 1) ^ 2 / ((p : ℚ) * ((p : ℚ) - 2)) := by
  have hp0 : (p : ℚ) ≠ 0 := cast_ne_zero_of_prime hp
  have hp2 : ((p : ℚ) - 2) ≠ 0 := sub_two_ne_zero hp h2
  have hx1 : (1 - x) ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  rw [Gloc]
  field_simp
  ring

/-- **`B1loc_mul_Gloc_v_zero`.**  `KERNEL-PROVED`.  `B1loc(p)·G_p(u,0) = 1`. -/
theorem B1loc_mul_Gloc_v_zero {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) {x : ℚ} (hx : x ≠ 1) :
    B1loc p * Gloc p x 1 = 1 := by
  have hp0 : (p : ℚ) ≠ 0 := cast_ne_zero_of_prime hp
  have hp1 : ((p : ℚ) - 1) ≠ 0 := sub_one_ne_zero_of_prime hp
  have hp2 : ((p : ℚ) - 2) ≠ 0 := sub_two_ne_zero hp h2
  rw [Gloc_at_v_zero hp h2 hx, B1loc]
  field_simp

/-- **`B1fin_mul_Gfin_v_zero`.**  `KERNEL-PROVED`.  Every **finite** product over odd primes
satisfies `B1fin(P) · ∏_{p ∈ P} G_p(u,0) = 1`.  (No infinite-product statement is claimed.) -/
theorem B1fin_mul_Gfin_v_zero {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (x : ℕ → ℚ)
    (hx : ∀ p ∈ P, x p ≠ 1) :
    B1fin P * ∏ p ∈ P, Gloc p (x p) 1 = 1 := by
  rw [B1fin, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun p hp =>
    B1loc_mul_Gloc_v_zero (hP p hp).1 (hP p hp).2 (hx p hp)

/-! ## §18  The majorant, at `v = 0` -/

/-- **`Gloc_v_zero_sub_one`.**  `KERNEL-PROVED`.  `G_p(u,0) − 1 = 1/(p(p−2))`. -/
theorem Gloc_v_zero_sub_one {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) {x : ℚ} (hx : x ≠ 1) :
    Gloc p x 1 - 1 = 1 / ((p : ℚ) * ((p : ℚ) - 2)) := by
  have hp0 : (p : ℚ) ≠ 0 := cast_ne_zero_of_prime hp
  have hp2 : ((p : ℚ) - 2) ≠ 0 := sub_two_ne_zero hp h2
  rw [Gloc_at_v_zero hp h2 hx]
  field_simp
  ring

/-- **`Gloc_v_zero_majorant`.**  `KERNEL-PROVED` (the `v = 0` slice of the requested
majorant): `|G_p(u,0) − 1| ≤ 3/p²` for every odd prime `p`. -/
theorem Gloc_v_zero_majorant {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) {x : ℚ} (hx : x ≠ 1) :
    |Gloc p x 1 - 1| ≤ 3 / (p : ℚ) ^ 2 := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have hp3 : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h3
  have hp0 : (0 : ℚ) < (p : ℚ) := by linarith
  have hp2 : (0 : ℚ) < (p : ℚ) - 2 := by linarith
  rw [Gloc_v_zero_sub_one hp h2 hx, abs_of_pos (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

end Effectivity
end Erdos287
