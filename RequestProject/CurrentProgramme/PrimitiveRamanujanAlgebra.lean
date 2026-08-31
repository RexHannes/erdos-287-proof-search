import Mathlib
import RequestProject.Erdos287.NormalForm3221
import RequestProject.HostileAudit.GeneralModulusInducedCharacter

/-!
# Primitive `t` Ramanujan algebra — Erdős #287, PRIMITIVE-LOCALPROFILE Δ, §A

Exact algebra only.  Nothing analytic is proved or assumed here.

The additive character used is the **repository's own** phase
`Erdos287.NormalForm3221.phase x = exp(2πi x)`; the Ramanujan sum is defined from it
literally,

```
c_g(N) = ∑_{t < g, gcd(t,g) = 1} e(tN/g).
```

Banked in this file.

* `ramanujan_unit_shift` — `DET1-PRIMITIVE-T-RAMANUJAN45`:
  for a unit `2b (mod g)` with inverse `w`,
  `c_g(a + s·w) = c_g(2ab + s)`.
* `ramanujan_eq_divisor_sum` — `DET1-PRIMITIVE-RAMANUJAN-DIVISOR-NORMALFORM45`:
  `c_g(N) = ∑_{r ∣ gcd(g,N)} r · μ(g/r)`.
* `moebius_mul_moebius_div` and `ramanujan_moebius_normalForm` —
  `DET1-RAMANUJAN-MOBIUS-SIMPLIFICATION45`:
  for squarefree `g = r·k` with `gcd(r,k) = 1`, `μ(g)·μ(g/r) = μ(r)`, hence
  `μ(g)/g · c_g(N) = ∑_{r k = g, r ∣ N} μ(r)/k`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators
open ArithmeticFunction

namespace Erdos287
namespace PrimitiveRamanujan

open Erdos287.NormalForm3221

/-! ## §A.1  Elementary phase algebra -/

/-- `e(x)^n = e(nx)`. -/
theorem phase_pow (x : ℝ) (n : ℕ) : (phase x) ^ n = phase (n * x) := by
  unfold phase
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- `e(x) = 1` exactly for integer `x`. -/
theorem phase_eq_one_iff (x : ℝ) : phase x = 1 ↔ ∃ k : ℤ, x = k := by
  unfold phase
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h1 : ((x : ℂ)) * (2 * Real.pi * Complex.I) = (n : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast at hn ⊢; linear_combination hn
    have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [hpi, Complex.I_ne_zero]
    exact_mod_cast mul_right_cancel₀ hne h1
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; ring⟩

/-- `e(k) = 1` for an integer `k`. -/
theorem phase_intCast (k : ℤ) : phase (k : ℝ) = 1 := (phase_eq_one_iff _).2 ⟨k, rfl⟩

/-- The complete additive sum: `∑_{t < g} e(tN/g) = g·1_{g ∣ N}`. -/
theorem full_phase_sum (g : ℕ) (hg : 0 < g) (N : ℤ) :
    ∑ t ∈ Finset.range g, phase ((t : ℝ) * N / g) = if (g : ℤ) ∣ N then (g : ℂ) else 0 := by
  have hg0 : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hg.ne'
  have hterm : ∀ t ∈ Finset.range g, phase ((t : ℝ) * N / g) = (phase ((N : ℝ) / g)) ^ t := by
    intro t _
    rw [phase_pow]
    congr 1
    field_simp
  rw [Finset.sum_congr rfl hterm]
  set z := phase ((N : ℝ) / g) with hz
  by_cases hdvd : (g : ℤ) ∣ N
  · have hz1 : z = 1 := by
      obtain ⟨k, hk⟩ := hdvd
      refine (phase_eq_one_iff _).2 ⟨k, ?_⟩
      rw [hk]; push_cast; field_simp
    simp [hz1, hdvd]
  · have hz1 : z ≠ 1 := by
      intro h
      obtain ⟨k, hk⟩ := (phase_eq_one_iff _).1 h
      refine hdvd ⟨k, ?_⟩
      have : (N : ℝ) = g * k := by field_simp at hk; linarith [hk]
      exact_mod_cast this
    rw [geom_sum_eq hz1]
    have hzg : z ^ g = 1 := by
      rw [hz, phase_pow]
      have hgn : (g : ℝ) * ((N : ℝ) / g) = ((N : ℤ) : ℝ) := by field_simp
      rw [hgn, phase_intCast]
    simp [hzg, hdvd]

/-! ## §A.2  The Ramanujan sum -/

/-- The Ramanujan sum `c_g(N) = ∑_{t < g, gcd(t,g) = 1} e(tN/g)`, built from the
repository's additive phase. -/
noncomputable def ramanujan (g : ℕ) (N : ℤ) : ℂ :=
  ∑ t ∈ (Finset.range g).filter (fun t => Nat.Coprime t g), phase ((t : ℝ) * N / g)

/-- `c_g` only depends on `N` modulo `g`. -/
theorem ramanujan_congr {g : ℕ} {N N' : ℤ} (h : (g : ℤ) ∣ N - N') :
    ramanujan g N = ramanujan g N' := by
  rcases Nat.eq_zero_or_pos g with hg | hg
  · simp [ramanujan, hg]
  have hg0 : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hg.ne'
  refine Finset.sum_congr rfl ?_
  intro t _
  obtain ⟨k, hk⟩ := h
  refine phase_congr (t * k) ?_
  have hN : (N : ℝ) = N' + g * k := by
    have hNZ : (N : ℤ) = N' + g * k := by linarith [hk]
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hNZ
  rw [hN]
  field_simp
  push_cast
  ring

/-- For squarefree `g` and `r ∣ g`, the complementary factor is coprime to `r`. -/
theorem coprime_div_of_squarefree (g r : ℕ) (h : Squarefree g) (hr : r ∣ g) :
    Nat.Coprime r (g / r) := by
  obtain ⟨c, rfl⟩ := hr
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with rfl | h'
    · simp at h
    · exact h'
  rw [Nat.mul_div_cancel_left _ hr0]
  exact (Nat.squarefree_mul_iff.1 h).1

/-! ### The divisor normal form -/

/-- For `r ∣ g`, the multiples of `r` below `g` are exactly `r·u` with `u < g/r`. -/
theorem multiples_image {g r : ℕ} (hg : 0 < g) (hr : r ∣ g) (hr0 : 0 < r) :
    (Finset.range g).filter (fun t => r ∣ t) = (Finset.range (g / r)).image (fun u => r * u) := by
  obtain ⟨c, rfl⟩ := hr
  have hc : r * c / r = c := Nat.mul_div_cancel_left _ hr0
  rw [hc]
  ext t
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨ht, u, rfl⟩
    exact ⟨u, by
      have : u < c := by
        by_contra hcon
        push_neg at hcon
        exact absurd ht (by
          simp only [not_lt]
          exact Nat.mul_le_mul_left r hcon)
      exact this, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨mul_lt_mul_of_pos_left hu hr0, ⟨u, rfl⟩⟩

/-- **`DET1-PRIMITIVE-RAMANUJAN-DIVISOR-NORMALFORM45`.**  `LEAN_PROVED`.

`c_g(N) = ∑_{r ∣ gcd(g,N)} r · μ(g/r)`. -/
theorem ramanujan_eq_divisor_sum (g : ℕ) (hg : 0 < g) (N : ℤ) :
    ramanujan g N
      = ∑ r ∈ (Int.gcd (g : ℤ) N).divisors, (r : ℂ) * (moebius (g / r) : ℤ) := by
  have hgne : g ≠ 0 := hg.ne'
  -- Step 1: insert the Möbius expansion of the coprimality indicator.
  have step1 : ramanujan g N
      = ∑ t ∈ Finset.range g,
          ∑ r ∈ g.divisors.filter (fun d => d ∣ t),
            ((moebius r : ℤ) : ℂ) * phase ((t : ℝ) * N / g) := by
    unfold ramanujan
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro t _
    rw [← Finset.sum_mul]
    have h0 := Erdos287.HostileAudit.coprimeIndicator_moebius_expansion (n := t) (j := g) hgne
    have hsum : (∑ r ∈ g.divisors.filter (fun d => d ∣ t), ((moebius r : ℤ) : ℂ))
        = if Nat.Coprime t g then (1 : ℂ) else 0 := by
      have hcast : (∑ r ∈ g.divisors.filter (fun d => d ∣ t), ((moebius r : ℤ) : ℂ))
          = (((∑ r ∈ g.divisors.filter (fun d => d ∣ t), moebius r : ℤ)) : ℂ) := by
        push_cast; ring
      rw [hcast, h0]
      split <;> simp
    rw [hsum]
    split <;> simp
  -- Step 2: swap the order of summation.
  have step2 : ∑ t ∈ Finset.range g,
          ∑ r ∈ g.divisors.filter (fun d => d ∣ t),
            ((moebius r : ℤ) : ℂ) * phase ((t : ℝ) * N / g)
      = ∑ r ∈ g.divisors, ∑ t ∈ (Finset.range g).filter (fun t => r ∣ t),
            ((moebius r : ℤ) : ℂ) * phase ((t : ℝ) * N / g) := by
    refine Finset.sum_comm' ?_
    intro t r
    simp only [Finset.mem_filter, Finset.mem_range]
    tauto
  -- Step 3: evaluate the inner sums.
  have step3 : ∀ r ∈ g.divisors,
      ∑ t ∈ (Finset.range g).filter (fun t => r ∣ t),
            ((moebius r : ℤ) : ℂ) * phase ((t : ℝ) * N / g)
        = ((moebius r : ℤ) : ℂ) *
            (if ((g / r : ℕ) : ℤ) ∣ N then ((g / r : ℕ) : ℂ) else 0) := by
    intro r hr
    rw [Nat.mem_divisors] at hr
    obtain ⟨hrdvd, -⟩ := hr
    have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hrdvd hg
    have hgr0 : 0 < g / r := Nat.div_pos (Nat.le_of_dvd hg hrdvd) hr0
    rw [← Finset.mul_sum, multiples_image hg hrdvd hr0, Finset.sum_image (by
      intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hr0 hab)]
    congr 1
    rw [← full_phase_sum (g / r) hgr0 N]
    refine Finset.sum_congr rfl ?_
    intro u _
    congr 1
    have hgeq : (g : ℝ) = r * (g / r : ℕ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (Nat.eq_mul_of_div_eq_right hrdvd rfl)
    have hr0' : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hr0.ne'
    have hgr0' : ((g / r : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hgr0.ne'
    rw [hgeq]
    push_cast
    field_simp
  rw [step1, step2, Finset.sum_congr rfl step3]
  -- Step 4: reindex `r ↦ g/r`.
  have step4 : ∑ r ∈ g.divisors,
        ((moebius r : ℤ) : ℂ) * (if ((g / r : ℕ) : ℤ) ∣ N then ((g / r : ℕ) : ℂ) else 0)
      = ∑ k ∈ g.divisors,
        ((moebius (g / k) : ℤ) : ℂ) * (if (k : ℤ) ∣ N then (k : ℂ) else 0) := by
    rw [← Nat.sum_div_divisors g
      (fun k => ((moebius (g / k) : ℤ) : ℂ) * (if (k : ℤ) ∣ N then (k : ℂ) else 0))]
    refine Finset.sum_congr rfl ?_
    intro r hr
    rw [Nat.mem_divisors] at hr
    rw [Nat.div_div_self hr.1 hgne]
  rw [step4]
  -- Step 5: recognise the divisors of `gcd(g,N)`.
  have hdivs : (Int.gcd (g : ℤ) N).divisors
      = g.divisors.filter (fun k : ℕ => ((k : ℤ) ∣ N)) := by
    ext k
    simp only [Nat.mem_divisors, Finset.mem_filter]
    constructor
    · intro hk
      have h1 : (k : ℤ) ∣ (g : ℤ) :=
        dvd_trans (Int.natCast_dvd_natCast.2 hk.1) (Int.gcd_dvd_left _ _)
      have h2 : (k : ℤ) ∣ N := dvd_trans (Int.natCast_dvd_natCast.2 hk.1) (Int.gcd_dvd_right _ _)
      exact ⟨⟨Int.ofNat_dvd.1 h1, hgne⟩, h2⟩
    · rintro ⟨⟨hkg, -⟩, hkN⟩
      refine ⟨Int.dvd_gcd (Int.natCast_dvd_natCast.2 hkg) hkN, ?_⟩
      intro h
      have : (Int.gcd (g : ℤ) N : ℤ) = 0 := by exact_mod_cast h
      have hg' : (g : ℤ) = 0 := Int.eq_zero_of_gcd_eq_zero_left (by exact_mod_cast h)
      exact hgne (by exact_mod_cast hg')
  rw [hdivs, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro k _
  split <;> simp [mul_comm]

/-! ### Invariance under multiplication by a unit -/

/-- `c_g` is invariant under multiplication of the argument by a unit mod `g`. -/
theorem ramanujan_unit_mul {g : ℕ} (hg : 0 < g) {u : ℤ} (hu : IsCoprime u (g : ℤ)) (N : ℤ) :
    ramanujan g (u * N) = ramanujan g N := by
  rw [ramanujan_eq_divisor_sum g hg, ramanujan_eq_divisor_sum g hg]
  congr 1
  have hgcd : Int.gcd (g : ℤ) (u * N) = Int.gcd (g : ℤ) N := by
    refine Nat.dvd_antisymm ?_ ?_
    · have h1 : (Int.gcd (g : ℤ) (u * N) : ℤ) ∣ (g : ℤ) := Int.gcd_dvd_left _ _
      have h2 : (Int.gcd (g : ℤ) (u * N) : ℤ) ∣ u * N := Int.gcd_dvd_right _ _
      have hcop : IsCoprime ((Int.gcd (g : ℤ) (u * N) : ℤ)) u :=
        hu.symm.of_isCoprime_of_dvd_left h1
      have hN : (Int.gcd (g : ℤ) (u * N) : ℤ) ∣ N := hcop.dvd_of_dvd_mul_left h2
      exact_mod_cast Int.dvd_gcd h1 hN
    · exact_mod_cast Int.dvd_gcd (a := (g : ℤ)) (b := u * N) (Int.gcd_dvd_left (g : ℤ) N)
        (Dvd.dvd.mul_left (Int.gcd_dvd_right (g : ℤ) N) u)
  rw [hgcd]

/-- **`DET1-PRIMITIVE-T-RAMANUJAN45`.**  `LEAN_PROVED`.

If `w` is an inverse of `2b` modulo `g` then `c_g(a + s·w) = c_g(2ab + s)`. -/
theorem ramanujan_unit_shift {g : ℕ} (hg : 0 < g) (a b s w : ℤ)
    (hw : (g : ℤ) ∣ 2 * b * w - 1) :
    ramanujan g (a + s * w) = ramanujan g (2 * a * b + s) := by
  have hcop : IsCoprime (2 * b) (g : ℤ) := by
    obtain ⟨k, hk⟩ := hw
    exact ⟨w, -k, by linarith [hk]⟩
  have h1 : ramanujan g ((2 * b) * (a + s * w)) = ramanujan g (a + s * w) :=
    ramanujan_unit_mul hg hcop _
  have h2 : ramanujan g ((2 * b) * (a + s * w)) = ramanujan g (2 * a * b + s) := by
    refine ramanujan_congr ?_
    obtain ⟨k, hk⟩ := hw
    exact ⟨s * k, by linear_combination s * hk⟩
  rw [← h1, h2]

/-! ## §A.3  Möbius simplification on the squarefree sector -/

/-- **`DET1-RAMANUJAN-MOBIUS-SIMPLIFICATION45`, part 1.**  `LEAN_PROVED`.

For squarefree `g = r·k` with `gcd(r,k) = 1`: `μ(g)·μ(g/r) = μ(r)`. -/
theorem moebius_mul_moebius_div {g r k : ℕ} (hg : Squarefree g) (hrk : g = r * k)
    (hcop : Nat.Coprime r k) :
    (moebius g) * (moebius (g / r)) = moebius r := by
  have hr0 : r ≠ 0 := by rintro rfl; simp [hrk] at hg
  have hdiv : g / r = k := by rw [hrk]; exact Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hr0)
  have hk : Squarefree k := by
    refine hg.squarefree_of_dvd ?_
    exact ⟨r, by rw [hrk]; ring⟩
  have hgm : moebius g = moebius r * moebius k := by
    rw [hrk]
    exact isMultiplicative_moebius.map_mul_of_coprime hcop
  rw [hdiv, hgm]
  have hk2 : moebius k * moebius k = 1 := by
    have := moebius_sq_eq_one_of_squarefree hk
    nlinarith [this]
  calc moebius r * moebius k * moebius k = moebius r * (moebius k * moebius k) := by ring
    _ = moebius r := by rw [hk2, mul_one]

/-- **`DET1-RAMANUJAN-MOBIUS-SIMPLIFICATION45`, part 2.**  `LEAN_PROVED`.

For squarefree `g > 0`:

```
μ(g)/g · c_g(N) = ∑_{r ∣ gcd(g,N)} μ(r)/(g/r),
```

i.e. exactly `∑_{r k = g, r ∣ N} μ(r)/k`. -/
theorem ramanujan_moebius_normalForm {g : ℕ} (hg : 0 < g) (hsq : Squarefree g) (N : ℤ) :
    ((moebius g : ℤ) : ℂ) / (g : ℂ) * ramanujan g N
      = ∑ r ∈ (Int.gcd (g : ℤ) N).divisors, ((moebius r : ℤ) : ℂ) / ((g / r : ℕ) : ℂ) := by
  have hg0 : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hg.ne'
  rw [ramanujan_eq_divisor_sum g hg, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro r hr
  have hrg : r ∣ g := by
    have := (Nat.mem_divisors.1 hr).1
    exact this.trans (Int.natCast_dvd_natCast.1 (Int.gcd_dvd_left _ _))
  have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hrg hg
  have hkey : (moebius g) * (moebius (g / r)) = moebius r :=
    moebius_mul_moebius_div hsq (by rw [Nat.mul_div_cancel' hrg])
      (coprime_div_of_squarefree g r hsq hrg)
  have hgr : (g : ℂ) = (r : ℂ) * ((g / r : ℕ) : ℂ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℂ)) (Nat.mul_div_cancel' hrg).symm
  have hrne : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr0.ne'
  have hgrne : ((g / r : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.div_pos (Nat.le_of_dvd hg hrg) hr0).ne'
  have hkeyC : ((moebius g : ℤ) : ℂ) * ((moebius (g / r) : ℤ) : ℂ) = ((moebius r : ℤ) : ℂ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) hkey
  rw [hgr]
  field_simp
  exact hkeyC

end PrimitiveRamanujan
end Erdos287
