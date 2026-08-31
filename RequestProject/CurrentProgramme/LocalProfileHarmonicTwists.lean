import Mathlib
import RequestProject.CurrentProgramme.ShortLiftLocalProfile
import RequestProject.CurrentProgramme.ConductorSplitLargeSieve

/-!
# Exact local-profile harmonic expansion — Erdős #287, SHARED-g₀ REPAIR Δ, §1

**Exact finite algebra.**  No asymptotics; in particular the research claim
`total L¹ cost = log^{o(1)} X` is *not* formalised — the divisor estimates it needs are not
available in this repository.

The reduction expands the coprimality constraint of the repository's own local profile

```
m_{g,b}(Δ) = ∑_{gcd(d, 2bg) = 1} μ(d)/d · Ψ(d/Δ)     (`Erdos287.ShortLift.mProfile`)
```

by `1_{gcd(d,H)=1} = ∑_{ℓ ∣ gcd(d,H)} μ(ℓ)` and the squarefree support of `μ`, giving the
**exact finite** identity

```
m_{g,b}(Δ) = ∑_{ℓ ∣ rad(2bg)} (1/ℓ) · ∑_{e ≥ 1, gcd(e,ℓ) = 1} μ(e)/e · Ψ(ℓe/Δ),
```

in the finite-support (truncated at `T`) form compatible with `mProfile`: the inner sum runs
over `1 ≤ e ≤ ⌊T/ℓ⌋`.

Proved here:

* `rad_squarefree`, `gcd_rad_eq_one_iff` — the radical bookkeeping;
* `moebius_coprime_twist_sum` — the exact pointwise Möbius identity
  `∑_{ℓ ∣ rad H, ℓ ∣ d, gcd(d/ℓ,ℓ)=1} μ(d/ℓ) = 1_{gcd(d,H)=1} μ(d)`;
* `mProfile_harmonic_twist_expansion` — **`DET1-LOCALPROFILE-HARMONIC-TWISTS45`, algebraic
  core**: the displayed exact finite expansion.

Research status: `DET1-LOCALPROFILE-HARMONIC-TWISTS45 : ALGEBRAIC CORE FORMALLY PROVED;
ANALYTIC L¹ COST RESEARCH PASS (not formalised).`
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators
open ArithmeticFunction

namespace Erdos287
namespace LocalProfileHarmonic

open Erdos287.ShortLift

/-! ## §1.1  The radical -/

/-- The radical `rad n = ∏_{p ∣ n} p`. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- The radical is nonzero. -/
theorem rad_ne_zero (n : ℕ) : rad n ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 ?_
  intro p hp
  exact (Nat.prime_of_mem_primeFactors hp).pos.ne'

/-- The radical is squarefree. -/
theorem rad_squarefree (n : ℕ) : Squarefree (rad n) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro a ha b hb hab
    have hpa := Nat.prime_of_mem_primeFactors ha
    have hpb := Nat.prime_of_mem_primeFactors hb
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes hpa hpb).mpr hab)
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).squarefree

/-- Coprimality to `n` is coprimality to its radical. -/
theorem gcd_rad_eq_one_iff {d n : ℕ} (hn : n ≠ 0) :
    Nat.gcd d (rad n) = 1 ↔ Nat.Coprime d n := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨p, hp, hpd, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.1 hc
    have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpn, hn⟩
    have hdvd : p ∣ rad n := Finset.dvd_prod_of_mem _ hmem
    have hgd := Nat.dvd_gcd hpd hdvd
    rw [h] at hgd
    exact hp.one_lt.ne' (Nat.dvd_one.1 hgd)
  · intro h
    exact Nat.Coprime.prod_right
      (fun p hp => Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mem_primeFactors hp) h)

/-- Every divisor of a radical is squarefree. -/
theorem squarefree_of_dvd_rad {ℓ n : ℕ} (h : ℓ ∣ rad n) : Squarefree ℓ :=
  (rad_squarefree n).squarefree_of_dvd h

/-! ## §1.2  The exact pointwise Möbius identity -/

/-- **`LEAN_PROVED`.**  The exact finite Möbius identity behind the harmonic expansion:

```
∑_{ℓ ∣ rad H, ℓ ∣ d, gcd(d/ℓ, ℓ) = 1} μ(d/ℓ) = 1_{gcd(d,H)=1} · μ(d).
```
-/
theorem moebius_coprime_twist_sum {H d : ℕ} (hH : H ≠ 0) :
    ∑ ℓ ∈ (rad H).divisors.filter (fun ℓ => ℓ ∣ d ∧ Nat.Coprime (d / ℓ) ℓ),
        (moebius (d / ℓ) : ℤ)
      = if Nat.Coprime d H then (moebius d : ℤ) else 0 := by
  classical
  by_cases hsq : Squarefree d
  · -- squarefree `d`: the coprimality condition is automatic and `μ(d/ℓ) = μ(d)μ(ℓ)`
    have hfilter : (rad H).divisors.filter (fun ℓ => ℓ ∣ d ∧ Nat.Coprime (d / ℓ) ℓ)
        = (Nat.gcd d (rad H)).divisors := by
      ext ℓ
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, _⟩, h2, _⟩
        exact ⟨⟨h2, h1⟩, Nat.gcd_ne_zero_right (rad_ne_zero H)⟩
      · rintro ⟨⟨h1, h2⟩, _⟩
        refine ⟨⟨h2, rad_ne_zero H⟩, h1, ?_⟩
        exact (Erdos287.PrimitiveRamanujan.coprime_div_of_squarefree d ℓ hsq h1).symm
    have hterm : ∀ ℓ ∈ (Nat.gcd d (rad H)).divisors,
        (moebius (d / ℓ) : ℤ) = (moebius d : ℤ) * (moebius ℓ : ℤ) := by
      intro ℓ hℓ
      rw [Nat.mem_divisors] at hℓ
      have hℓd : ℓ ∣ d := dvd_trans hℓ.1 (Nat.gcd_dvd_left _ _)
      have hcop : Nat.Coprime ℓ (d / ℓ) :=
        Erdos287.PrimitiveRamanujan.coprime_div_of_squarefree d ℓ hsq hℓd
      have hkey : (moebius d) * (moebius (d / ℓ)) = moebius ℓ :=
        Erdos287.PrimitiveRamanujan.moebius_mul_moebius_div hsq
          (by rw [Nat.mul_div_cancel' hℓd]) hcop
      have hsqd : (moebius d) * (moebius d) = 1 := by
        rcases ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq with h
        nlinarith [h]
      calc (moebius (d / ℓ) : ℤ)
          = ((moebius d) * (moebius d)) * (moebius (d / ℓ)) := by rw [hsqd, one_mul]
        _ = (moebius d) * ((moebius d) * (moebius (d / ℓ))) := by ring
        _ = (moebius d : ℤ) * (moebius ℓ : ℤ) := by rw [hkey]
    rw [hfilter, Finset.sum_congr rfl hterm, ← Finset.mul_sum,
      Erdos287.PostBalanced7Pro.sum_moebius_divisors]
    by_cases hc : Nat.Coprime d H
    · have : Nat.gcd d (rad H) = 1 := (gcd_rad_eq_one_iff hH).2 hc
      rw [this, if_pos rfl, if_pos hc, mul_one]
    · have hne : Nat.gcd d (rad H) ≠ 1 := fun hcon => hc ((gcd_rad_eq_one_iff hH).1 hcon)
      rw [if_neg hne, if_neg hc, mul_zero]
  · -- non-squarefree `d`: every term vanishes, and so does `μ(d)`
    have hzero : ∀ ℓ ∈ (rad H).divisors.filter
        (fun ℓ => ℓ ∣ d ∧ Nat.Coprime (d / ℓ) ℓ), (moebius (d / ℓ) : ℤ) = 0 := by
      intro ℓ hℓ
      rw [Finset.mem_filter, Nat.mem_divisors] at hℓ
      obtain ⟨⟨hℓrad, -⟩, hℓd, hcop⟩ := hℓ
      have hℓsq : Squarefree ℓ := squarefree_of_dvd_rad hℓrad
      have hnotsq : ¬ Squarefree (d / ℓ) := by
        intro hdl
        refine hsq ?_
        have : d = ℓ * (d / ℓ) := (Nat.mul_div_cancel' hℓd).symm
        rw [this]
        exact (Nat.squarefree_mul_iff.2 ⟨hcop.symm, hℓsq, hdl⟩)
      exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnotsq
    rw [Finset.sum_eq_zero hzero, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    simp

/-! ## §1.3  The exact harmonic-twist expansion -/

/-- The inner twisted profile
`∑_{1 ≤ e ≤ ⌊T/ℓ⌋, gcd(e,ℓ) = 1} μ(e)/e · Ψ(ℓe/Δ)`. -/
def twistInner (l D T : ℕ) (Psi : ℚ → ℚ) : ℚ :=
  ∑ e ∈ Finset.Icc 1 (T / l),
    if Nat.Coprime e l then (moebius e : ℚ) / e * Psi (((l * e : ℕ) : ℚ) / D) else 0

/-- Reindexing `d = ℓe`: the inner twisted profile as a sum over the multiples of `ℓ`. -/
theorem twistInner_reindex {l : ℕ} (hl : l ≠ 0) (D T : ℕ) (Psi : ℚ → ℚ) :
    (1 / (l : ℚ)) * twistInner l D T Psi
      = ∑ d ∈ Finset.Icc 1 T,
          if l ∣ d then
            (if Nat.Coprime (d / l) l then
              (moebius (d / l) : ℚ) / d * Psi ((d : ℚ) / D) else 0)
          else 0 := by
  classical
  have hlpos : 0 < l := Nat.pos_of_ne_zero hl
  have hlq : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hl
  rw [twistInner, Finset.mul_sum, ← Finset.sum_filter]
  refine (Finset.sum_nbij' (i := fun d => d / l) (j := fun e => l * e) ?_ ?_ ?_ ?_ ?_).symm
  · intro d hd
    rw [Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨h1, h2⟩, hdvd⟩ := hd
    rw [Finset.mem_Icc]
    exact ⟨(Nat.one_le_div_iff hlpos).2 (Nat.le_of_dvd (by omega) hdvd),
      Nat.div_le_div_right h2⟩
  · intro e he
    rw [Finset.mem_Icc] at he
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨e, rfl⟩⟩
    · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hl (by omega))
    · show l * e ≤ T
      rw [mul_comm]
      exact (Nat.le_div_iff_mul_le hlpos).1 he.2
  · intro d hd
    rw [Finset.mem_filter] at hd
    exact Nat.mul_div_cancel' hd.2
  · intro e _
    exact Nat.mul_div_cancel_left e hlpos
  · intro d hd
    have hmem := hd
    rw [Finset.mem_filter, Finset.mem_Icc] at hmem
    obtain ⟨⟨hd1, -⟩, hdvd⟩ := hmem
    have hd0 : d ≠ 0 := by omega
    by_cases hc : Nat.Coprime (d / l) l
    · rw [if_pos hc, if_pos hc]
      have hml : (l * (d / l) : ℕ) = d := Nat.mul_div_cancel' hdvd
      have hdlne : d / l ≠ 0 := by
        intro hcon
        rw [hcon, mul_zero] at hml
        exact hd0 hml.symm
      have hdlq : ((d / l : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hdlne
      have hdq : ((d : ℕ) : ℚ) = (l : ℚ) * ((d / l : ℕ) : ℚ) := by
        rw [← Nat.cast_mul, hml]
      rw [hml, hdq]
      field_simp
    · rw [if_neg hc, if_neg hc, mul_zero]

/-- **`DET1-LOCALPROFILE-HARMONIC-TWISTS45`, algebraic core.**  `LEAN_PROVED`.

The exact finite harmonic-twist expansion of the repository's local profile:

```
m_{g,b}(Δ) = ∑_{ℓ ∣ rad(2bg)} (1/ℓ) ∑_{1 ≤ e ≤ ⌊T/ℓ⌋, gcd(e,ℓ)=1} μ(e)/e · Ψ(ℓe/Δ).
```

Everything is a finite sum over explicit `Finset`s; no analytic cost estimate is claimed. -/
theorem mProfile_harmonic_twist_expansion {g b : ℕ} (hg : g ≠ 0) (hb : b ≠ 0) (D T : ℕ)
    (Psi : ℚ → ℚ) :
    mProfile g b D Psi T
      = ∑ l ∈ (rad (2 * b * g)).divisors, (1 / (l : ℚ)) * twistInner l D T Psi := by
  classical
  have hH : 2 * b * g ≠ 0 := by positivity
  have hswap : ∑ l ∈ (rad (2 * b * g)).divisors, (1 / (l : ℚ)) * twistInner l D T Psi
      = ∑ d ∈ Finset.Icc 1 T, ∑ l ∈ (rad (2 * b * g)).divisors,
          (if l ∣ d then
            (if Nat.Coprime (d / l) l then
              (moebius (d / l) : ℚ) / d * Psi ((d : ℚ) / D) else 0)
          else 0) := by
    rw [Finset.sum_comm.symm]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [Nat.mem_divisors] at hl
    have hl0 : l ≠ 0 := by
      rintro rfl
      exact (rad_ne_zero (2 * b * g)) (Nat.eq_zero_of_zero_dvd hl.1)
    exact twistInner_reindex hl0 D T Psi
  rw [hswap, mProfile]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.mem_Icc] at hd
  have hd0 : d ≠ 0 := by omega
  have hpoint : ∑ l ∈ (rad (2 * b * g)).divisors,
      (if l ∣ d then
        (if Nat.Coprime (d / l) l then
          (moebius (d / l) : ℚ) / d * Psi ((d : ℚ) / D) else 0)
      else 0)
      = (∑ l ∈ (rad (2 * b * g)).divisors.filter (fun l => l ∣ d ∧ Nat.Coprime (d / l) l),
          (moebius (d / l) : ℚ)) * (Psi ((d : ℚ) / D) / d) := by
    calc ∑ l ∈ (rad (2 * b * g)).divisors,
          (if l ∣ d then
            (if Nat.Coprime (d / l) l then
              (moebius (d / l) : ℚ) / d * Psi ((d : ℚ) / D) else 0)
          else 0)
        = ∑ l ∈ (rad (2 * b * g)).divisors,
            (if (l ∣ d ∧ Nat.Coprime (d / l) l) then
              (moebius (d / l) : ℚ) * (Psi ((d : ℚ) / D) / d) else 0) := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          by_cases h1 : l ∣ d
          · by_cases h2 : Nat.Coprime (d / l) l
            · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]; ring
            · rw [if_pos h1, if_neg h2, if_neg (fun h : l ∣ d ∧ Nat.Coprime (d / l) l => h2 h.2)]
          · rw [if_neg h1, if_neg (fun h : l ∣ d ∧ Nat.Coprime (d / l) l => h1 h.1)]
      _ = ∑ l ∈ (rad (2 * b * g)).divisors.filter
            (fun l => l ∣ d ∧ Nat.Coprime (d / l) l),
              (moebius (d / l) : ℚ) * (Psi ((d : ℚ) / D) / d) := (Finset.sum_filter _ _).symm
      _ = (∑ l ∈ (rad (2 * b * g)).divisors.filter
            (fun l => l ∣ d ∧ Nat.Coprime (d / l) l), (moebius (d / l) : ℚ))
              * (Psi ((d : ℚ) / D) / d) := (Finset.sum_mul _ _ _).symm
  rw [hpoint]
  have hkey : (∑ l ∈ (rad (2 * b * g)).divisors.filter
      (fun l => l ∣ d ∧ Nat.Coprime (d / l) l), (moebius (d / l) : ℚ))
      = if Nat.Coprime d (2 * b * g) then (moebius d : ℚ) else 0 := by
    have hz := moebius_coprime_twist_sum (H := 2 * b * g) (d := d) hH
    have hcast := congrArg (fun z : ℤ => (z : ℚ)) hz
    push_cast at hcast
    simpa using hcast
  rw [hkey]
  by_cases hc : Nat.Coprime d (2 * b * g)
  · rw [if_pos hc, if_pos hc]
    ring
  · rw [if_neg hc, if_neg hc, zero_mul]

end LocalProfileHarmonic
end Erdos287
