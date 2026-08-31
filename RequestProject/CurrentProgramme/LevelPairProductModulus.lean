import Mathlib
import RequestProject.CurrentProgramme.PrimitiveRamanujanAlgebra
import RequestProject.CurrentProgramme.PrimitiveReducedDenominator

/-!
# Product-modulus Möbius sign compression — Erdős #287, ONE-LEVEL MÖBIUS Δ, §§1–3, §5

**Exact integer / rational algebra only.**  Nothing analytic, nothing asymptotic.  No existing
module is edited; this file is append-only and imports the banked shared-`g₀` algebra.

Setting.  A *level pair* is

```
g₁ = g₀ r₁,   g₂ = g₀ r₂,   gcd(r₁,r₂) = 1,   gcd(g₀, r₁r₂) = 1,
n  = r₁ r₂,
D  = t₁ r₂ - t₂ r₁.
```

Banked here:

* `moebius_levelPair_compress` — `μ(g₁)μ(g₂) = μ(r₁)μ(r₂)` for squarefree `g₀`;
* `moebius_levelPair_eq_moebius_n` — `μ(g₁)μ(g₂) = μ(n)`;
* `lcm_levelPair_eq` — `lcm(g₁,g₂) = g₀ n`
  (`DET1-LEVELPAIR-PRODUCTMOD-SIGN45`);
* `gcd_D_n_eq_one` — `gcd(D,n) = 1` proved **directly** from primitivity, not through the
  banked `gcd(D,Λ) ∣ g₀`, which is also re-exported as `gcd_D_lambda_dvd_g0_reexport`
  (`DET1-D-N-COPRIME45`);
* `unitary_split_dvd`, `unitary_split_coprime`, `levelPair_norm_eq` — the `(g₀,n,r)`
  reparametrisation and `1/(g₁g₂) = 1/(g₀²n)`;
* `levelPair_divisorSplit`, `levelPair_reindex_fixed_n`, `levelPair_reindex` — the exact finite
  reindexing of `∑_{g₁,g₂} μ(g₁)μ(g₂)/(g₁g₂) K(g₁,g₂)` into
  `∑_{g₀} 1/g₀² ∑_n μ(n)/n ∑_{r ∣ n} K(g₀r, g₀(n/r))`
  (`DET1-LEVELPAIR-N-DIVISORSPLIT45`);
* `fareyDifference_eq_D_div_g0n` — `t₁/g₁ - t₂/g₂ = D/(g₀n)`, so the additive/Farey datum
  depends only on `(g₀,n,D)` and not on the unitary divisor split `r ∣ n`.

No asymptotic dyadic range is formalised, and no analytic property of `Φ_A` is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators
open ArithmeticFunction

namespace Erdos287
namespace LevelPairProduct

/-! ## §1  Product-modulus Möbius sign compression -/

/-- **`DET1-LEVELPAIR-PRODUCTMOD-SIGN45`, step 1.**  `LEAN_PROVED`.

For squarefree `g₀` coprime to both cofactors,
`μ(g₀r₁)·μ(g₀r₂) = μ(r₁)·μ(r₂)`: the shared part contributes `μ(g₀)² = 1`. -/
theorem moebius_levelPair_compress {g0 r1 r2 : ℕ} (hg0 : Squarefree g0)
    (h1 : Nat.Coprime g0 r1) (h2 : Nat.Coprime g0 r2) :
    (moebius (g0 * r1) : ℤ) * (moebius (g0 * r2) : ℤ)
      = (moebius r1 : ℤ) * (moebius r2 : ℤ) := by
  rw [isMultiplicative_moebius.map_mul_of_coprime h1,
    isMultiplicative_moebius.map_mul_of_coprime h2]
  have hsq : (moebius g0 : ℤ) ^ 2 = 1 := by exact_mod_cast moebius_sq_eq_one_of_squarefree hg0
  calc (moebius g0 : ℤ) * moebius r1 * ((moebius g0 : ℤ) * moebius r2)
      = (moebius g0 : ℤ) ^ 2 * ((moebius r1 : ℤ) * moebius r2) := by ring
    _ = (moebius r1 : ℤ) * moebius r2 := by rw [hsq, one_mul]

/-- **`DET1-LEVELPAIR-PRODUCTMOD-SIGN45`, step 2.**  `LEAN_PROVED`.

With `n = r₁r₂` and `gcd(r₁,r₂) = 1`, the compressed sign is a single Möbius value:
`μ(g₁)μ(g₂) = μ(n)`. -/
theorem moebius_levelPair_eq_moebius_n {g0 r1 r2 : ℕ} (hg0 : Squarefree g0)
    (h1 : Nat.Coprime g0 r1) (h2 : Nat.Coprime g0 r2) (hr : Nat.Coprime r1 r2) :
    (moebius (g0 * r1) : ℤ) * (moebius (g0 * r2) : ℤ) = (moebius (r1 * r2) : ℤ) := by
  rw [moebius_levelPair_compress hg0 h1 h2, isMultiplicative_moebius.map_mul_of_coprime hr]

/-- **`DET1-LEVELPAIR-PRODUCTMOD-SIGN45`, step 3.**  `LEAN_PROVED`.

`lcm(g₀r₁, g₀r₂) = g₀ · n` with `n = r₁r₂`. -/
theorem lcm_levelPair_eq {g0 r1 r2 : ℕ} (hg0 : 0 < g0) (hr : Nat.Coprime r1 r2) :
    Nat.lcm (g0 * r1) (g0 * r2) = g0 * (r1 * r2) := by
  rw [Erdos287.ReducedDenominator.lcm_sharedG0_eq hg0 hr, mul_assoc]

/-! ## §2  `gcd(D,n) = 1` -/

/-- **`DET1-D-N-COPRIME45`.**  `LEAN_PROVED`.

Directly from primitivity `gcd(t₁,g₁) = gcd(t₂,g₂) = 1`: with `D = t₁r₂ - t₂r₁` and
`n = r₁r₂`,

```
gcd(D, n) = 1.
```

The proof is prime-by-prime through the two banked coprimality lemmas and does **not** pass
through `gcd(D,Λ) ∣ g₀`. -/
theorem gcd_D_n_eq_one {g0 r1 r2 : ℕ} {t1 t2 : ℤ} (hcop : Nat.Coprime r1 r2)
    (h1 : Int.gcd t1 ((g0 : ℤ) * r1) = 1) (h2 : Int.gcd t2 ((g0 : ℤ) * r2) = 1) :
    Int.gcd (t1 * r2 - t2 * r1) ((r1 * r2 : ℕ) : ℤ) = 1 := by
  set d : ℕ := Int.gcd (t1 * (r2 : ℤ) - t2 * r1) ((r1 * r2 : ℕ) : ℤ) with hd
  have hdvd : d ∣ r1 * r2 := by
    have : (d : ℤ) ∣ ((r1 * r2 : ℕ) : ℤ) := Int.gcd_dvd_right _ _
    exact_mod_cast this
  have hc1 : Nat.Coprime d r1 :=
    Erdos287.ReducedDenominator.gcd_D_lambda_coprime_left hcop h1 (r1 * r2)
  have hc2 : Nat.Coprime d r2 :=
    Erdos287.ReducedDenominator.gcd_D_lambda_coprime_right hcop h2 (r1 * r2)
  have hstep : d ∣ r2 := hc1.dvd_of_dvd_mul_left hdvd
  exact Nat.Coprime.eq_one_of_dvd hc2 hstep

/-- Re-export of the banked `gcd(D,Λ) ∣ g₀` for the record; the `gcd(D,n)=1` statement above
is proved independently of it. -/
theorem gcd_D_lambda_dvd_g0_reexport {g0 r1 r2 : ℕ} {t1 t2 : ℤ} (hcop : Nat.Coprime r1 r2)
    (h1 : Int.gcd t1 ((g0 : ℤ) * r1) = 1) (h2 : Int.gcd t2 ((g0 : ℤ) * r2) = 1) :
    Int.gcd (t1 * r2 - t2 * r1) ((g0 * r1 * r2 : ℕ) : ℤ) ∣ g0 :=
  Erdos287.ReducedDenominator.gcd_D_lambda_dvd_g0 hcop h1 h2

/-! ## §3  The `(g₀,n,r)` level-pair reparametrisation -/

/-- For squarefree `n` every divisor `r ∣ n` is a *unitary* divisor: `gcd(r, n/r) = 1`. -/
theorem unitary_split_coprime {n r : ℕ} (hn : Squarefree n) (hr : r ∣ n) :
    Nat.Coprime r (n / r) :=
  Erdos287.PrimitiveRamanujan.coprime_div_of_squarefree n r hn hr

/-- The split recomposes: `r · (n/r) = n`. -/
theorem unitary_split_dvd {n r : ℕ} (hr : r ∣ n) : r * (n / r) = n :=
  Nat.mul_div_cancel' hr

/-- **Normalisation.**  `LEAN_PROVED`.  `1/(g₁g₂) = 1/(g₀² n)` with `n = r₁r₂`. -/
theorem levelPair_norm_eq (g0 r1 r2 : ℕ) :
    (1 : ℚ) / ((g0 * r1 : ℕ) * (g0 * r2 : ℕ)) = 1 / ((g0 : ℚ) ^ 2 * ((r1 * r2 : ℕ) : ℚ)) := by
  push_cast
  ring_nf

/-- The ordered level pairs over a fixed `n` are exactly the divisor splits of `n`. -/
theorem levelPair_divisorSplit {M : Type*} [AddCommMonoid M] (n g0 : ℕ) (K : ℕ → ℕ → M) :
    ∑ p ∈ n.divisorsAntidiagonal, K (g0 * p.1) (g0 * p.2)
      = ∑ r ∈ n.divisors, K (g0 * r) (g0 * (n / r)) :=
  Nat.sum_divisorsAntidiagonal (fun a b => K (g0 * a) (g0 * b))

/-- **`DET1-LEVELPAIR-N-DIVISORSPLIT45`, fixed `n`.**  `LEAN_PROVED`.

For squarefree `n` coprime to squarefree `g₀`, the level-pair sum over ordered factorisations
`r₁r₂ = n` compresses to a single Möbius weight times the divisor sum:

```
∑_{r₁r₂ = n} μ(g₀r₁)μ(g₀r₂)/((g₀r₁)(g₀r₂)) K(g₀r₁, g₀r₂)
  = (1/g₀²)·(μ(n)/n)·∑_{r ∣ n} K(g₀r, g₀(n/r)).
``` -/
theorem levelPair_reindex_fixed_n {g0 n : ℕ} (hg0 : Squarefree g0) (hg0pos : 0 < g0)
    (hn : Squarefree n) (hcop : Nat.Coprime g0 n) (K : ℕ → ℕ → ℂ) :
    ∑ p ∈ n.divisorsAntidiagonal,
        ((moebius (g0 * p.1) : ℤ) : ℂ) * ((moebius (g0 * p.2) : ℤ) : ℂ)
          / (((g0 * p.1 : ℕ) : ℂ) * ((g0 * p.2 : ℕ) : ℂ)) * K (g0 * p.1) (g0 * p.2)
      = (1 / (g0 : ℂ) ^ 2) * (((moebius n : ℤ) : ℂ) / (n : ℂ))
          * ∑ r ∈ n.divisors, K (g0 * r) (g0 * (n / r)) := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn.ne_zero
  have hg0C : ((g0 : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hg0pos.ne'
  have hnC : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hnpos.ne'
  have key : ∀ p ∈ n.divisorsAntidiagonal,
      ((moebius (g0 * p.1) : ℤ) : ℂ) * ((moebius (g0 * p.2) : ℤ) : ℂ)
          / (((g0 * p.1 : ℕ) : ℂ) * ((g0 * p.2 : ℕ) : ℂ)) * K (g0 * p.1) (g0 * p.2)
        = (1 / (g0 : ℂ) ^ 2) * (((moebius n : ℤ) : ℂ) / (n : ℂ)) * K (g0 * p.1) (g0 * p.2) := by
    intro p hp
    rw [Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨hprod, hne⟩ := hp
    have hr1 : p.1 ∣ n := ⟨p.2, hprod.symm⟩
    have hr2 : p.2 ∣ n := ⟨p.1, by rw [← hprod]; ring⟩
    have hcop12 : Nat.Coprime p.1 p.2 := by
      have := hn
      rw [← hprod] at this
      exact (Nat.squarefree_mul_iff.1 this).1
    have hc1 : Nat.Coprime g0 p.1 := Nat.Coprime.coprime_dvd_right hr1 hcop
    have hc2 : Nat.Coprime g0 p.2 := Nat.Coprime.coprime_dvd_right hr2 hcop
    have hmu : (moebius (g0 * p.1) : ℤ) * (moebius (g0 * p.2) : ℤ) = (moebius n : ℤ) := by
      rw [moebius_levelPair_eq_moebius_n hg0 hc1 hc2 hcop12, hprod]
    have hmuC : ((moebius (g0 * p.1) : ℤ) : ℂ) * ((moebius (g0 * p.2) : ℤ) : ℂ)
        = ((moebius n : ℤ) : ℂ) := by exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) hmu
    have hden : (((g0 * p.1 : ℕ) : ℂ) * ((g0 * p.2 : ℕ) : ℂ)) = (g0 : ℂ) ^ 2 * (n : ℂ) := by
      have : ((p.1 : ℂ)) * ((p.2 : ℂ)) = (n : ℂ) := by
        exact_mod_cast congrArg (fun m : ℕ => (m : ℂ)) hprod
      push_cast
      rw [← this]
      ring
    rw [hmuC, hden]
    field_simp
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
  congr 1
  exact levelPair_divisorSplit n g0 K

/-- **`DET1-LEVELPAIR-N-DIVISORSPLIT45`.**  `LEAN_PROVED`.

The full finite reindexing: summed over any finite family of admissible shared parts `g₀` and
product moduli `n`,

```
∑_{g₀} ∑_{n} ∑_{r₁r₂=n} μ(g₁)μ(g₂)/(g₁g₂) K(g₁,g₂)
  = ∑_{g₀} 1/g₀² ∑_n μ(n)/n ∑_{r ∣ n} K(g₀r, g₀(n/r)).
```

No dyadic or asymptotic range is involved: `G` and `N` are arbitrary finsets subject only to
the stated squarefreeness / coprimality hypotheses. -/
theorem levelPair_reindex {G N : Finset ℕ}
    (hG : ∀ g0 ∈ G, Squarefree g0 ∧ 0 < g0) (hN : ∀ n ∈ N, Squarefree n)
    (hcop : ∀ g0 ∈ G, ∀ n ∈ N, Nat.Coprime g0 n) (K : ℕ → ℕ → ℂ) :
    ∑ g0 ∈ G, ∑ n ∈ N, ∑ p ∈ n.divisorsAntidiagonal,
        ((moebius (g0 * p.1) : ℤ) : ℂ) * ((moebius (g0 * p.2) : ℤ) : ℂ)
          / (((g0 * p.1 : ℕ) : ℂ) * ((g0 * p.2 : ℕ) : ℂ)) * K (g0 * p.1) (g0 * p.2)
      = ∑ g0 ∈ G, (1 / (g0 : ℂ) ^ 2) * ∑ n ∈ N, (((moebius n : ℤ) : ℂ) / (n : ℂ))
          * ∑ r ∈ n.divisors, K (g0 * r) (g0 * (n / r)) := by
  refine Finset.sum_congr rfl ?_
  intro g0 hg0
  obtain ⟨hsq, hpos⟩ := hG g0 hg0
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [levelPair_reindex_fixed_n hsq hpos (hN n hn) (hcop g0 hg0 n hn) K, mul_assoc]

/-! ## §5  The Farey kernel is independent of the divisor split -/

/-- **`fareyDifference_eq_D_div_g0n`.**  `LEAN_PROVED`.

```
t₁/g₁ - t₂/g₂ = D/(g₀n),   D = t₁r₂ - t₂r₁,   n = r₁r₂.
```

Consequently the additive/Farey datum of a level pair depends only on `(g₀, n, D)` and not on
the unitary divisor split `r ∣ n`.  No analytic property of `Φ_A` is asserted. -/
theorem fareyDifference_eq_D_div_g0n {g0 r1 r2 : ℕ} (hg0 : 0 < g0) (hr1 : 0 < r1) (hr2 : 0 < r2)
    (t1 t2 : ℤ) :
    (t1 : ℚ) / ((g0 * r1 : ℕ) : ℚ) - (t2 : ℚ) / ((g0 * r2 : ℕ) : ℚ)
      = ((t1 * r2 - t2 * r1 : ℤ) : ℚ) / ((g0 : ℚ) * ((r1 * r2 : ℕ) : ℚ)) := by
  have h0 : ((g0 : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hg0.ne'
  have h1 : ((r1 : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hr1.ne'
  have h2 : ((r2 : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hr2.ne'
  push_cast
  field_simp

/-- The Farey datum is literally independent of which unitary divisor split of `n` produced the
level pair: two splits `r ∣ n` and `r' ∣ n` with the same `(g₀,n,D)` give the same difference. -/
theorem fareyDifference_split_invariant {g0 n : ℕ} (hg0 : 0 < g0) (hn : 0 < n) (D : ℤ)
    {r r' : ℕ} (hr : r ∣ n) (hr' : r' ∣ n) (hrpos : 0 < r) (hr'pos : 0 < r')
    {t1 t2 t1' t2' : ℤ}
    (hD : t1 * ((n / r : ℕ) : ℤ) - t2 * (r : ℤ) = D)
    (hD' : t1' * ((n / r' : ℕ) : ℤ) - t2' * (r' : ℤ) = D) :
    (t1 : ℚ) / ((g0 * r : ℕ) : ℚ) - (t2 : ℚ) / ((g0 * (n / r) : ℕ) : ℚ)
      = (t1' : ℚ) / ((g0 * r' : ℕ) : ℚ) - (t2' : ℚ) / ((g0 * (n / r') : ℕ) : ℚ) := by
  have hq : 0 < n / r := Nat.div_pos (Nat.le_of_dvd hn hr) hrpos
  have hq' : 0 < n / r' := Nat.div_pos (Nat.le_of_dvd hn hr') hr'pos
  rw [fareyDifference_eq_D_div_g0n hg0 hrpos hq t1 t2,
    fareyDifference_eq_D_div_g0n hg0 hr'pos hq' t1' t2', hD, hD',
    unitary_split_dvd hr, unitary_split_dvd hr']

end LevelPairProduct
end Erdos287
