import Mathlib
import RequestProject.CurrentProgramme.SharedG0UnitSectorGcd

/-!
# Averaged `b`-pair `gcd` router, finite core — Erdős #287, SHARED-g₀ REPAIR Δ, §5

**Finite combinatorics / exact integer algebra.**  No asymptotic notation, no `O`-symbols,
no analytic input.

The averaged `b`-pair router needs, after the unit-sector reduction of §4
(`sharedGcd_reciprocalDiff_eq_originalDiff`), a bound for

```
∑_{b₁,b₂ < B} gcd(g₀, b₁ - b₂).
```

The chain proved here is entirely exact:

* `gcd_eq_sum_totient_divisors` — `gcd(g₀,n) = ∑_{d ∣ g₀, d ∣ n} φ(d)`;
* `int_gcd_eq_sum_totient_divisors` — the same with an integer second argument;
* `pairCountCongruentModulo_le` — the exact interval count
  `#{(b₁,b₂) ∈ [0,B)² : d ∣ b₁-b₂} ≤ B·(⌊B/d⌋ + 1)`, with `⌊·⌋` the literal `Nat` division;
* `bpair_gcd_sum_le_divisorCount` — the finite precursor
  `∑_{b₁,b₂ < B} gcd(g₀,b₁-b₂) ≤ B²·τ(g₀) + B·g₀`, using `∑_{d ∣ g₀} φ(d) = g₀`.

Research status: `DET1-SHAREDG0-BPAIR-AVERAGED45 : FORMAL FINITE CORE PASS.`  The downstream
analytic large-`g₀` closure is **not** claimed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators

namespace Erdos287
namespace SharedG0BPair

/-! ## §5.1  `gcd` as a totient divisor sum -/

/-- **`gcd(g₀,n) = ∑_{d ∣ g₀, d ∣ n} φ(d)`.**  `LEAN_PROVED`. -/
theorem gcd_eq_sum_totient_divisors {g0 : ℕ} (hg0 : 0 < g0) (n : ℕ) :
    Nat.gcd g0 n = ∑ d ∈ g0.divisors.filter (fun d => d ∣ n), Nat.totient d := by
  have hdiv : (Nat.gcd g0 n).divisors = g0.divisors.filter (fun d => d ∣ n) := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, _⟩
      exact ⟨⟨h1, hg0.ne'⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩
      refine ⟨⟨h1, h2⟩, ?_⟩
      exact Nat.gcd_ne_zero_left hg0.ne'
  rw [← hdiv, Nat.sum_totient]

/-- The integer-difference form used by the `b`-pair router. -/
theorem int_gcd_eq_sum_totient_divisors {g0 : ℕ} (hg0 : 0 < g0) (n : ℤ) :
    Int.gcd (g0 : ℤ) n
      = ∑ d ∈ g0.divisors.filter (fun d : ℕ => ((d : ℤ) ∣ n)), Nat.totient d := by
  classical
  rw [Int.gcd_eq_natAbs, Int.natAbs_natCast, gcd_eq_sum_totient_divisors hg0 n.natAbs]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  refine Finset.filter_congr ?_
  intro d _
  simp [Int.natCast_dvd]

/-! ## §5.2  The exact interval pair count -/

/-- The number of pairs `(b₁,b₂) ∈ [0,B)²` congruent modulo `d`. -/
def pairCountCongruentModulo (d B : ℕ) : ℕ :=
  ((Finset.range B ×ˢ Finset.range B).filter
    (fun p => (d : ℤ) ∣ ((p.1 : ℤ) - (p.2 : ℤ)))).card

/-- **Exact interval count.**  `LEAN_PROVED`.

```
#{(b₁,b₂) ∈ [0,B)² : b₁ ≡ b₂ (mod d)} ≤ B · (⌊B/d⌋ + 1),
```

with `⌊B/d⌋` the literal `Nat` division — the exact-floor form of the research display
`B²/d + O(B)`. -/
theorem pairCountCongruentModulo_le (d B : ℕ) :
    pairCountCongruentModulo d B ≤ B * (B / d + 1) := by
  classical
  have hmaps : ∀ p ∈ (Finset.range B ×ˢ Finset.range B).filter
      (fun p => (d : ℤ) ∣ ((p.1 : ℤ) - (p.2 : ℤ))),
      (p.1, p.2 / d) ∈ Finset.range B ×ˢ Finset.range (B / d + 1) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    refine ⟨hp.1.1, ?_⟩
    have : p.2 / d ≤ B / d := Nat.div_le_div_right (le_of_lt hp.1.2)
    omega
  have hinj : ∀ p ∈ (Finset.range B ×ˢ Finset.range B).filter
      (fun p => (d : ℤ) ∣ ((p.1 : ℤ) - (p.2 : ℤ))),
      ∀ q ∈ (Finset.range B ×ˢ Finset.range B).filter
        (fun p => (d : ℤ) ∣ ((p.1 : ℤ) - (p.2 : ℤ))),
      (p.1, p.2 / d) = (q.1, q.2 / d) → p = q := by
    intro p hp q hq heq
    rw [Finset.mem_filter] at hp hq
    have h1 : p.1 = q.1 := (Prod.ext_iff.mp heq).1
    have hdiv : p.2 / d = q.2 / d := (Prod.ext_iff.mp heq).2
    have hmp : p.1 % d = p.2 % d := by
      have := hp.2
      have hmod : (p.2 : ℕ) ≡ (p.1 : ℕ) [MOD d] := (Nat.modEq_iff_dvd).2 (by simpa using this)
      exact hmod.symm
    have hmq : q.1 % d = q.2 % d := by
      have := hq.2
      have hmod : (q.2 : ℕ) ≡ (q.1 : ℕ) [MOD d] := (Nat.modEq_iff_dvd).2 (by simpa using this)
      exact hmod.symm
    have h2 : p.2 = q.2 := by
      have e1 : d * (p.2 / d) + p.2 % d = p.2 := Nat.div_add_mod _ _
      have e2 : d * (q.2 / d) + q.2 % d = q.2 := Nat.div_add_mod _ _
      rw [hdiv] at e1
      rw [h1] at hmp
      omega
    exact Prod.ext h1 h2
  have hcard := Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => (p.1, p.2 / d))
    hmaps (fun p hp q hq h => hinj p hp q hq h)
  simpa [pairCountCongruentModulo, Finset.card_product] using hcard

/-! ## §5.3  The averaged `b`-pair finite precursor -/

/-- **`DET1-SHAREDG0-BPAIR-AVERAGED45`, finite precursor.**  `LEAN_PROVED`.

```
∑_{b₁,b₂ < B} gcd(g₀, b₁-b₂)  ≤  B²·τ(g₀) + B·g₀,
```

obtained from `gcd = ∑_{d ∣ g₀, d ∣ n} φ(d)`, the exact interval count of §5.2 and the exact
identity `∑_{d ∣ g₀} φ(d) = g₀`.  Nothing asymptotic is asserted. -/
theorem bpair_gcd_sum_le_divisorCount {g0 : ℕ} (hg0 : 0 < g0) (B : ℕ) :
    ∑ p ∈ Finset.range B ×ˢ Finset.range B, Int.gcd (g0 : ℤ) ((p.1 : ℤ) - (p.2 : ℤ))
      ≤ B ^ 2 * g0.divisors.card + B * g0 := by
  classical
  have hpoint : ∀ p : ℕ × ℕ, Int.gcd (g0 : ℤ) ((p.1 : ℤ) - (p.2 : ℤ))
      = ∑ d ∈ g0.divisors,
          (if ((d : ℤ) ∣ ((p.1 : ℤ) - (p.2 : ℤ))) then Nat.totient d else 0) := by
    intro p
    rw [int_gcd_eq_sum_totient_divisors hg0, Finset.sum_filter]
  have hstep1 : ∑ p ∈ Finset.range B ×ˢ Finset.range B,
      Int.gcd (g0 : ℤ) ((p.1 : ℤ) - (p.2 : ℤ))
      = ∑ d ∈ g0.divisors, ∑ p ∈ Finset.range B ×ˢ Finset.range B,
          (if ((d : ℤ) ∣ ((p.1 : ℤ) - (p.2 : ℤ))) then Nat.totient d else 0) := by
    rw [Finset.sum_congr rfl (fun p _ => hpoint p), Finset.sum_comm]
  have hstep2 : ∀ d ∈ g0.divisors,
      ∑ p ∈ Finset.range B ×ˢ Finset.range B,
        (if ((d : ℤ) ∣ ((p.1 : ℤ) - (p.2 : ℤ))) then Nat.totient d else 0)
        = Nat.totient d * pairCountCongruentModulo d B := by
    intro d _
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, pairCountCongruentModulo,
      mul_comm]
  have hstep3 : ∀ d ∈ g0.divisors,
      Nat.totient d * pairCountCongruentModulo d B ≤ B ^ 2 + Nat.totient d * B := by
    intro d _
    have hcount := pairCountCongruentModulo_le d B
    have hphi : Nat.totient d ≤ d := Nat.totient_le d
    have hkey : Nat.totient d * (B / d) ≤ B := by
      calc Nat.totient d * (B / d) ≤ d * (B / d) := Nat.mul_le_mul_right _ hphi
        _ ≤ B := Nat.mul_div_le B d
    calc Nat.totient d * pairCountCongruentModulo d B
        ≤ Nat.totient d * (B * (B / d + 1)) := Nat.mul_le_mul_left _ hcount
      _ = (Nat.totient d * (B / d)) * B + Nat.totient d * B := by ring
      _ ≤ B * B + Nat.totient d * B := by
          exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hkey) _
      _ = B ^ 2 + Nat.totient d * B := by ring
  calc ∑ p ∈ Finset.range B ×ˢ Finset.range B, Int.gcd (g0 : ℤ) ((p.1 : ℤ) - (p.2 : ℤ))
      = ∑ d ∈ g0.divisors, Nat.totient d * pairCountCongruentModulo d B := by
        rw [hstep1]; exact Finset.sum_congr rfl hstep2
    _ ≤ ∑ d ∈ g0.divisors, (B ^ 2 + Nat.totient d * B) := Finset.sum_le_sum hstep3
    _ = B ^ 2 * g0.divisors.card + (∑ d ∈ g0.divisors, Nat.totient d) * B := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_mul]
        ring
    _ = B ^ 2 * g0.divisors.card + B * g0 := by
        rw [Nat.sum_totient]; ring

end SharedG0BPair
end Erdos287
