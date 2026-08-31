import Mathlib
import RequestProject.CurrentProgramme.PrimitiveRamanujanAlgebra
import RequestProject.CurrentProgramme.ConductorSplitLargeSieve

/-!
# Primitive `t` / Ramanujan reassembly — Erdős #287, PRIMITIVE-LOCALPROFILE Δ, §B

Exact finite identities only; **no analytic estimate** appears in this file.

The representation loop of the reduction is

```
∑_{k d = n} μ(d) · 1_{gcd(2b,k) = 1} · 1_{gcd(b,d) = 1}
```

and the two branches actually used are proved here:

* `reassemblyBranch_of_coprime` — on the sector `gcd(2b, n) = 1` (the `r = 1`, `g = k`
  retention branch) both indicators are identically `1`, so the whole convolution collapses
  to `∑_{d ∣ n} μ(d)`, which vanishes unless `n = 1`: this is the `r > 1` cancellation.
* `moebius_properDivisors_sum` — for `n > 1`, `∑_{d ∣ n, d < n} μ(d) = -μ(n)`.

Compiled together with the Ramanujan normal form of §A these give the reassembly

```
μ(g)/g · c_g(N) = rawProgression(g,N) - additiveZeroMode(g,N),
```

`primitive_ramanujan_reassembly`, i.e. the loop returns exactly the raw progression minus
the additive zero mode.  This is a *representation loop*: it is an identity between two
descriptions of the same finite sum, and it is `FORMALLY VERIFIED; NOT FALSE`; it is not an
estimate and it does not by itself bound anything.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators
open ArithmeticFunction

namespace Erdos287
namespace PrimitiveReassembly

open Erdos287.PrimitiveRamanujan

/-! ## §B.1  The two Möbius branches -/

/-- **`r > 1` cancellation.**  For `n > 1`, `∑_{d ∣ n, d < n} μ(d) = -μ(n)`.

The underlying `∑_{d ∣ n} μ(d) = [n = 1]` is the repository's own
`Erdos287.PostBalanced7Pro.sum_moebius_divisors`. -/
theorem moebius_properDivisors_sum {n : ℕ} (hn : 1 < n) :
    ∑ d ∈ n.properDivisors, moebius d = - moebius n := by
  have hn0 : n ≠ 0 := by omega
  have hsplit : ∑ d ∈ n.divisors, moebius d
      = (∑ d ∈ n.properDivisors, moebius d) + moebius n := by
    rw [← Nat.insert_self_properDivisors hn0,
      Finset.sum_insert (by simp [Nat.mem_properDivisors])]
    ring
  rw [Erdos287.PostBalanced7Pro.sum_moebius_divisors n, if_neg (by omega)] at hsplit
  linarith [hsplit]

/-! ## §B.2  The reassembly convolution and its branches -/

/-- The literal representation-loop convolution

```
∑_{k d = n} μ(d) 1_{gcd(2b,k)=1} 1_{gcd(b,d)=1}.
```
-/
def reassemblyBranch (b n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, if Nat.Coprime (2 * b) (n / d) ∧ Nat.Coprime b d then moebius d else 0

/-- **The explicit branch used in the reduction.**  On the sector `gcd(2b,n) = 1` both
indicators are identically `1`, so the convolution equals `∑_{d ∣ n} μ(d)`; hence it is `1`
for `n = 1` and `0` for every `n > 1` — the `r > 1` cancellation leaving only `n = 1`. -/
theorem reassemblyBranch_of_coprime {b n : ℕ} (hcop : Nat.Coprime (2 * b) n) :
    reassemblyBranch b n = if n = 1 then 1 else 0 := by
  have hb : Nat.Coprime b n := Nat.Coprime.coprime_dvd_left ⟨2, by ring⟩ hcop
  have hall : ∀ d ∈ n.divisors,
      (if Nat.Coprime (2 * b) (n / d) ∧ Nat.Coprime b d then moebius d else 0) = moebius d := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    have h1 : Nat.Coprime (2 * b) (n / d) :=
      Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hd.1) hcop
    have h2 : Nat.Coprime b d := Nat.Coprime.coprime_dvd_right hd.1 hb
    rw [if_pos ⟨h1, h2⟩]
  rw [reassemblyBranch, Finset.sum_congr rfl hall,
    Erdos287.PostBalanced7Pro.sum_moebius_divisors n]

/-- `n = 1` is the surviving term. -/
theorem reassemblyBranch_one (b : ℕ) : reassemblyBranch b 1 = 1 := by
  simp [reassemblyBranch]

/-- Every `n > 1` on the coprime sector cancels. -/
theorem reassemblyBranch_eq_zero {b n : ℕ} (hn : 1 < n) (hcop : Nat.Coprime (2 * b) n) :
    reassemblyBranch b n = 0 := by
  rw [reassemblyBranch_of_coprime hcop, if_neg (by omega)]

/-! ## §B.3  Raw progression and additive zero mode -/

/-- The raw progression term: the `r = g`, `k = 1` divisor of the normal form. -/
noncomputable def rawProgression (g : ℕ) (N : ℤ) : ℂ :=
  if (g : ℤ) ∣ N then ((moebius g : ℤ) : ℂ) else 0

/-- The additive zero mode: all remaining divisors `r < g` of `gcd(g,N)`, with the sign of
the reduction. -/
noncomputable def additiveZeroMode (g : ℕ) (N : ℤ) : ℂ :=
  - ∑ r ∈ (Int.gcd (g : ℤ) N).divisors.erase g, ((moebius r : ℤ) : ℂ) / ((g / r : ℕ) : ℂ)

/-- **`DET1-PRIMITIVE-RAMANUJAN-REASSEMBLY45`.**  `REPRESENTATION LOOP; FORMALLY VERIFIED;
NOT FALSE.`

Complete primitive-`t` / Ramanujan reassembly on the squarefree sector returns exactly

```
raw progression − additive zero mode.
```
-/
theorem primitive_ramanujan_reassembly {g : ℕ} (hg : 0 < g) (hsq : Squarefree g) (N : ℤ) :
    ((moebius g : ℤ) : ℂ) / (g : ℂ) * ramanujan g N
      = rawProgression g N - additiveZeroMode g N := by
  rw [ramanujan_moebius_normalForm hg hsq N, rawProgression, additiveZeroMode, sub_neg_eq_add]
  by_cases hdvd : (g : ℤ) ∣ N
  · have hmem : g ∈ (Int.gcd (g : ℤ) N).divisors := by
      rw [Nat.mem_divisors]
      refine ⟨Int.dvd_gcd (dvd_refl ((g : ℤ))) hdvd, ?_⟩
      intro h
      have hg0 : (g : ℤ) = 0 := Int.eq_zero_of_gcd_eq_zero_left (by exact_mod_cast h)
      exact hg.ne' (by exact_mod_cast hg0)
    rw [if_pos hdvd, ← Finset.add_sum_erase _ _ hmem]
    congr 1
    rw [Nat.div_self hg]
    simp
  · have hnotmem : g ∉ (Int.gcd (g : ℤ) N).divisors := by
      intro hmem
      exact hdvd (dvd_trans (Int.natCast_dvd_natCast.2 (Nat.mem_divisors.1 hmem).1)
        (Int.gcd_dvd_right (g : ℤ) N))
    rw [if_neg hdvd, Finset.erase_eq_of_notMem hnotmem, zero_add]

end PrimitiveReassembly
end Erdos287
