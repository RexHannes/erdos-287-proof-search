import Mathlib

/-!
# Primitive `D`-frequency multiplicity — Erdős #287, PRIMITIVE-LOCALPROFILE Δ, §D

Exact integer algebra and an exact `Finset` cardinality bound.

Set `g₁ = g₀·r₁`, `g₂ = g₀·r₂` with `gcd(r₁,r₂) = 1`, and

```
D = t₁ r₂ - t₂ r₁.
```

* `dLine_solution_form` — every integer solution of `r₂ t₁ - r₁ t₂ = D` differs from a fixed
  one by `t₁ = t₁⁰ + r₁ u`, `t₂ = t₂⁰ + r₂ u`.
* `dSolutionSet_card_le` — **`DET1-PRIMITIVE-D-MULTIPLICITY45`**: inside the box
  `1 ≤ tᵢ ≤ gᵢ` the number of solutions is at most `g₀ + 1`.
  (The proof in fact gives the sharper `g₀`; the banked statement is the `g₀ + 1` of the
  reduction, and `dSolutionSet_card_le_g0` records the sharp form.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

namespace Erdos287
namespace PrimitiveD

/-! ## §D.1  The solution line -/

/-- **Solution form.**  With `gcd(r₁,r₂) = 1` and `r₁ ≠ 0`, any two solutions of
`r₂ t₁ - r₁ t₂ = D` differ by `(r₁ u, r₂ u)`. -/
theorem dLine_solution_form {r1 r2 t1 t2 t1' t2' D : ℤ} (hcop : IsCoprime r1 r2) (hr1 : r1 ≠ 0)
    (h : r2 * t1 - r1 * t2 = D) (h' : r2 * t1' - r1 * t2' = D) :
    ∃ u : ℤ, t1 = t1' + r1 * u ∧ t2 = t2' + r2 * u := by
  have hkey : r2 * (t1 - t1') = r1 * (t2 - t2') := by linarith
  have hdvd : r1 ∣ (t1 - t1') := by
    have h1 : r1 ∣ r2 * (t1 - t1') := ⟨t2 - t2', hkey⟩
    exact hcop.dvd_of_dvd_mul_left h1
  obtain ⟨u, hu⟩ := hdvd
  refine ⟨u, by linarith [hu], ?_⟩
  have h2 : r1 * (r2 * u) = r1 * (t2 - t2') := by
    rw [← hkey, hu]; ring
  have h3 : r2 * u = t2 - t2' := mul_left_cancel₀ hr1 h2
  linarith [h3]

/-! ## §D.2  The multiplicity count -/

/-- The set of solutions of `r₂ t₁ - r₁ t₂ = D` in the box `1 ≤ t₁ ≤ g₀r₁`,
`1 ≤ t₂ ≤ g₀r₂`. -/
def dSolutionSet (g0 r1 r2 : ℕ) (D : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (1 : ℤ) ((g0 : ℤ) * r1)) ×ˢ (Finset.Icc (1 : ℤ) ((g0 : ℤ) * r2))).filter
    (fun p => (r2 : ℤ) * p.1 - (r1 : ℤ) * p.2 = D)

/-- **Sharp multiplicity.**  At most `g₀` solutions in the box. -/
theorem dSolutionSet_card_le_g0 {g0 r1 r2 : ℕ} (hcop : Nat.Coprime r1 r2) (hr1 : 0 < r1)
    (D : ℤ) : (dSolutionSet g0 r1 r2 D).card ≤ g0 := by
  have hr1z : (0 : ℤ) < (r1 : ℤ) := by exact_mod_cast hr1
  have hcopz : IsCoprime ((r1 : ℤ)) ((r2 : ℤ)) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd_natCast_natCast] using hcop
  classical
  have hmaps : ∀ p ∈ dSolutionSet g0 r1 r2 D,
      (p.1 - 1) / (r1 : ℤ) ∈ Finset.Icc (0 : ℤ) ((g0 : ℤ) - 1) := by
    intro p hp
    rw [dSolutionSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_Icc] at hp
    obtain ⟨⟨⟨h1, h2⟩, -⟩, -⟩ := hp
    rw [Finset.mem_Icc]
    constructor
    · exact Int.ediv_nonneg (by linarith) (le_of_lt hr1z)
    · have hlt : (p.1 - 1) / (r1 : ℤ) < (g0 : ℤ) := by
        rw [Int.ediv_lt_iff_lt_mul hr1z]
        linarith
      omega
  have hinj : ∀ p ∈ dSolutionSet g0 r1 r2 D, ∀ q ∈ dSolutionSet g0 r1 r2 D,
      (p.1 - 1) / (r1 : ℤ) = (q.1 - 1) / (r1 : ℤ) → p = q := by
    intro p hp q hq heq
    rw [dSolutionSet, Finset.mem_filter] at hp hq
    have hD : (r2 : ℤ) * p.1 - (r1 : ℤ) * p.2 = (r2 : ℤ) * q.1 - (r1 : ℤ) * q.2 := by
      rw [hp.2, hq.2]
    have hdvd : (r1 : ℤ) ∣ (p.1 - q.1) := by
      have h1 : (r1 : ℤ) ∣ (r2 : ℤ) * (p.1 - q.1) := ⟨p.2 - q.2, by linarith⟩
      exact hcopz.dvd_of_dvd_mul_left h1
    have hmod : (p.1 - 1) % (r1 : ℤ) = (q.1 - 1) % (r1 : ℤ) := by
      have hmq : (p.1 : ℤ) ≡ q.1 [ZMOD (r1 : ℤ)] :=
        Int.modEq_iff_dvd.2 (by simpa [neg_sub] using hdvd.neg_right)
      exact hmq.sub_right 1
    have h1 : p.1 = q.1 := by
      have e1 := Int.mul_ediv_add_emod (p.1 - 1) (r1 : ℤ)
      have e2 := Int.mul_ediv_add_emod (q.1 - 1) (r1 : ℤ)
      rw [heq, hmod] at e1
      omega
    have h2 : p.2 = q.2 := by
      have : (r1 : ℤ) * p.2 = (r1 : ℤ) * q.2 := by rw [h1] at hD; linarith
      exact mul_left_cancel₀ (ne_of_gt hr1z) this
    exact Prod.ext h1 h2
  have hcard := Finset.card_le_card_of_injOn (s := dSolutionSet g0 r1 r2 D)
    (t := Finset.Icc (0 : ℤ) ((g0 : ℤ) - 1)) (fun p => (p.1 - 1) / (r1 : ℤ))
    (fun p hp => hmaps p hp) (fun p hp q hq h => hinj p hp q hq h)
  have hIcc : (Finset.Icc (0 : ℤ) ((g0 : ℤ) - 1)).card = g0 := by
    rw [Int.card_Icc]
    simp
  omega

/-- **`DET1-PRIMITIVE-D-MULTIPLICITY45`.**  `LEAN_PROVED`.

Under `1 ≤ tᵢ ≤ gᵢ` with `g₁ = g₀r₁`, `g₂ = g₀r₂`, `gcd(r₁,r₂) = 1`, the number of solutions
of `r₂t₁ - r₁t₂ = D` is at most `g₀ + 1`. -/
theorem dSolutionSet_card_le {g0 r1 r2 : ℕ} (hcop : Nat.Coprime r1 r2) (hr1 : 0 < r1) (D : ℤ) :
    (dSolutionSet g0 r1 r2 D).card ≤ g0 + 1 :=
  le_trans (dSolutionSet_card_le_g0 hcop hr1 D) (Nat.le_succ g0)

end PrimitiveD
end Erdos287
