import Mathlib
import RequestProject.CurrentProgramme.PrimitiveDMultiplicity

/-!
# Farey near-collision, exact finite count — Erdős #287, PRIMITIVE-LOCALPROFILE Δ, §E

Everything here is exact rational arithmetic and exact `Finset` cardinality: no real
cardinality, no asymptotic notation, no analytic input.

With `g₁ = g₀r₁`, `g₂ = g₀r₂`, `gcd(r₁,r₂) = 1`, and `D = r₂t₁ - r₁t₂`:

* `lcm_of_coprime_cofactors` — `lcm(g₁,g₂) = g₀r₁r₂`;
* `farey_near_collision_D_bound` — `|t₁/g₁ - t₂/g₂| ≤ 1/A  ⟹  |D| ≤ lcm(g₁,g₂)/A`;
* `nearCollisionSet_card_le` — the finite-count child: with the explicit integer floor
  `B = ⌊lcm(g₁,g₂)/A⌋`, the number of near-collision pairs in the box is at most
  `(2B+1)·g₀`, by fibring over `D` and applying `DET1-PRIMITIVE-D-MULTIPLICITY45`.

The displayed asymptotic `gcd(g₁,g₂) + g₁g₂/A` is **not** formalised: it needs range /
analytic notation absent from this repository.  Only the exact finite precursor is banked;
the asymptotic wrapper stays conditional.

Research status: `DET1-PRIMITIVE-FAREY-NEARCOLLISION45 : COMBINATORIAL PASS; ANALYTIC
MIXED-WEIGHT ROUTING OPEN.`
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

namespace Erdos287
namespace PrimitiveFarey

open Erdos287.PrimitiveD

/-! ## §E.1  The exact rational implication -/

/-- `lcm(g₀r₁, g₀r₂) = g₀r₁r₂` when `gcd(r₁,r₂) = 1`. -/
theorem lcm_of_coprime_cofactors {g0 r1 r2 : ℕ} (hg0 : 0 < g0) (hcop : Nat.Coprime r1 r2) :
    Nat.lcm (g0 * r1) (g0 * r2) = g0 * r1 * r2 := by
  have hgcd : Nat.gcd (g0 * r1) (g0 * r2) = g0 := by
    rw [Nat.gcd_mul_left, hcop, mul_one]
  have h := Nat.gcd_mul_lcm (g0 * r1) (g0 * r2)
  rw [hgcd] at h
  have : g0 * Nat.lcm (g0 * r1) (g0 * r2) = g0 * (g0 * r1 * r2) := by
    rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_left hg0 this

/-- **Exact Farey implication.**  `|t₁/g₁ - t₂/g₂| ≤ 1/A` forces `|D| ≤ lcm(g₁,g₂)/A`, with
`D = r₂t₁ - r₁t₂` and all arithmetic exact in `ℚ`. -/
theorem farey_near_collision_D_bound {g0 r1 r2 : ℕ} (hg0 : 0 < g0) (hr1 : 0 < r1) (hr2 : 0 < r2)
    (t1 t2 : ℤ) {A : ℚ}
    (h : |(t1 : ℚ) / ((g0 : ℚ) * r1) - (t2 : ℚ) / ((g0 : ℚ) * r2)| ≤ 1 / A) :
    |(((r2 : ℤ) * t1 - (r1 : ℤ) * t2 : ℤ) : ℚ)| ≤ ((g0 : ℚ) * r1 * r2) / A := by
  have hg0' : (0 : ℚ) < (g0 : ℚ) := by exact_mod_cast hg0
  have hr1' : (0 : ℚ) < (r1 : ℚ) := by exact_mod_cast hr1
  have hr2' : (0 : ℚ) < (r2 : ℚ) := by exact_mod_cast hr2
  have hid : (t1 : ℚ) / ((g0 : ℚ) * r1) - (t2 : ℚ) / ((g0 : ℚ) * r2)
      = (((r2 : ℤ) * t1 - (r1 : ℤ) * t2 : ℤ) : ℚ) / ((g0 : ℚ) * r1 * r2) := by
    push_cast
    field_simp
  have hpos : (0 : ℚ) < (g0 : ℚ) * r1 * r2 := by positivity
  rw [hid, abs_div, abs_of_pos hpos] at h
  have h2 := (div_le_iff₀ hpos).1 h
  calc |(((r2 : ℤ) * t1 - (r1 : ℤ) * t2 : ℤ) : ℚ)| ≤ 1 / A * ((g0 : ℚ) * r1 * r2) := h2
    _ = ((g0 : ℚ) * r1 * r2) / A := by ring

/-- The same bound written with the literal least common multiple:
`|t₁/g₁ - t₂/g₂| ≤ 1/A  ⟹  |D| ≤ lcm(g₁,g₂)/A`. -/
theorem farey_near_collision_lcm_bound {g0 r1 r2 : ℕ} (hg0 : 0 < g0) (hr1 : 0 < r1)
    (hr2 : 0 < r2) (hcop : Nat.Coprime r1 r2) (t1 t2 : ℤ) {A : ℚ}
    (h : |(t1 : ℚ) / ((g0 : ℚ) * r1) - (t2 : ℚ) / ((g0 : ℚ) * r2)| ≤ 1 / A) :
    |(((r2 : ℤ) * t1 - (r1 : ℤ) * t2 : ℤ) : ℚ)|
      ≤ ((Nat.lcm (g0 * r1) (g0 * r2) : ℕ) : ℚ) / A := by
  have hbound := farey_near_collision_D_bound hg0 hr1 hr2 t1 t2 h
  rw [lcm_of_coprime_cofactors hg0 hcop]
  push_cast
  push_cast at hbound
  exact hbound

/-! ## §E.2  The exact finite count -/

/-- The set of near-collision pairs in the box `1 ≤ tᵢ ≤ gᵢ`. -/
noncomputable def nearCollisionSet (g0 r1 r2 : ℕ) (A : ℚ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (1 : ℤ) ((g0 : ℤ) * r1)) ×ˢ (Finset.Icc (1 : ℤ) ((g0 : ℤ) * r2))).filter
    (fun p => |(p.1 : ℚ) / ((g0 : ℚ) * r1) - (p.2 : ℚ) / ((g0 : ℚ) * r2)| ≤ 1 / A)

/-- **`DET1-PRIMITIVE-FAREY-NEARCOLLISION45`, exact finite precursor.**  `LEAN_PROVED`.

With `B = ⌊lcm(g₁,g₂)/A⌋` (an explicit integer floor), the number of Farey near-collisions
in the box is at most `(2B+1)·g₀`.  No asymptotic wrapper is asserted. -/
theorem nearCollisionSet_card_le {g0 r1 r2 : ℕ} (hg0 : 0 < g0) (hr1 : 0 < r1) (hr2 : 0 < r2)
    (hcop : Nat.Coprime r1 r2) {A : ℚ} (hA : 0 < A) :
    (nearCollisionSet g0 r1 r2 A).card
      ≤ (2 * (⌊((g0 : ℚ) * r1 * r2) / A⌋).toNat + 1) * g0 := by
  classical
  set B : ℤ := ⌊((g0 : ℚ) * r1 * r2) / A⌋ with hB
  have hBnn : 0 ≤ B := by
    rw [hB]
    refine Int.le_floor.2 ?_
    have : (0 : ℚ) ≤ ((g0 : ℚ) * r1 * r2) / A := by positivity
    simpa using this
  -- every near-collision pair has its `D` in `[-B, B]`
  have hmaps : ∀ p ∈ nearCollisionSet g0 r1 r2 A,
      (r2 : ℤ) * p.1 - (r1 : ℤ) * p.2 ∈ Finset.Icc (-B) B := by
    intro p hp
    rw [nearCollisionSet, Finset.mem_filter] at hp
    have hbound := farey_near_collision_D_bound hg0 hr1 hr2 p.1 p.2 hp.2
    have habs : |(r2 : ℤ) * p.1 - (r1 : ℤ) * p.2| ≤ B := by
      refine Int.le_floor.2 ?_
      calc ((|(r2 : ℤ) * p.1 - (r1 : ℤ) * p.2| : ℤ) : ℚ)
          = |(((r2 : ℤ) * p.1 - (r1 : ℤ) * p.2 : ℤ) : ℚ)| := by push_cast [abs_sub_comm]; simp
        _ ≤ ((g0 : ℚ) * r1 * r2) / A := hbound
    rw [Finset.mem_Icc]
    constructor
    · linarith [neg_abs_le ((r2 : ℤ) * p.1 - (r1 : ℤ) * p.2), habs]
    · linarith [le_abs_self ((r2 : ℤ) * p.1 - (r1 : ℤ) * p.2), habs]
  -- fibre over `D` and use the multiplicity bound
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun p : ℤ × ℤ => (r2 : ℤ) * p.1 - (r1 : ℤ) * p.2)
    (s := nearCollisionSet g0 r1 r2 A) (t := Finset.Icc (-B) B)
    (fun p hp => Finset.mem_coe.2 (hmaps p (Finset.mem_coe.1 hp)))
  have hfiber : ∀ D ∈ Finset.Icc (-B) B,
      ((nearCollisionSet g0 r1 r2 A).filter
        (fun p => (r2 : ℤ) * p.1 - (r1 : ℤ) * p.2 = D)).card ≤ g0 := by
    intro D _
    refine le_trans (Finset.card_le_card ?_) (dSolutionSet_card_le_g0 hcop hr1 D)
    intro p hp
    rw [Finset.mem_filter, nearCollisionSet, Finset.mem_filter] at hp
    rw [dSolutionSet, Finset.mem_filter]
    exact ⟨hp.1.1, hp.2⟩
  have hsum : (nearCollisionSet g0 r1 r2 A).card ≤ (Finset.Icc (-B) B).card * g0 := by
    rw [hfib]
    calc ∑ D ∈ Finset.Icc (-B) B,
          ((nearCollisionSet g0 r1 r2 A).filter
            (fun p => (r2 : ℤ) * p.1 - (r1 : ℤ) * p.2 = D)).card
        ≤ ∑ _D ∈ Finset.Icc (-B) B, g0 := Finset.sum_le_sum hfiber
      _ = (Finset.Icc (-B) B).card * g0 := by rw [Finset.sum_const, smul_eq_mul]
  have hIcc : (Finset.Icc (-B) B).card = 2 * B.toNat + 1 := by
    rw [Int.card_Icc]
    omega
  rw [hIcc] at hsum
  exact hsum

end PrimitiveFarey
end Erdos287
