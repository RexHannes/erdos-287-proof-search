import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V6: the finite per-middle-row contact target

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The contact-core route needs, for a middle row `p`, the finite contact target

`H_p(𝒞) ≤ 2 π(z) + 4 ⌊M / z²⌋`.

Section 1–3 formalize this as an **exact, sorry-free finite combinatorial inequality**: it is the
charging inequality for a contact set `H` charged to small primes (each prime absorbing at most
two contacts) and to the multiples of `z²` in the window (each absorbing at most four).  Nothing
analytic is used.

Section 4 contains the **exact balancing identity** `M / z² = z / l` at the optimizing scale
`z³ = M l`, which is the algebraic half of the asymptotic consequence.

Section 5 keeps the genuinely external part separate and uninhabited: the prime-counting
asymptotic `π(z) ≪ z / log z` and the resulting `H_p(𝒞) ≪ M^{1/3} (log M)^{-2/3}` are *not*
proved here; only the implication that consumes them is kernel-proved.
-/

namespace Erdos287
namespace ResearchBankV6
namespace ContactTarget

open Finset

/-! ## 1.  Small primes and multiples of `z²` -/

/-- The primes `≤ z`. -/
def primesLE (z : ℕ) : Finset ℕ := (Finset.Icc 1 z).filter Nat.Prime

/-- `π(z)`, the number of primes `≤ z`. -/
def piCount (z : ℕ) : ℕ := (primesLE z).card

/-- The multiples of `z²` in the window `[1, M]`. -/
def squareMultiples (M z : ℕ) : Finset ℕ := (Finset.Icc 1 M).filter (fun n => z ^ 2 ∣ n)

/-- There are exactly `⌊M / z²⌋` multiples of `z²` in `[1, M]`. -/
theorem squareMultiples_card (M z : ℕ) : (squareMultiples M z).card = M / z ^ 2 := by
  have h : Finset.Icc 1 M = Finset.Ioc 0 M := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [squareMultiples, h]
  exact Nat.Ioc_filter_dvd_card_eq_div M (z ^ 2)

/-! ## 2.  The generic charging inequality -/

/-- **Charging inequality.**  If every member of a finite set `H` is charged to an element of
`T₁ ∪ T₂`, no element of `T₁` carrying more than `c₁` charges and no element of `T₂` carrying more
than `c₂`, then `|H| ≤ c₁ |T₁| + c₂ |T₂|`. -/
theorem card_le_of_charge {α : Type*} [DecidableEq α] {H : Finset α} {T₁ T₂ : Finset ℕ}
    (c₁ c₂ : ℕ) (f : α → ℕ) (hf : ∀ x ∈ H, f x ∈ T₁ ∪ T₂)
    (h₁ : ∀ t ∈ T₁, (H.filter (fun x => f x = t)).card ≤ c₁)
    (h₂ : ∀ t ∈ T₂, (H.filter (fun x => f x = t)).card ≤ c₂) :
    H.card ≤ c₁ * T₁.card + c₂ * T₂.card := by
  have hmaps : Set.MapsTo f (H : Set α) ((T₁ ∪ T₂ : Finset ℕ) : Set ℕ) := by
    intro x hx
    exact_mod_cast hf x hx
  have hsplit : H.card = ∑ t ∈ T₁ ∪ T₂, (H.filter (fun x => f x = t)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hunion : T₁ ∪ T₂ = T₁ ∪ (T₂ \ T₁) := by
    ext t; by_cases h : t ∈ T₁ <;> simp [h, Finset.mem_union]
  have hdisj : Disjoint T₁ (T₂ \ T₁) := Finset.disjoint_sdiff
  rw [hsplit, hunion, Finset.sum_union hdisj]
  have hA : ∑ t ∈ T₁, (H.filter (fun x => f x = t)).card ≤ c₁ * T₁.card := by
    calc ∑ t ∈ T₁, (H.filter (fun x => f x = t)).card ≤ ∑ _t ∈ T₁, c₁ :=
          Finset.sum_le_sum h₁
      _ = c₁ * T₁.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hB : ∑ t ∈ T₂ \ T₁, (H.filter (fun x => f x = t)).card ≤ c₂ * T₂.card := by
    calc ∑ t ∈ T₂ \ T₁, (H.filter (fun x => f x = t)).card ≤ ∑ _t ∈ T₂ \ T₁, c₂ :=
          Finset.sum_le_sum (fun t ht => h₂ t (Finset.mem_sdiff.1 ht).1)
      _ = c₂ * (T₂ \ T₁).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ c₂ * T₂.card := Nat.mul_le_mul_left _ (Finset.card_le_card (Finset.sdiff_subset))
  omega

/-! ## 3.  The finite per-middle-row contact target -/

/-- **Finite contact target (KERNEL).**  Let `H` be the contact set of a middle row and let each
contact be charged either to a prime `≤ z` (each such prime absorbing at most two contacts) or to
a multiple of `z²` in `[1, M]` (each absorbing at most four).  Then

`|H| ≤ 2 π(z) + 4 ⌊M / z²⌋`. -/
theorem contact_target_bound {α : Type*} [DecidableEq α] {H : Finset α} (M z : ℕ)
    (f : α → ℕ) (hf : ∀ x ∈ H, f x ∈ primesLE z ∪ squareMultiples M z)
    (hprime : ∀ q ∈ primesLE z, (H.filter (fun x => f x = q)).card ≤ 2)
    (hsq : ∀ d ∈ squareMultiples M z, (H.filter (fun x => f x = d)).card ≤ 4) :
    H.card ≤ 2 * piCount z + 4 * (M / z ^ 2) := by
  have h := card_le_of_charge 2 4 f hf hprime hsq
  rw [squareMultiples_card] at h
  exact h

/-! ## 4.  The exact balancing identity at the optimizing scale -/

/-- **Exact balancing identity.**  At the optimizing scale `z³ = M l` the two contributions of the
contact target are equal: `M / z² = z / l`.  This is the exact algebraic content of the choice
`z ≍ (M log M)^{1/3}`; no analytic input is used. -/
theorem balanced_scale {M l z : ℝ} (hz : z ≠ 0) (hl : l ≠ 0) (hcube : z ^ 3 = M * l) :
    M / z ^ 2 = z / l := by
  field_simp
  nlinarith [hcube]

/-- Consequently, at the optimizing scale the whole finite target collapses to a single term. -/
theorem contact_target_at_balanced_scale {M l z c₁ c₂ : ℝ} (hz : z ≠ 0) (hl : l ≠ 0)
    (hcube : z ^ 3 = M * l) :
    c₁ * (z / l) + c₂ * (M / z ^ 2) = (c₁ + c₂) * (z / l) := by
  rw [balanced_scale hz hl hcube]; ring

/-! ## 5.  The external asymptotic adapter (uninhabited) -/

/-- **(PNT-ADAPTER), external analytic input.**  The prime-counting bound `π(z) ≪ z / log z`.
`externalAnalyticBank`: recorded, *not* proved in this project. -/
def PrimeCountingAsymptotic : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 2 ≤ z → (piCount z : ℝ) ≤ C * (z : ℝ) / Real.log z

/-- The asymptotic contact target `H_p(𝒞) ≪ M^{1/3} (log M)^{-2/3}`, as a statement about a given
contact-size function `H`. -/
def ContactCubeRootTarget (H : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    H M ≤ C * (M : ℝ) ^ ((1 : ℝ) / 3) * (Real.log M) ^ (-(2 : ℝ) / 3)

/-- **(CONTACT-ASYMPTOTIC-ADAPTER), external analytic input.**  The optimization step which
converts the finite target `H M ≤ 2 π(z) + 4 ⌊M/z²⌋`, uniformly in `z`, together with the
prime-counting bound, into the cube-root asymptotic.  It carries the floor bookkeeping and the
analytic estimates for `log z` at `z ≍ (M log M)^{1/3}`.

`externalAnalyticBank`: recorded, *not* proved in this project. -/
def ContactAsymptoticAdapter (H : ℕ → ℝ) : Prop :=
  PrimeCountingAsymptotic →
    (∀ M z : ℕ, 2 ≤ z → H M ≤ 2 * (piCount z : ℝ) + 4 * ((M / z ^ 2 : ℕ) : ℝ)) →
      ContactCubeRootTarget H

/-- **CONDITIONAL.**  The cube-root contact bound follows from the finite kernel inequality
*only* through the external adapter; the implication is kernel-proved, its premises are not
inhabited here. -/
theorem contact_cubeRoot_conditional {H : ℕ → ℝ} (hadapt : ContactAsymptoticAdapter H)
    (hpnt : PrimeCountingAsymptotic)
    (hfin : ∀ M z : ℕ, 2 ≤ z → H M ≤ 2 * (piCount z : ℝ) + 4 * ((M / z ^ 2 : ℕ) : ℝ)) :
    ContactCubeRootTarget H := hadapt hpnt hfin

/-- The real-valued form of the finite kernel inequality, ready for the adapter. -/
theorem contact_target_bound_real {α : Type*} [DecidableEq α] {H : Finset α} (M z : ℕ)
    (f : α → ℕ) (hf : ∀ x ∈ H, f x ∈ primesLE z ∪ squareMultiples M z)
    (hprime : ∀ q ∈ primesLE z, (H.filter (fun x => f x = q)).card ≤ 2)
    (hsq : ∀ d ∈ squareMultiples M z, (H.filter (fun x => f x = d)).card ≤ 4) :
    (H.card : ℝ) ≤ 2 * (piCount z : ℝ) + 4 * ((M / z ^ 2 : ℕ) : ℝ) := by
  have := contact_target_bound M z f hf hprime hsq
  exact_mod_cast this

end ContactTarget
end ResearchBankV6
end Erdos287
