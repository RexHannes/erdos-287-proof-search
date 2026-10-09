import Mathlib

/-!
# Anchored V3 — the old-empty / new-hit exact finite certificate

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This module formalises one *exact finite rational certificate* on a fixed terminal bank:

```
r₁ = 199777,  r₂ = 200341,  s = 37,  m₁ = 74 * r₁,  m₂ = 74 * r₂,
ℓ  = 5407,    n₁ = m₁ * ℓ,  n₂ = m₂ * ℓ,           S₀ = 1 - 1/(r₁ * r₂).
```

The arithmetic heart is the identity `1/n₁ + 1/n₂ = 1/(r₁ * r₂)`, which holds because
`74 * 5407 = 400118 = r₁ + r₂`.  Hence `S₀ + 1/n₁ + 1/n₂ = 1` with a *two-term* terminal
addition.

The old (rowwise-neutral) model is shown to be empty on the same bank from explicit arithmetic
facts only:

* the old row targets are nonzero, so each of the two rows must contribute at least one site;
* old rowwise neutrality imposes an even cardinality on each row's contribution;
* hence every old-legal completion uses at least four terms;
* every bank site is at most `siteBound = 10 ^ 11`, so any such addition is at least
  `4 / 10 ^ 11`, which exceeds `1 - S₀ = 1 / (r₁ * r₂)`.

## STRICT SCOPE FIREWALL

`same_bank_old_empty_new_global_hit` is **only** a terminal arithmetic certificate about
rational sums.  It does **not** assert the existence of a full background word, it does **not**
produce an Erdős #287 counterexample, and it does **not** extend the certified finite frontier.
No statement in this file quantifies over sets of integers with unit reciprocal sum.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV3
namespace OldEmptyNewHit

/-- First core prime of the certificate. -/
def r₁ : ℕ := 199777

/-- Second core prime of the certificate. -/
def r₂ : ℕ := 200341

/-- The recorded small factor `s = 37` (so that `74 = 2 * s`). -/
def s : ℕ := 37

/-- First row modulus. -/
def m₁ : ℕ := 74 * r₁

/-- Second row modulus. -/
def m₂ : ℕ := 74 * r₂

/-- The band prime of the certificate. -/
def bandPrime : ℕ := 5407

/-- First new terminal site. -/
def n₁ : ℕ := m₁ * bandPrime

/-- Second new terminal site. -/
def n₂ : ℕ := m₂ * bandPrime

/-- The baseline partial sum of the certificate. -/
def S₀ : ℚ := 1 - 1 / ((r₁ * r₂ : ℕ) : ℚ)

/-- The explicit uniform upper bound on the size of a bank site. -/
def siteBound : ℕ := 10 ^ 11

theorem two_mul_s : 2 * s = 74 := by norm_num [s]

/-- The exact arithmetic coincidence driving the certificate: `74 * 5407 = r₁ + r₂`. -/
theorem coincidence : 74 * bandPrime = r₁ + r₂ := by norm_num [bandPrime, r₁, r₂]

theorem n₁_eq : n₁ = 79934373686 := by norm_num [n₁, m₁, r₁, bandPrime]

theorem n₂_eq : n₂ = 80160040238 := by norm_num [n₂, m₂, r₂, bandPrime]

theorem n₁_le_siteBound : n₁ ≤ siteBound := by norm_num [n₁_eq, siteBound]

theorem n₂_le_siteBound : n₂ ≤ siteBound := by norm_num [n₂_eq, siteBound]

/-- **The exact two-term reciprocal identity** `1/n₁ + 1/n₂ = 1/(r₁ * r₂)`. -/
theorem newHit_reciprocal :
    1 / ((n₁ : ℕ) : ℚ) + 1 / ((n₂ : ℕ) : ℚ) = 1 / ((r₁ * r₂ : ℕ) : ℚ) := by
  rw [n₁_eq, n₂_eq]
  norm_num [r₁, r₂]

/-- **The exact new global hit**: the baseline plus the two new terminal sites is `1`. -/
theorem newHit_exact : S₀ + 1 / ((n₁ : ℕ) : ℚ) + 1 / ((n₂ : ℕ) : ℚ) = 1 := by
  have h := newHit_reciprocal
  simp only [S₀, add_assoc]
  rw [h]
  ring

/-- An **old-legal completion** on the same bank: a two-row selection of distinct bank sites in
which each row target is nonzero (each row selection is nonempty) and each row satisfies the old
rowwise-neutrality parity condition (even cardinality). -/
structure OldCompletion where
  /-- sites selected in the first row -/
  T₁ : Finset ℕ
  /-- sites selected in the second row -/
  T₂ : Finset ℕ
  /-- the two rows select different sites -/
  disj : Disjoint T₁ T₂
  /-- bank sites are positive -/
  pos : ∀ t ∈ T₁ ∪ T₂, 0 < t
  /-- bank sites obey the uniform bank bound -/
  bdd : ∀ t ∈ T₁ ∪ T₂, t ≤ siteBound
  /-- the first old row target is nonzero -/
  ne₁ : T₁.Nonempty
  /-- the second old row target is nonzero -/
  ne₂ : T₂.Nonempty
  /-- old rowwise neutrality in the first row -/
  even₁ : Even T₁.card
  /-- old rowwise neutrality in the second row -/
  even₂ : Even T₂.card

namespace OldCompletion

variable (c : OldCompletion)

/-- The full set of sites used by an old-legal completion. -/
def sites : Finset ℕ := c.T₁ ∪ c.T₂

/-- A nonempty row of even cardinality has at least two sites. -/
theorem two_le_card_row {T : Finset ℕ} (hne : T.Nonempty) (he : Even T.card) : 2 ≤ T.card := by
  rcases he with ⟨k, hk⟩
  have h1 : 1 ≤ T.card := Finset.card_pos.mpr hne
  omega

/-- **Every old-legal completion uses at least four terms.** -/
theorem four_le_card : 4 ≤ c.sites.card := by
  have h1 := two_le_card_row c.ne₁ c.even₁
  have h2 := two_le_card_row c.ne₂ c.even₂
  have : (c.T₁ ∪ c.T₂).card = c.T₁.card + c.T₂.card := Finset.card_union_of_disjoint c.disj
  simp only [sites, this]
  omega

/-- **The exact rational lower bound** for an old-legal addition. -/
theorem four_div_siteBound_le_sum :
    4 / ((siteBound : ℕ) : ℚ) ≤ ∑ t ∈ c.sites, 1 / ((t : ℕ) : ℚ) := by
  have hb : (0:ℚ) < ((siteBound : ℕ) : ℚ) := by norm_num [siteBound]
  have hterm : ∀ t ∈ c.sites, 1 / ((siteBound : ℕ) : ℚ) ≤ 1 / ((t : ℕ) : ℚ) := by
    intro t ht
    have h1 : 0 < t := c.pos t ht
    have h2 : t ≤ siteBound := c.bdd t ht
    have h1' : (0:ℚ) < (t : ℚ) := by exact_mod_cast h1
    have h2' : ((t : ℕ) : ℚ) ≤ ((siteBound : ℕ) : ℚ) := by exact_mod_cast h2
    exact one_div_le_one_div_of_le h1' h2'
  have hsum := Finset.card_nsmul_le_sum c.sites (fun t => 1 / ((t : ℕ) : ℚ))
    (1 / ((siteBound : ℕ) : ℚ)) hterm
  have hcard : (4:ℚ) ≤ (c.sites.card : ℚ) := by exact_mod_cast c.four_le_card
  have hstep : (4:ℚ) * (1 / ((siteBound : ℕ) : ℚ)) ≤
      (c.sites.card : ℚ) * (1 / ((siteBound : ℕ) : ℚ)) := by
    have : (0:ℚ) ≤ 1 / ((siteBound : ℕ) : ℚ) := by positivity
    exact mul_le_mul_of_nonneg_right hcard this
  calc 4 / ((siteBound : ℕ) : ℚ) = (4:ℚ) * (1 / ((siteBound : ℕ) : ℚ)) := by ring
    _ ≤ (c.sites.card : ℚ) * (1 / ((siteBound : ℕ) : ℚ)) := hstep
    _ = c.sites.card • (1 / ((siteBound : ℕ) : ℚ)) := by simp [nsmul_eq_mul]
    _ ≤ ∑ t ∈ c.sites, 1 / ((t : ℕ) : ℚ) := hsum

end OldCompletion

/-- The exact rational gap left by the baseline. -/
theorem one_sub_S₀ : 1 - S₀ = 1 / ((r₁ * r₂ : ℕ) : ℚ) := by
  simp [S₀]

/-- The old lower bound strictly exceeds the remaining gap. -/
theorem gap_lt_four_div_siteBound : 1 - S₀ < 4 / ((siteBound : ℕ) : ℚ) := by
  rw [one_sub_S₀]
  norm_num [r₁, r₂, siteBound]

/-- **Old-model emptiness**: no old-legal completion is exact on this bank. -/
theorem old_empty (c : OldCompletion) : S₀ + ∑ t ∈ c.sites, 1 / ((t : ℕ) : ℚ) ≠ 1 := by
  intro hEq
  have hsum : ∑ t ∈ c.sites, 1 / ((t : ℕ) : ℚ) = 1 - S₀ := by linarith
  have h1 := c.four_div_siteBound_le_sum
  have h2 := gap_lt_four_div_siteBound
  rw [hsum] at h1
  linarith

/-- **Same bank: old-empty, new global hit.**

The exact terminal arithmetic certificate: on the fixed bank with site bound `10 ^ 11`, the
two new sites `n₁, n₂` complete the baseline `S₀` exactly, while *every* old-legal (rowwise
neutral, nonzero row target) completion fails to be exact.

FIREWALL: this is a statement about rational sums only.  It asserts nothing about the existence
of a background word, it is not an Erdős #287 counterexample, and it does not extend the
certified finite frontier. -/
theorem same_bank_old_empty_new_global_hit :
    (n₁ ≤ siteBound ∧ n₂ ≤ siteBound ∧
        S₀ + 1 / ((n₁ : ℕ) : ℚ) + 1 / ((n₂ : ℕ) : ℚ) = 1) ∧
      ∀ c : OldCompletion, S₀ + ∑ t ∈ c.sites, 1 / ((t : ℕ) : ℚ) ≠ 1 :=
  ⟨⟨n₁_le_siteBound, n₂_le_siteBound, newHit_exact⟩, old_empty⟩

end OldEmptyNewHit
end AnchoredV3
end Erdos287
