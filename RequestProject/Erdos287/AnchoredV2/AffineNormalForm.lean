import Mathlib

/-!
# Anchored V2 — affine path normal form of a contact-equation system

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Along a supplied spanning tree of a connected contact-equation system every label is an affine
function of the root label,

`q_v = α_v q₀ + β_v`,  `α_v, β_v ∈ ℚ`,

with the tree recursion `α_v = a_v α_{parent v}`, `β_v = a_v β_{parent v} + b_v` supplied as
certified data.  Every non-tree edge then either imposes a genuine rational affine equation on
`q₀` or is an identity; `FullyBalanced` says all fundamental non-tree relations are identities,
and then the rational label solutions form a one-parameter affine family.

If moreover an integral root value `x₀` making all labels integral is supplied, all integral
root values lie in the arithmetic progression `x₀ + L ℤ` with `L` the lcm of the denominators of
the `α_v`.  **No claim is made that any resulting label is prime or a prime power.**
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV2

/-- A rational multiple of an integer is an integer exactly when the denominator divides it
(first direction). -/
theorem den_dvd_of_mul_int (q : ℚ) (n k : ℤ) (h : q * n = k) : ((q.den : ℤ) ∣ n) := by
  have h1 : (q.num : ℚ) * n = k * q.den := by
    rw [← Rat.mul_den_eq_num, mul_assoc, mul_comm (q.den : ℚ) (n : ℚ), ← mul_assoc, h]
  have h2 : q.num * n = k * q.den := by exact_mod_cast h1
  have h3 : (q.den : ℤ) ∣ q.num * n := ⟨k, by linarith [h2]⟩
  have hcop : IsCoprime (q.den : ℤ) q.num := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Nat.coprime_comm] using q.reduced
  exact hcop.dvd_of_dvd_mul_left h3

/-- A rational multiple of an integer is an integer exactly when the denominator divides it
(second direction). -/
theorem mul_int_of_den_dvd (q : ℚ) (m : ℤ) (h : (q.den : ℤ) ∣ m) : ∃ k : ℤ, q * m = k := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨q.num * c, ?_⟩
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

/-- Certified affine data for a contact-equation system along a supplied spanning tree. -/
structure AffineTreeData where
  /-- the labelled positions -/
  verts : Finset ℕ
  /-- the chosen root -/
  root : ℕ
  /-- the supplied spanning-tree parent map -/
  parent : ℕ → ℕ
  /-- the multiplicative coefficient of the tree relation at each non-root vertex -/
  tcoef : ℕ → ℚ
  /-- the additive constant of the tree relation at each non-root vertex -/
  tconst : ℕ → ℚ
  /-- a rank function witnessing that the parent map is well founded -/
  depth : ℕ → ℕ
  /-- the affine multiplier of each label in terms of the root label -/
  alpha : ℕ → ℚ
  /-- the affine constant of each label in terms of the root label -/
  beta : ℕ → ℚ
  /-- the fundamental non-tree edges -/
  nonTree : Finset (ℕ × ℕ)
  /-- the multiplicative coefficient of each non-tree relation -/
  ncoef : ℕ × ℕ → ℚ
  /-- the additive constant of each non-tree relation -/
  nconst : ℕ × ℕ → ℚ

namespace AffineTreeData

/-- The supplied affine data is certified: the root normalisation and the tree recursion hold,
and the parent map strictly decreases the rank. -/
structure Certified (D : AffineTreeData) : Prop where
  /-- the root is a labelled position -/
  root_mem : D.root ∈ D.verts
  /-- the root normalisation `α_root = 1` -/
  alpha_root : D.alpha D.root = 1
  /-- the root normalisation `β_root = 0` -/
  beta_root : D.beta D.root = 0
  /-- parents of labelled positions are labelled -/
  parent_mem : ∀ v ∈ D.verts, v ≠ D.root → D.parent v ∈ D.verts
  /-- the rank strictly decreases towards the root -/
  depth_lt : ∀ v ∈ D.verts, v ≠ D.root → D.depth (D.parent v) < D.depth v
  /-- the affine multiplier obeys the tree recursion -/
  alpha_rec : ∀ v ∈ D.verts, v ≠ D.root → D.alpha v = D.tcoef v * D.alpha (D.parent v)
  /-- the affine constant obeys the tree recursion -/
  beta_rec : ∀ v ∈ D.verts, v ≠ D.root →
    D.beta v = D.tcoef v * D.beta (D.parent v) + D.tconst v
  /-- non-tree edges join labelled positions -/
  nonTree_mem : ∀ e ∈ D.nonTree, e.1 ∈ D.verts ∧ e.2 ∈ D.verts

/-- A labelling satisfies the spanning-tree relations. -/
def SatisfiesTree (D : AffineTreeData) (q : ℕ → ℚ) : Prop :=
  ∀ v ∈ D.verts, v ≠ D.root → q v = D.tcoef v * q (D.parent v) + D.tconst v

/-- A labelling satisfies the non-tree relations. -/
def SatisfiesNonTree (D : AffineTreeData) (q : ℕ → ℚ) : Prop :=
  ∀ e ∈ D.nonTree, q e.1 = D.ncoef e * q e.2 + D.nconst e

/-- A labelling satisfies the whole contact-equation system. -/
def Satisfies (D : AffineTreeData) (q : ℕ → ℚ) : Prop :=
  SatisfiesTree D q ∧ SatisfiesNonTree D q

/-- The affine family of labellings parameterised by the root value. -/
def famLabel (D : AffineTreeData) (x : ℚ) : ℕ → ℚ := fun v => D.alpha v * x + D.beta v

/-- The coefficient of the affine equation imposed on the root value by a non-tree edge. -/
def edgeCoef (D : AffineTreeData) (e : ℕ × ℕ) : ℚ := D.alpha e.1 - D.ncoef e * D.alpha e.2

/-- The constant of the affine equation imposed on the root value by a non-tree edge. -/
def edgeConst (D : AffineTreeData) (e : ℕ × ℕ) : ℚ :=
  D.ncoef e * D.beta e.2 + D.nconst e - D.beta e.1

/-- Every fundamental non-tree relation is an identity. -/
def FullyBalanced (D : AffineTreeData) : Prop :=
  ∀ e ∈ D.nonTree, D.edgeCoef e = 0 ∧ D.edgeConst e = 0

/-- The affine family satisfies the spanning-tree relations. -/
theorem famLabel_satisfiesTree {D : AffineTreeData} (hC : D.Certified) (x : ℚ) :
    D.SatisfiesTree (D.famLabel x) := by
  intro v hv hroot
  unfold famLabel
  rw [hC.alpha_rec v hv hroot, hC.beta_rec v hv hroot]
  ring

/-- **Path transfer / uniqueness.**  Any labelling satisfying the spanning-tree relations is the
member of the affine family determined by its root value. -/
theorem eq_famLabel_of_satisfiesTree {D : AffineTreeData} (hC : D.Certified) {q : ℕ → ℚ}
    (hq : D.SatisfiesTree q) : ∀ v ∈ D.verts, q v = D.famLabel (q D.root) v := by
  have key : ∀ n : ℕ, ∀ v ∈ D.verts, D.depth v = n → q v = D.famLabel (q D.root) v := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv hdv
      by_cases hroot : v = D.root
      · subst hroot
        simp [famLabel, hC.alpha_root, hC.beta_root]
      · have hp := hC.parent_mem v hv hroot
        have hlt := hC.depth_lt v hv hroot
        have hpar := ih (D.depth (D.parent v)) (by omega) (D.parent v) hp rfl
        rw [hq v hv hroot, hpar]
        unfold famLabel
        rw [hC.alpha_rec v hv hroot, hC.beta_rec v hv hroot]
        ring
  exact fun v hv => key (D.depth v) v hv rfl

/-- A non-tree edge relation on the affine family is exactly a rational affine equation on the
root value. -/
theorem nonTree_iff {D : AffineTreeData} (e : ℕ × ℕ) (x : ℚ) :
    (D.famLabel x) e.1 = D.ncoef e * (D.famLabel x) e.2 + D.nconst e ↔
      D.edgeCoef e * x = D.edgeConst e := by
  unfold famLabel edgeCoef edgeConst
  constructor <;> intro h <;> linear_combination h

/-- **Non-tree dichotomy.**  A fundamental non-tree edge either imposes a genuine rational
affine equation on the root value (a unique admissible value, or none at all), or is an
identity satisfied by every root value. -/
theorem nonTree_dichotomy {D : AffineTreeData} (e : ℕ × ℕ) :
    (∀ x : ℚ, (D.famLabel x) e.1 = D.ncoef e * (D.famLabel x) e.2 + D.nconst e) ∨
    (∃! x : ℚ, (D.famLabel x) e.1 = D.ncoef e * (D.famLabel x) e.2 + D.nconst e) ∨
    (∀ x : ℚ, ¬ (D.famLabel x) e.1 = D.ncoef e * (D.famLabel x) e.2 + D.nconst e) := by
  by_cases hc : D.edgeCoef e = 0
  · by_cases hk : D.edgeConst e = 0
    · left
      intro x
      exact (nonTree_iff e x).2 (by rw [hc, hk]; ring)
    · right; right
      intro x hx
      have := (nonTree_iff e x).1 hx
      rw [hc, zero_mul] at this
      exact hk this.symm
  · right; left
    refine ⟨D.edgeConst e / D.edgeCoef e, ?_, ?_⟩
    · refine (nonTree_iff e _).2 ?_
      field_simp
    · intro y hy
      have := (nonTree_iff e y).1 hy
      field_simp
      linarith [this]

/-- **`fullyBalanced_one_parameter`.**  If all fundamental non-tree relations are identities the
rational label solutions form a one-parameter affine family: every member of the family is a
solution, and every solution is the member determined by its root value. -/
theorem fullyBalanced_one_parameter {D : AffineTreeData} (hC : D.Certified)
    (hB : D.FullyBalanced) :
    (∀ x : ℚ, D.Satisfies (D.famLabel x)) ∧
      (∀ q : ℕ → ℚ, D.Satisfies q → ∀ v ∈ D.verts, q v = D.famLabel (q D.root) v) := by
  refine ⟨fun x => ⟨famLabel_satisfiesTree hC x, ?_⟩, fun q hq =>
    eq_famLabel_of_satisfiesTree hC hq.1⟩
  intro e he
  refine (nonTree_iff e x).2 ?_
  rw [(hB e he).1, (hB e he).2]
  ring

/-- The explicit common denominator / modulus of the integral root progression. -/
def modulus (D : AffineTreeData) : ℕ := D.verts.lcm (fun v => (D.alpha v).den)

theorem modulus_pos (D : AffineTreeData) : 0 < D.modulus := by
  rcases Nat.eq_zero_or_pos D.modulus with h | h
  · exfalso
    unfold modulus at h
    rw [Finset.lcm_eq_zero_iff] at h
    obtain ⟨v, -, hv0⟩ := h
    exact (D.alpha v).den_nz hv0
  · exact h

/-- **`integral_root_progression`.**  Given one integral root value making all labels integral,
every integral root value with integral labels lies in the arithmetic progression
`x₀ + modulus · ℤ`. -/
theorem integral_root_progression {D : AffineTreeData} {x₀ x : ℤ}
    (h₀ : ∀ v ∈ D.verts, ∃ k : ℤ, D.famLabel (x₀ : ℚ) v = (k : ℚ))
    (h : ∀ v ∈ D.verts, ∃ k : ℤ, D.famLabel (x : ℚ) v = (k : ℚ)) :
    ∃ t : ℤ, x = x₀ + (D.modulus : ℤ) * t := by
  have hden : ∀ v ∈ D.verts, ((D.alpha v).den : ℤ) ∣ (x - x₀) := by
    intro v hv
    obtain ⟨k, hk⟩ := h v hv
    obtain ⟨k₀, hk₀⟩ := h₀ v hv
    refine den_dvd_of_mul_int (D.alpha v) (x - x₀) (k - k₀) ?_
    unfold famLabel at hk hk₀
    push_cast
    linarith [hk, hk₀]
  have hnat : ∀ v ∈ D.verts, (D.alpha v).den ∣ (x - x₀).natAbs := by
    intro v hv
    have := hden v hv
    rwa [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast] at this
  have hlcm : D.modulus ∣ (x - x₀).natAbs := Finset.lcm_dvd hnat
  have hZ : (D.modulus : ℤ) ∣ (x - x₀) := by
    rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
    exact hlcm
  obtain ⟨t, ht⟩ := hZ
  exact ⟨t, by linarith [ht]⟩

/-- **`integral_progression_sound`.**  Conversely every member of the progression again makes
all labels integral, provided the affine constants are integral. -/
theorem integral_progression_sound {D : AffineTreeData} {x₀ : ℤ}
    (h₀ : ∀ v ∈ D.verts, ∃ k : ℤ, D.famLabel (x₀ : ℚ) v = (k : ℚ)) (t : ℤ) :
    ∀ v ∈ D.verts, ∃ k : ℤ, D.famLabel ((x₀ + (D.modulus : ℤ) * t : ℤ) : ℚ) v = (k : ℚ) := by
  intro v hv
  obtain ⟨k₀, hk₀⟩ := h₀ v hv
  have hdvd : ((D.alpha v).den : ℤ) ∣ (D.modulus : ℤ) * t := by
    refine Dvd.dvd.mul_right ?_ t
    have : (D.alpha v).den ∣ D.modulus :=
      Finset.dvd_lcm (f := fun w => (D.alpha w).den) hv
    exact_mod_cast this
  obtain ⟨k₁, hk₁⟩ := mul_int_of_den_dvd (D.alpha v) ((D.modulus : ℤ) * t) hdvd
  refine ⟨k₀ + k₁, ?_⟩
  unfold famLabel at hk₀ ⊢
  push_cast at hk₀ hk₁ ⊢
  linarith [hk₀, hk₁]

end AffineTreeData

end AnchoredV2
end Erdos287
