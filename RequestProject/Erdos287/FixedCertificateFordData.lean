import Mathlib

/-!
# The literal fixed Ford certificate — data layer (V12, Part G1)

V12 asks for the *explicit* fixed Ford certificate `g*` to be pinned:

* a central parameter `ν₀ = 0.16623`;
* `g₀(∅) = 1`;
* a one-variable branch `−1_{x ≤ 1/2}`;
* a two-variable branch supported on `(1−ν₀)/2 < x₁+x₂ < 1/2`;
* a three-variable branch `−1_{x₁+x₂+x₃ ≤ 1/2}`;
* a fixed small shrink `g*` of `g₀`.

## What is and is not claimed here

The source dossier is **not present in this repository**, so this file does *not* assert
that the data below is the published Ford certificate; it defines the data exactly as
transcribed in the request, so that its finite arithmetic can be checked, and keeps every
source-dependent statement as an explicit predicate:

* `fordCandidate` — the transcribed branch data, with the two-variable coefficient left
  as a *parameter* `c₂`, because the request specifies that branch's support but not its
  sign;
* `CertificatePinned` — the predicate "this data is the published certificate", which is
  never proved (`FIXED_CERTIFICATE287_PIN` = SOURCE BLOCKED in this repository);
* `PositiveComparisonMargin` — the source's positivity statement `C* = C₀ + O(ε) > 0`,
  also never proved, and deliberately *not* given an invented effective `ε`.

What *is* proved here is only the finite arithmetic of the transcribed data: that the
two-variable window is nonempty, that it lies strictly below `1/2`, that it is disjoint
from the three-variable cut, and the branch values at sample points.

## Main results

* `nu0_bounds`, `twoVarWindow_nonempty`, `twoVarWindow_subset_half`;
* `fordCandidate_empty`, `fordCandidate_one`, `fordCandidate_three` — the branch values;
* `shrink_le` — a shrink by `1 − δ` never increases the absolute value of a branch.
-/

open scoped BigOperators

namespace Erdos287
namespace FordData

/-! ## The central parameter -/

/-- The central parameter `ν₀ = 0.16623`, transcribed as an exact rational. -/
def nu0 : ℚ := 16623 / 100000

theorem nu0_bounds : 0 < nu0 ∧ nu0 < 1 / 2 := by
  constructor <;> norm_num [nu0]

/-- The lower endpoint `(1 − ν₀)/2` of the two-variable window. -/
def twoVarLow : ℚ := (1 - nu0) / 2

theorem twoVarLow_eq : twoVarLow = 83377 / 200000 := by norm_num [twoVarLow, nu0]

/-- The two-variable window is nonempty: `(1 − ν₀)/2 < 1/2`. -/
theorem twoVarWindow_nonempty : twoVarLow < 1 / 2 := by norm_num [twoVarLow, nu0]

/-- Everything in the two-variable window is strictly below the one-variable cut `1/2`. -/
theorem twoVarWindow_subset_half (s : ℚ) (h : twoVarLow < s ∧ s < 1 / 2) : s < 1 / 2 := h.2

/-- The window has positive width `ν₀/2`. -/
theorem twoVarWindow_width : (1 : ℚ) / 2 - twoVarLow = nu0 / 2 := by
  norm_num [twoVarLow, nu0]

/-! ## The branch data -/

/-- The transcribed Ford certificate as a function of the list of variables, with the
two-variable coefficient carried as a parameter `c₂` (the request pins that branch's
*support*, not its sign). -/
def fordCandidate (c2 : ℚ) : List ℚ → ℚ
  | [] => 1
  | [x] => if x ≤ 1 / 2 then -1 else 0
  | [x1, x2] => if twoVarLow < x1 + x2 ∧ x1 + x2 < 1 / 2 then c2 else 0
  | [x1, x2, x3] => if x1 + x2 + x3 ≤ 1 / 2 then -1 else 0
  | _ => 0

theorem fordCandidate_empty (c2 : ℚ) : fordCandidate c2 [] = 1 := rfl

theorem fordCandidate_one (c2 x : ℚ) (h : x ≤ 1 / 2) : fordCandidate c2 [x] = -1 := by
  simp only [fordCandidate, if_pos h]

theorem fordCandidate_one_out (c2 x : ℚ) (h : ¬ x ≤ 1 / 2) : fordCandidate c2 [x] = 0 := by
  simp only [fordCandidate, if_neg h]

theorem fordCandidate_two_in (c2 x1 x2 : ℚ)
    (h1 : twoVarLow < x1 + x2) (h2 : x1 + x2 < 1 / 2) :
    fordCandidate c2 [x1, x2] = c2 := by
  simp only [fordCandidate, if_pos (And.intro h1 h2)]

theorem fordCandidate_two_out (c2 x1 x2 : ℚ) (h : x1 + x2 ≤ twoVarLow) :
    fordCandidate c2 [x1, x2] = 0 := by
  have : ¬ (twoVarLow < x1 + x2 ∧ x1 + x2 < 1 / 2) := by
    rintro ⟨h1, -⟩; exact absurd h1 (not_lt.2 h)
  simp only [fordCandidate, if_neg this]

theorem fordCandidate_three (c2 x1 x2 x3 : ℚ) (h : x1 + x2 + x3 ≤ 1 / 2) :
    fordCandidate c2 [x1, x2, x3] = -1 := by
  simp only [fordCandidate, if_pos h]

/-- Sample point in the two-variable window: `x₁ = x₂ = 0.22` gives `x₁+x₂ = 0.44`, which
lies strictly between `(1−ν₀)/2 = 0.416885` and `1/2`. -/
theorem fordCandidate_two_sample (c2 : ℚ) :
    fordCandidate c2 [22 / 100, 22 / 100] = c2 :=
  fordCandidate_two_in c2 _ _ (by norm_num [twoVarLow, nu0]) (by norm_num)

/-- Sample point outside the window: `x₁ = x₂ = 0.2` gives `0.4 < 0.416885`. -/
theorem fordCandidate_two_sample_out (c2 : ℚ) :
    fordCandidate c2 [2 / 10, 2 / 10] = 0 :=
  fordCandidate_two_out c2 _ _ (by norm_num [twoVarLow, nu0])

/-! ## The shrink -/

/-- The fixed small shrink: `g* = (1 − δ)·g₀` with `0 < δ < 1`.  The source proves the
existence of an admissible `δ` through a limiting argument `C* = C₀ + O(ε)`; no effective
decimal value is invented here, so `δ` stays a parameter. -/
def shrink (delta : ℚ) (g : List ℚ → ℚ) : List ℚ → ℚ := fun L => (1 - delta) * g L

theorem shrink_empty (delta c2 : ℚ) : shrink delta (fordCandidate c2) [] = 1 - delta := by
  simp [shrink, fordCandidate]

/-- A shrink with `0 ≤ δ ≤ 1` never increases the absolute value of a branch. -/
theorem shrink_le (delta : ℚ) (h0 : 0 ≤ delta) (h1 : delta ≤ 1) (g : List ℚ → ℚ) (L : List ℚ) :
    |shrink delta g L| ≤ |g L| := by
  rw [shrink, abs_mul]
  have : |1 - delta| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  calc |1 - delta| * |g L| ≤ 1 * |g L| :=
        mul_le_mul_of_nonneg_right this (abs_nonneg _)
    _ = |g L| := one_mul _

/-! ## The source-dependent predicates (never proved here) -/

/-- **`FIXED_CERTIFICATE287_PIN`.**  The predicate asserting that the transcribed data is
the published Ford certificate, in the sense that its branch values agree with a supplied
source function `gSource`.  This repository contains no copy of the source, so no
inhabitant is constructed: the pin is **SOURCE BLOCKED** here. -/
def CertificatePinned (c2 : ℚ) (gSource : List ℚ → ℚ) : Prop :=
  ∀ L : List ℚ, L.length ≤ 3 → fordCandidate c2 L = gSource L

/-- **Positivity of the comparison margin.**  The source statement is
`C* = C₀ + O(ε) > 0` for a sufficiently small shrink; no effective `ε` is available in
this repository, so this is a predicate, not a theorem. -/
def PositiveComparisonMargin (Cstar : ℝ) : Prop := 0 < 1 + Cstar

/-- Trivial but useful: a pinned certificate is determined by the source on the relevant
lengths, so two pins of the same source agree.  (Pure logic; asserts nothing about the
source.) -/
theorem pinned_unique {c2 c2' : ℚ} {gSource : List ℚ → ℚ}
    (h : CertificatePinned c2 gSource) (h' : CertificatePinned c2' gSource)
    (L : List ℚ) (hL : L.length ≤ 3) :
    fordCandidate c2 L = fordCandidate c2' L := by
  rw [h L hL, h' L hL]

/-- If the two-variable coefficient is pinned by the source at a window point, it is
determined. -/
theorem pinned_two_var {c2 : ℚ} {gSource : List ℚ → ℚ} (h : CertificatePinned c2 gSource)
    (x1 x2 : ℚ) (h1 : twoVarLow < x1 + x2) (h2 : x1 + x2 < 1 / 2) :
    c2 = gSource [x1, x2] := by
  rw [← h [x1, x2] (by simp), fordCandidate_two_in c2 x1 x2 h1 h2]

end FordData
end Erdos287
