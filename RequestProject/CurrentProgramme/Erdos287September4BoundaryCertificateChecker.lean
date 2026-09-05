import RequestProject.CurrentProgramme.Erdos287September4BoundaryDivisorLattice
import RequestProject.CurrentProgramme.Erdos287September4LargeLTailCompiler

/-!
# Erdős #287 — September-4 bank, §8–§10: the boundary certificate checker and the budget

```
EXACT RATIONAL BUDGET  poleBudget + oscillatoryBudget < 10⁻⁶ : KERNEL-PROVED
ORDERED-FIELD BUDGET COMPILER                                : KERNEL-PROVED
BOUNDARY CERTIFICATE CHECKER (coverage + bounds soundness)   : KERNEL-PROVED
CONDITIONAL COMPACT-SLAB CLOSURE 42.9 ≤ L ≤ 62.5             : KERNEL-PROVED (implication)
SLAB + TAIL JOIN 42.9 ≤ L ≤ 3727                             : KERNEL-PROVED (implication)
ACTUAL NUMERICAL BOUNDARY CERTIFICATE                        : NOT BUILT (no data banked)
```

This module is **append-only**.

## What the checker is

An **untrusted** external generator may emit a compressed certificate: a finite list of
event boxes covering the slab `429/10 ≤ L ≤ 125/2`, each box listing the active boundary
classes (the datatype of §5) with an exact rational directed upper bound per class.  The
certificate is **data**.  Lean re-checks, by kernel computation, every proposition the
conclusion depends on:

* the boxes are well formed and their declared bounds are nonnegative;
* the boxes *cover* the whole slab (`chainCovers`);
* the boxes do not overlap (unless the certificate explicitly sets `allowOverlap`);
* the directed bounds of each box sum to at most the exact rational budget.

What the checker cannot decide is the **physics**: that inside each box the interior is
consumed by the Möbius collapse of §4 so that only the listed boundary classes remain, and
that each listed class really is dominated by its declared rational bound.  That is exactly
the content of the external `BoundaryDominationInput`, which is a hypothesis socket and is
**never inhabited here**.

## Status coexistence

`BOUNDARY CHECKER : KERNEL-PROVED` coexists with
`BOUNDARY CERTIFICATE : UNINHABITED / NOT YET RUN`: `bankedCertificates = []`
(`no_banked_certificate`), and no `BoundaryDominationInput` is constructed anywhere.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace September4Checker

open September4BoundaryLattice (BoundaryKind)

/-! ## §9  The exact rational budget -/

/-- The universal-pole budget, exactly `1.4164610 × 10⁻⁸`. -/
def poleBudget : ℚ := 14164610 / 10 ^ 15

/-- The remaining oscillatory budget, exactly `9.85835 × 10⁻⁷`. -/
def oscillatoryBudget : ℚ := 985835 / 10 ^ 12

/-- The target: `10⁻⁶`. -/
def targetBudget : ℚ := 1 / 10 ^ 6

/-- **`budget_sum_lt_target`.**  `KERNEL-PROVED`.  The exact rational arithmetic

    1.4164610e-8 + 9.85835e-7  <  1e-6,

with the intended slack retained (the sharper pole value is *not* rounded to 1.417e-8). -/
theorem budget_sum_lt_target : poleBudget + oscillatoryBudget < targetBudget := by
  norm_num [poleBudget, oscillatoryBudget, targetBudget]

/-- The exact rational values, recorded. -/
theorem budget_values :
    poleBudget = 14164610 / 10 ^ 15 ∧ oscillatoryBudget = 985835 / 10 ^ 12 := ⟨rfl, rfl⟩

/-- **`signedFloor_budget_compiler`.**  `KERNEL-PROVED`.  A pure ordered-field statement: if
the pole part and the oscillatory part of the signed remainder are within their budgets
relative to `B_X`, then the whole signed remainder is within `10⁻⁶`. -/
theorem signedFloor_budget_compiler (BX R0 Rosc Rsigned : ℝ) (hB : 0 < BX)
    (hsplit : |Rsigned| ≤ |R0| + |Rosc|)
    (h0 : |R0| / BX < (poleBudget : ℝ)) (hosc : |Rosc| / BX < (oscillatoryBudget : ℝ)) :
    |Rsigned| / BX < 1 / 10 ^ 6 := by
  have hsum : |Rsigned| / BX ≤ |R0| / BX + |Rosc| / BX := by
    rw [← add_div]
    gcongr
  have hlt : |R0| / BX + |Rosc| / BX < (poleBudget : ℝ) + (oscillatoryBudget : ℝ) := by
    exact add_lt_add h0 hosc
  have hbud : ((poleBudget + oscillatoryBudget : ℚ) : ℝ) < ((targetBudget : ℚ) : ℝ) := by
    exact_mod_cast budget_sum_lt_target
  have htarget : ((targetBudget : ℚ) : ℝ) = 1 / 10 ^ 6 := by
    norm_num [targetBudget]
  push_cast at hbud
  linarith

/-! ## §8.1  The certificate datatype -/

/-- One event box of the compressed certificate: an exact rational `L`-interval together
with the complete list of active boundary classes and, for each, a directed rational upper
bound. -/
structure EventBox where
  /-- Lower endpoint of the `L`-interval. -/
  Llo : ℚ
  /-- Upper endpoint of the `L`-interval. -/
  Lhi : ℚ
  /-- The active boundary classes with their declared directed bounds. -/
  entries : List (BoundaryKind × ℚ)
  deriving Repr

/-- The declared total of a box: the sum of its directed bounds. -/
def EventBox.total (b : EventBox) : ℚ := (b.entries.map Prod.snd).sum

/-- A compressed boundary certificate: a finite list of event boxes, plus an explicit flag
saying whether overlapping boxes (which would double-charge) are allowed. -/
structure BoundaryCertificate where
  /-- The event boxes. -/
  boxes : List EventBox
  /-- Whether overlapping boxes are explicitly allowed. -/
  allowOverlap : Bool
  deriving Repr

/-- The exact lower endpoint of the compact slab: `42.9`. -/
def slabLo : ℚ := 429 / 10

/-- The exact upper endpoint of the compact slab: `62.5`. -/
def slabHi : ℚ := 125 / 2

/-! ## §8.2  The decidable checks -/

/-- Coverage check: starting from `x`, each box must begin at or below the current point and
the chain must run past the top of the slab. -/
def chainCovers : ℚ → List EventBox → Bool
  | _, [] => false
  | x, [b] => decide (b.Llo ≤ x) && decide (slabHi ≤ b.Lhi)
  | x, b :: bs => decide (b.Llo ≤ x) && chainCovers b.Lhi bs

/-- No-overlap check: consecutive boxes must not overlap. -/
def nonOverlapping : List EventBox → Bool
  | [] => true
  | [_] => true
  | b :: c :: bs => decide (b.Lhi ≤ c.Llo) && nonOverlapping (c :: bs)

/-- Per-box check: well-formed interval, nonnegative declared bounds, and a declared total
inside the exact rational budget. -/
def checkBox (b : EventBox) : Bool :=
  decide (b.Llo ≤ b.Lhi) && b.entries.all (fun e => decide (0 ≤ e.2)) &&
    decide (b.total ≤ poleBudget + oscillatoryBudget)

/-- The complete checker.  Everything it verifies is decided by kernel computation. -/
def checkCert (c : BoundaryCertificate) : Bool :=
  c.boxes.all checkBox && chainCovers slabLo c.boxes &&
    (c.allowOverlap || nonOverlapping c.boxes)

/-! ## §8.3  Soundness of the coverage check -/

/-- **`chainCovers_sound`.**  `KERNEL-PROVED`.  If the coverage check succeeds from `x`, then
every real point of `[x, slabHi]` lies in one of the boxes. -/
theorem chainCovers_sound : ∀ (bs : List EventBox) (x : ℚ), chainCovers x bs = true →
    ∀ L : ℝ, (x : ℝ) ≤ L → L ≤ (slabHi : ℝ) →
      ∃ b ∈ bs, (b.Llo : ℝ) ≤ L ∧ L ≤ (b.Lhi : ℝ) := by
  intro bs
  induction bs with
  | nil =>
      intro x hx
      simp [chainCovers] at hx
  | cons b bs ih =>
      intro x hx L hL hL'
      match bs, ih with
      | [], _ =>
          simp only [chainCovers, Bool.and_eq_true, decide_eq_true_eq] at hx
          obtain ⟨hb, htop⟩ := hx
          have hblo : (b.Llo : ℝ) ≤ (x : ℝ) := by exact_mod_cast hb
          have hbhi : (slabHi : ℝ) ≤ (b.Lhi : ℝ) := by exact_mod_cast htop
          exact ⟨b, List.mem_cons_self, le_trans hblo hL, le_trans hL' hbhi⟩
      | c :: t, ih =>
          simp only [chainCovers, Bool.and_eq_true, decide_eq_true_eq] at hx
          obtain ⟨hb, hrest⟩ := hx
          have hblo : (b.Llo : ℝ) ≤ (x : ℝ) := by exact_mod_cast hb
          by_cases hcase : L ≤ (b.Lhi : ℝ)
          · exact ⟨b, List.mem_cons_self, le_trans hblo hL, hcase⟩
          · obtain ⟨b', hb', h1, h2⟩ := ih b.Lhi hrest L (le_of_not_ge hcase) hL'
            exact ⟨b', List.mem_cons_of_mem _ hb', h1, h2⟩

/-- **`checker_coverage`.**  `KERNEL-PROVED`.  A certificate that passes the checker covers
the whole compact slab `[42.9, 62.5]`. -/
theorem checker_coverage (c : BoundaryCertificate) (h : checkCert c = true) {L : ℝ}
    (hL : (slabLo : ℝ) ≤ L) (hL' : L ≤ (slabHi : ℝ)) :
    ∃ b ∈ c.boxes, (b.Llo : ℝ) ≤ L ∧ L ≤ (b.Lhi : ℝ) := by
  have hcov : chainCovers slabLo c.boxes = true := by
    simp only [checkCert, Bool.and_eq_true] at h
    exact h.1.2
  exact chainCovers_sound c.boxes slabLo hcov L hL hL'

/-! ## §8.4  The external domination input (uninhabited) -/

/-- **External hypothesis socket.**  What the *checker* cannot decide: that inside each box
the interior divisor assignments are consumed by the Möbius collapse of §4, leaving only the
listed boundary classes, and that every listed class is dominated by its declared rational
bound.  This development builds **no inhabitant** of this structure. -/
structure BoundaryDominationInput (c : BoundaryCertificate) where
  /-- The true directed contribution of a boundary class at a point of the slab. -/
  contrib : ℝ → BoundaryKind → ℝ
  /-- The signed-floor ratio `|R_{B,floor}| / B_X` at a point of the slab. -/
  floorRatio : ℝ → ℝ
  /-- Boundary-only residual: after the interior collapse, the ratio is at most the sum of
  the contributions of the classes listed in the covering box. -/
  boundary_only : ∀ b ∈ c.boxes, ∀ L : ℝ, (b.Llo : ℝ) ≤ L → L ≤ (b.Lhi : ℝ) →
    floorRatio L ≤ (b.entries.map (fun e => contrib L e.1)).sum
  /-- Each listed class is dominated by its declared directed rational bound. -/
  dominates : ∀ b ∈ c.boxes, ∀ L : ℝ, (b.Llo : ℝ) ≤ L → L ≤ (b.Lhi : ℝ) →
    ∀ e ∈ b.entries, contrib L e.1 ≤ (e.2 : ℝ)

/-- List-level monotonicity used by the checker: a list of real contributions dominated
entrywise by declared rational bounds sums to at most the declared total. -/
theorem list_contrib_le_total (f : BoundaryKind → ℝ) :
    ∀ (l : List (BoundaryKind × ℚ)), (∀ e ∈ l, f e.1 ≤ (e.2 : ℝ)) →
      (l.map (fun e => f e.1)).sum ≤ (((l.map Prod.snd).sum : ℚ) : ℝ) := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons e l ih =>
      intro h
      have h1 : f e.1 ≤ (e.2 : ℝ) := h e List.mem_cons_self
      have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp only [List.map_cons, List.sum_cons, Rat.cast_add]
      linarith

/-! ## §8.5  The main checker theorem -/

/-- **`boundaryCertificateChecker_sound`.**  `KERNEL-PROVED`.  If the certificate passes the
kernel checker *and* the external domination input is supplied, then the signed floor ratio
is below `10⁻⁶` at every point of the compact slab.

Everything the conclusion depends on is re-checked in Lean: coverage, per-box bound
nonnegativity, and the exact rational budget arithmetic.  The untrusted generator supplies
data only. -/
theorem boundaryCertificateChecker_sound (c : BoundaryCertificate) (h : checkCert c = true)
    (D : BoundaryDominationInput c) {L : ℝ} (hL : (slabLo : ℝ) ≤ L) (hL' : L ≤ (slabHi : ℝ)) :
    D.floorRatio L < 1 / 10 ^ 6 := by
  obtain ⟨b, hb, h1, h2⟩ := checker_coverage c h hL hL'
  have hall : ∀ x ∈ c.boxes, checkBox x = true := by
    simp only [checkCert, Bool.and_eq_true] at h
    exact fun x hx => List.all_eq_true.1 h.1.1 x hx
  have hbox := hall b hb
  simp only [checkBox, Bool.and_eq_true, decide_eq_true_eq] at hbox
  have hbtotal : b.total ≤ poleBudget + oscillatoryBudget := hbox.2
  have hstep1 := D.boundary_only b hb L h1 h2
  have hstep2 := list_contrib_le_total (D.contrib L) b.entries (D.dominates b hb L h1 h2)
  have hstep3 : ((b.total : ℚ) : ℝ) < 1 / 10 ^ 6 := by
    have : (b.total : ℚ) < targetBudget := lt_of_le_of_lt hbtotal budget_sum_lt_target
    have hcast : ((b.total : ℚ) : ℝ) < ((targetBudget : ℚ) : ℝ) := by exact_mod_cast this
    have : ((targetBudget : ℚ) : ℝ) = 1 / 10 ^ 6 := by norm_num [targetBudget]
    linarith
  have : D.floorRatio L ≤ ((b.total : ℚ) : ℝ) := le_trans hstep1 (by
    simpa [EventBox.total] using hstep2)
  linarith

/-! ## §10  Conditional compact-slab closure, and the join with the tail -/

/-- The compact-slab conclusion: the supplied signed-floor ratio is below `10⁻⁶` throughout
`42.9 ≤ L ≤ 62.5`. -/
def CompactSlabSignedFloorBound (ratio : ℝ → ℝ) : Prop :=
  ∀ L : ℝ, (slabLo : ℝ) ≤ L → L ≤ (slabHi : ℝ) → ratio L < 1 / 10 ^ 6

/-- Validity of a certificate: it passes the kernel checker *and* its external inputs have
been discharged (the domination input).  Note that this is a `Type`-valued bundle precisely
because the second component is an external socket, and it is never inhabited here. -/
structure BoundaryCertificateValid (c : BoundaryCertificate) where
  /-- The kernel checker accepts the data. -/
  checked : checkCert c = true
  /-- The external analytic/computational input listed by the certificate. -/
  domination : BoundaryDominationInput c

/-- **`boundaryCertificateValid_implies_compactSlab`** (§10).  `KERNEL-PROVED` *implication*.

    BoundaryCertificateValid c  →  CompactSlabSignedFloorBound (ratio of c).

It concludes only the compact-slab budget statement, and only provided every external input
listed in the certificate has been discharged. -/
theorem boundaryCertificateValid_implies_compactSlab (c : BoundaryCertificate)
    (V : BoundaryCertificateValid c) : CompactSlabSignedFloorBound V.domination.floorRatio :=
  fun _ hL hL' => boundaryCertificateChecker_sound c V.checked V.domination hL hL'

/-- **`slab_and_tail_join`** (§10 + §11).  `KERNEL-PROVED` *implication*.  The conditional
compact-slab bound and the kernel-proved tail envelope combine to `|ratio| < 10⁻⁶` on the
whole range `42.9 ≤ L ≤ 3727`. -/
theorem slab_and_tail_join (ratio : ℝ → ℝ)
    (hslab : CompactSlabSignedFloorBound ratio)
    (hdom : ∀ L ∈ Set.Icc (125 / 2 : ℝ) 3727, ratio L ≤ September4LargeLTail.envelope L)
    {L : ℝ} (hL : (429 / 10 : ℝ) ≤ L) (hL' : L ≤ 3727) : ratio L < 1 / 10 ^ 6 := by
  by_cases hcase : L ≤ (125 / 2 : ℝ)
  · refine hslab L ?_ ?_
    · simpa [slabLo] using hL
    · simpa [slabHi] using hcase
  · exact September4LargeLTail.largeL_tail_compiler ratio hdom
      ⟨le_of_not_ge hcase, hL'⟩

/-! ## §8.6  No numerical certificate is banked -/

/-- The bank of actual numerical boundary certificates: **empty**.  No externally generated
certificate data has been supplied or kernel-checked in this run. -/
def bankedCertificates : List BoundaryCertificate := []

/-- **`no_banked_certificate`.**  `KERNEL-PROVED`.  The certificate bank is empty: the
checker is proved sound, but no actual certificate exists. -/
theorem no_banked_certificate : bankedCertificates = [] := rfl

/-- A **structural** demonstration that the checker is not vacuous: a single box spanning
the slab with an *empty* class list passes the syntactic checks.  It carries **no physical
content**: an empty class list asserts that no boundary class is active, which only the
(uninhabited) `BoundaryDominationInput` could certify.  It is deliberately *not* placed in
`bankedCertificates`. -/
def structuralDemoCertificate : BoundaryCertificate :=
  { boxes := [{ Llo := 429 / 10, Lhi := 125 / 2, entries := [] }], allowOverlap := false }

theorem structuralDemoCertificate_checks : checkCert structuralDemoCertificate = true := by
  norm_num [checkCert, structuralDemoCertificate, chainCovers, nonOverlapping, checkBox,
    EventBox.total, slabLo, slabHi, poleBudget, oscillatoryBudget]

/-- The demonstration certificate declares no boundary classes at all, hence carries no
numerical boundary information. -/
theorem structuralDemoCertificate_has_no_classes :
    ∀ b ∈ structuralDemoCertificate.boxes, b.entries = [] := by
  decide

end September4Checker
end Erdos287
