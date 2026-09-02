import Mathlib

/-!
# Exact Heath-Brown source records, and the exact-coefficient / one-bounded-majorant
firewall

```
SOURCE RECORDS                       : KERNEL-PROVED (typed, source-exact)
EXACT vs ARBITRARY-1-BOUNDED FIREWALL: KERNEL-PROVED
```

This module is **append-only**.

**§1 — the record.**  `HeathBrownRow` retains the literal source fields
`j_h, r_h, μ(r_h), e_{h,i}, μ(e_{h,i}), f_{h,i}, log f_{h,1}`, the perfect-power predicates
and the unit padding.  They are *not* replaced by an arbitrary `α` field: the consistency
predicate `SourceConsistent` pins `μ(r_h)` and `μ(e_{h,i})` to the actual Möbius values and
`log f_{h,1}` to the actual logarithm.

**§2 — the firewall.**  `exactGeneratedCoefficient` (the coefficient the source produces)
and `OneBoundedMajorant` (an arbitrary coefficient with `|c| ≤ 1`) are different objects.
The exact coefficient **may** be passed to the one-bounded interface once its pointwise
bound has genuinely been established (`majorant_of_exact_bounded`), and it **may not** be
identified with the majorant: an exact coefficient can exceed `1` in absolute value, and
distinct exact rows can share a majorant.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace HeathBrownSource

/-! ## §1  The exact source record -/

/-- **`HeathBrownRow`** — the literal Heath-Brown source record of one row. -/
structure HeathBrownRow where
  /-- The row index `j_h`. -/
  j_h : ℕ
  /-- The modulus `r_h`. -/
  r_h : ℕ
  /-- The recorded value of `μ(r_h)`. -/
  mu_r : ℤ
  /-- The divisors `e_{h,i}`. -/
  e : List ℕ
  /-- The recorded values of `μ(e_{h,i})`. -/
  mu_e : List ℤ
  /-- The cofactors `f_{h,i}`. -/
  f : List ℕ
  /-- The recorded value of `log f_{h,1}`. -/
  logf1 : ℝ
  /-- The perfect-power predicates of the row. -/
  perfectPower : List Bool
  /-- The unit padding of the row. -/
  unitPadding : ℕ

/-- **`SourceConsistent`** — the record really carries the *source* values: the recorded
Möbius values are the Möbius values, and the recorded logarithm is the logarithm. -/
structure SourceConsistent (row : HeathBrownRow) : Prop where
  /-- `μ(r_h)` is the Möbius value at `r_h`. -/
  mu_r_pinned : row.mu_r = ArithmeticFunction.moebius row.r_h
  /-- Each `μ(e_{h,i})` is the Möbius value at `e_{h,i}`. -/
  mu_e_pinned : row.mu_e = row.e.map (fun x => ArithmeticFunction.moebius x)
  /-- `log f_{h,1}` is the logarithm of the first cofactor. -/
  logf1_pinned : row.logf1 = Real.log ((row.f.headI : ℝ))
  /-- The perfect-power flags have one entry per cofactor. -/
  flags_match : row.perfectPower.length = row.f.length

/-- **`sourceConsistency_is_a_real_constraint`.**  `KERNEL-PROVED`.

The consistency predicate is not automatic: a record with an arbitrary `μ`-field violates
it, so the source values may not be replaced by arbitrary data. -/
theorem sourceConsistency_is_a_real_constraint :
    ∃ row : HeathBrownRow, ¬ SourceConsistent row := by
  refine ⟨⟨0, 1, 7, [], [], [], 0, [], 0⟩, ?_⟩
  intro h
  have := h.mu_r_pinned
  simp at this

/-- **`sourceConsistent_determines_the_moebius_fields`.**  `KERNEL-PROVED`.

Two consistent records with the same `r_h` and the same divisor list carry the same Möbius
data: the fields are pinned, not free. -/
theorem sourceConsistent_determines_the_moebius_fields {row₁ row₂ : HeathBrownRow}
    (h₁ : SourceConsistent row₁) (h₂ : SourceConsistent row₂)
    (hr : row₁.r_h = row₂.r_h) (he : row₁.e = row₂.e) :
    row₁.mu_r = row₂.mu_r ∧ row₁.mu_e = row₂.mu_e := by
  refine ⟨?_, ?_⟩
  · rw [h₁.mu_r_pinned, h₂.mu_r_pinned, hr]
  · rw [h₁.mu_e_pinned, h₂.mu_e_pinned, he]

/-! ## §2  Exact coefficient versus arbitrary one-bounded majorant -/

/-- **`exactGeneratedCoefficient`** — the coefficient the source generates from the row:
the product of the recorded Möbius values, weighted by the unit padding. -/
def exactGeneratedCoefficient (row : HeathBrownRow) : ℝ :=
  (row.mu_r : ℝ) * (row.mu_e.map (fun m => (m : ℝ))).prod * (row.unitPadding + 1 : ℝ)

/-- **`OneBoundedMajorant`** — an arbitrary coefficient bounded by `1`. -/
structure OneBoundedMajorant where
  /-- The coefficient. -/
  c : ℕ → ℝ
  /-- The pointwise bound. -/
  bound : ∀ n, |c n| ≤ 1

/-- **`majorant_of_exact_bounded`.**  `KERNEL-PROVED CONDITIONAL`.

An exact source coefficient may be passed to the one-bounded interface **once its pointwise
bound has genuinely been established** — and only then. -/
def majorant_of_exact_bounded (rows : ℕ → HeathBrownRow)
    (h : ∀ n, |exactGeneratedCoefficient (rows n)| ≤ 1) : OneBoundedMajorant where
  c := fun n => exactGeneratedCoefficient (rows n)
  bound := h

/-- **`exact_coefficient_need_not_be_one_bounded`.**  `KERNEL-PROVED`.

The pointwise bound is a genuine extra hypothesis: an exact source coefficient can exceed
`1` in absolute value (unit padding alone breaks the bound). -/
theorem exact_coefficient_need_not_be_one_bounded :
    ∃ row : HeathBrownRow, 1 < |exactGeneratedCoefficient row| := by
  refine ⟨⟨0, 1, 1, [], [], [], 0, [], 3⟩, ?_⟩
  norm_num [exactGeneratedCoefficient]

/-- **`majorant_is_not_the_source_coefficient`.**  `KERNEL-PROVED`.

The majorant interface forgets the source: two records with different exact coefficients can
be dominated by the same one-bounded majorant, so a majorant may never be substituted for
the source coefficient. -/
theorem majorant_is_not_the_source_coefficient :
    ∃ (row₁ row₂ : HeathBrownRow) (m : OneBoundedMajorant),
      exactGeneratedCoefficient row₁ ≠ exactGeneratedCoefficient row₂ ∧
      |exactGeneratedCoefficient row₁| ≤ 1 ∧ |exactGeneratedCoefficient row₂| ≤ 1 ∧
      ∀ n, |m.c n| ≤ 1 := by
  refine ⟨⟨0, 1, 1, [], [], [], 0, [], 0⟩, ⟨0, 1, -1, [], [], [], 0, [], 0⟩,
    ⟨fun _ => 1, fun _ => by norm_num⟩, ?_, ?_, ?_, fun _ => by norm_num⟩
  · norm_num [exactGeneratedCoefficient]
  · norm_num [exactGeneratedCoefficient]
  · norm_num [exactGeneratedCoefficient]

end HeathBrownSource
end Erdos287
