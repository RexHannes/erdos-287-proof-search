import Mathlib

/-!
# Erdős #287 — the one-low/four-high five-prime source geometry (§65)

INTERNAL #287 EFFECTIVITY PROGRAMME ONLY.  Nothing here claims Erdős #287.

This module gives the **finite, exact-rational kernel model** of the one-low/four-high
five-prime leakage cell used by the high-`X` source ledger.  Everything below is a statement
about the definitions introduced *in this file*: the file fixes the conventions (endpoint
conventions included) and then proves the combinatorial facts that the ledger consumes.
No analytic statement is proved or assumed here.

## Conventions fixed by this file

A **cell** carries five exponents: one *low* exponent `a` and four *high* exponents
`h 0, …, h 3`, normalised by `a + ∑ h i = 1` (the prime `p i` has size `X ^ (exponent)`).
The legal *one-low/four-high* region is

```
0 < a ≤ 1/10,      1/5 ≤ h i ≤ 3/10,      a + ∑ h i = 1.
```

The low prime is **pinned** to the fixed side of the factorisation (this is what "one-low"
means physically), so a divisor assignment is a subset `S ⊆ Fin 4` of the four high primes,
with exponent `σ S = ∑_{i ∈ S} h i`.

The directed product window has half-width `δ` and the leakage collar half-width `δ'`,
with `0 < δ < δ' ≤ 1/10`.  The three labelled counts use **closed** window endpoints and
**half-open** collars, and are pairwise disjoint by construction:

```
N1 = #{S : 1/2 - δ' ≤ σ S < 1/2 - δ}      (lower collar)
N2 = #{S : 1/2 - δ  ≤ σ S ≤ 1/2 + δ}      (product window)
N3 = #{S : 1/2 + δ  <  σ S ≤ 1/2 + δ'}    (upper collar)
```

and the divisor-assignment invariant is

```
H = N2 - N1 - N3   (an integer).
```

## What is proved

* `H_def` — the divisor-assignment formula, by definition.
* `three_counts_le_sixteen`, `H_abs_le_sixteen` — unconditional bounds.
* `balanced_counts_window`, `balanced_counts_collar`, `balanced_counts_outside` — the exact
  values of `(N1, N2, N3)` in the balanced chamber (`h` constant), for each of the three
  positions of `a` relative to the window and collar.
* `signSeparation_balanced` — on the balanced chamber, `N1 + N3 > 0 → N2 = 0`.
* `H_mem_balanced`, `H_abs_le_six_balanced` — on the balanced chamber `H ∈ {-6, 0, 6}`.
* `plusSix_cell_H`, `plusSix_cell_legal` — the explicit `+6` cell.
* `straddle_witness` — an explicit *unbalanced* legal cell with `N1 > 0` and `N2 > 0`:
  sign separation genuinely needs the balanced chamber and is not a formal triviality.
* `separationCost_le_six`, `plusSix_separationCost` — the separation-cost certificate.
* `plusSix_representation_exact` — representation error `= 0` on the `+6` cell.
* `prodBox_injective`, `fivePrimeBox_unique_factorisation` — unique factorisation in
  disjoint prime boxes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace SourceGeometry

/-! ## §65.1  Cells and the legal one-low/four-high region -/

/-- A five-prime source cell: one low exponent and four high exponents (exact rationals). -/
structure Cell where
  /-- the low exponent -/
  a : ℚ
  /-- the four high exponents -/
  h : Fin 4 → ℚ

/-- The **legal one-low/four-high region**: exact rational chamber conditions. -/
def OneLowFourHigh (c : Cell) : Prop :=
  0 < c.a ∧ c.a ≤ 1/10 ∧ (∀ i, 1/5 ≤ c.h i ∧ c.h i ≤ 3/10) ∧ c.a + ∑ i, c.h i = 1

/-- The **balanced chamber**: the four high exponents coincide. -/
def Balanced (c : Cell) : Prop := ∀ i j, c.h i = c.h j

/-- The exponent of the divisor assignment `S` (the low prime is pinned to the fixed side). -/
def sigma (c : Cell) (S : Finset (Fin 4)) : ℚ := ∑ i ∈ S, c.h i

/-! ## §65.2  The three labelled counts and the divisor-assignment formula -/

/-- Lower-collar count `N1`. -/
def N1 (c : Cell) (d d' : ℚ) : ℕ :=
  ((univ : Finset (Fin 4)).powerset.filter
    (fun S => 1/2 - d' ≤ sigma c S ∧ sigma c S < 1/2 - d)).card

/-- Product-window count `N2` (closed endpoints). -/
def N2 (c : Cell) (d : ℚ) : ℕ :=
  ((univ : Finset (Fin 4)).powerset.filter
    (fun S => 1/2 - d ≤ sigma c S ∧ sigma c S ≤ 1/2 + d)).card

/-- Upper-collar count `N3`. -/
def N3 (c : Cell) (d d' : ℚ) : ℕ :=
  ((univ : Finset (Fin 4)).powerset.filter
    (fun S => 1/2 + d < sigma c S ∧ sigma c S ≤ 1/2 + d')).card

/-- The **divisor-assignment invariant** `H = N2 - N1 - N3`. -/
def H (c : Cell) (d d' : ℚ) : ℤ :=
  (N2 c d : ℤ) - (N1 c d d' : ℤ) - (N3 c d d' : ℤ)

/-- **`H_def`.**  `KERNEL-PROVED`.  The exact divisor-assignment formula. -/
theorem H_def (c : Cell) (d d' : ℚ) :
    H c d d' = (N2 c d : ℤ) - (N1 c d d' : ℤ) - (N3 c d d' : ℤ) := rfl

/-! ## §65.3  Unconditional bounds -/

/-- **`three_counts_le_sixteen`.**  `KERNEL-PROVED`.  The three labelled regions are pairwise
disjoint, so their total occupancy is at most the number of divisor assignments. -/
theorem three_counts_le_sixteen (c : Cell) (d d' : ℚ) (hd : 0 ≤ d) :
    N1 c d d' + N2 c d + N3 c d d' ≤ 16 := by
  classical
  set A1 := (univ : Finset (Fin 4)).powerset.filter
    (fun S => 1/2 - d' ≤ sigma c S ∧ sigma c S < 1/2 - d) with hA1
  set A2 := (univ : Finset (Fin 4)).powerset.filter
    (fun S => 1/2 - d ≤ sigma c S ∧ sigma c S ≤ 1/2 + d) with hA2
  set A3 := (univ : Finset (Fin 4)).powerset.filter
    (fun S => 1/2 + d < sigma c S ∧ sigma c S ≤ 1/2 + d') with hA3
  have h12 : Disjoint A1 A2 := by
    refine Finset.disjoint_left.2 fun S hS1 hS2 => ?_
    rw [hA1, mem_filter] at hS1
    rw [hA2, mem_filter] at hS2
    linarith [hS1.2.2, hS2.2.1]
  have h13 : Disjoint A1 A3 := by
    refine Finset.disjoint_left.2 fun S hS1 hS3 => ?_
    rw [hA1, mem_filter] at hS1
    rw [hA3, mem_filter] at hS3
    linarith [hS1.2.2, hS3.2.1]  -- disjoint since `0 ≤ d`
  have h23 : Disjoint A2 A3 := by
    refine Finset.disjoint_left.2 fun S hS2 hS3 => ?_
    rw [hA2, mem_filter] at hS2
    rw [hA3, mem_filter] at hS3
    linarith [hS2.2.2, hS3.2.1]
  have hsub : A1 ∪ A2 ∪ A3 ⊆ (univ : Finset (Fin 4)).powerset := by
    intro S hS
    simp only [Finset.mem_union] at hS
    rcases hS with (hS | hS) | hS
    · exact (mem_filter.1 hS).1
    · exact (mem_filter.1 hS).1
    · exact (mem_filter.1 hS).1
  have hcard : (A1 ∪ A2 ∪ A3).card = A1.card + A2.card + A3.card := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨h13, h23⟩),
      Finset.card_union_of_disjoint h12]
  have hle : (A1 ∪ A2 ∪ A3).card ≤ ((univ : Finset (Fin 4)).powerset).card :=
    Finset.card_le_card hsub
  rw [hcard] at hle
  simpa [N1, N2, N3, hA1, hA2, hA3] using hle

/-- **`H_abs_le_sixteen`.**  `KERNEL-PROVED`.  Unconditional bound on the invariant. -/
theorem H_abs_le_sixteen (c : Cell) (d d' : ℚ) (hd : 0 ≤ d) : |H c d d'| ≤ 16 := by
  have hsum := three_counts_le_sixteen c d d' hd
  have h1 : (N1 c d d' : ℤ) + (N2 c d : ℤ) + (N3 c d d' : ℤ) ≤ 16 := by exact_mod_cast hsum
  have p1 : (0 : ℤ) ≤ (N1 c d d' : ℤ) := Int.natCast_nonneg _
  have p2 : (0 : ℤ) ≤ (N2 c d : ℤ) := Int.natCast_nonneg _
  have p3 : (0 : ℤ) ≤ (N3 c d d' : ℤ) := Int.natCast_nonneg _
  rw [abs_le, H]
  constructor <;> omega

/-! ## §65.4  The balanced chamber -/

section Balanced

variable {c : Cell} {d d' : ℚ}

/-- In the balanced chamber every assignment exponent is `#S · h 0`. -/
lemma sigma_balanced (hb : Balanced c) (S : Finset (Fin 4)) :
    sigma c S = (S.card : ℚ) * c.h 0 := by
  rw [sigma, Finset.sum_congr rfl (fun i _ => hb i 0), Finset.sum_const, nsmul_eq_mul]

/-- In the legal balanced chamber the common high exponent is `(1 - a)/4`. -/
lemma h_zero_balanced (hl : OneLowFourHigh c) (hb : Balanced c) :
    c.h 0 = (1 - c.a) / 4 := by
  obtain ⟨-, -, -, hsum⟩ := hl
  have hcast : ∑ i, c.h i = 4 * c.h 0 := by
    rw [Finset.sum_congr rfl (fun i _ => hb i 0), Finset.sum_const, Finset.card_univ]
    simp [nsmul_eq_mul]
  rw [hcast] at hsum
  linarith

variable (hl : OneLowFourHigh c) (hb : Balanced c)
  (hd : 0 < d) (hdd : d < d') (hd' : d' ≤ 1/10)

include hl hb hd hdd hd'

/-- Only pair assignments can meet the collar at all. -/
lemma card_eq_two_of_near_half {S : Finset (Fin 4)}
    (hlo : 1/2 - d' ≤ sigma c S) (hhi : sigma c S ≤ 1/2 + d') : S.card = 2 := by
  have ha0 := hl.1
  have ha1 := hl.2.1
  have hh : c.h 0 = (1 - c.a) / 4 := h_zero_balanced hl hb
  have hs : sigma c S = (S.card : ℚ) * c.h 0 := sigma_balanced hb S
  have hb1 : 9/40 ≤ c.h 0 := by rw [hh]; linarith
  have hb2 : c.h 0 ≤ 1/4 := by rw [hh]; linarith
  have hlow : 2 ≤ S.card := by
    by_contra hcon
    push_neg at hcon
    have hc1 : (S.card : ℚ) ≤ 1 := by
      have : S.card ≤ 1 := by omega
      exact_mod_cast this
    have : (S.card : ℚ) * c.h 0 ≤ 1 * c.h 0 :=
      mul_le_mul_of_nonneg_right hc1 (by linarith)
    rw [hs] at hlo
    linarith
  have hhigh : S.card ≤ 2 := by
    by_contra hcon
    push_neg at hcon
    have hc3 : (3 : ℚ) ≤ (S.card : ℚ) := by
      have : 3 ≤ S.card := by omega
      exact_mod_cast this
    have : (3 : ℚ) * c.h 0 ≤ (S.card : ℚ) * c.h 0 :=
      mul_le_mul_of_nonneg_right hc3 (by linarith)
    rw [hs] at hhi
    linarith
  omega

omit hd hdd hd' in
/-- On a pair, the exponent is exactly `1/2 - a/2`. -/
lemma sigma_pair (S : Finset (Fin 4)) (hS : S.card = 2) :
    sigma c S = 1/2 - c.a/2 := by
  rw [sigma_balanced hb S, hS, h_zero_balanced hl hb]
  push_cast
  ring

omit hl hb hd hdd hd' in
/-- The set of pair assignments has `6` elements. -/
lemma card_pairs :
    ((univ : Finset (Fin 4)).powerset.filter (fun S => S.card = 2)).card = 6 := by
  decide

/-- A near-half count that every pair meets equals `6`. -/
lemma count_eq_six (P : Finset (Fin 4) → Prop) [DecidablePred P]
    (hP : ∀ S, P S → 1/2 - d' ≤ sigma c S ∧ sigma c S ≤ 1/2 + d')
    (hall : ∀ S, S.card = 2 → P S) :
    ((univ : Finset (Fin 4)).powerset.filter P).card = 6 := by
  have hset : (univ : Finset (Fin 4)).powerset.filter P
      = (univ : Finset (Fin 4)).powerset.filter (fun S => S.card = 2) := by
    ext S
    simp only [mem_filter, mem_powerset, Finset.subset_univ, true_and]
    constructor
    · intro hS
      exact card_eq_two_of_near_half hl hb hd hdd hd' (hP S hS).1 (hP S hS).2
    · exact hall S
  rw [hset, card_pairs]

/-- A near-half count that no pair meets is `0`. -/
lemma count_eq_zero (P : Finset (Fin 4) → Prop) [DecidablePred P]
    (hP : ∀ S, P S → 1/2 - d' ≤ sigma c S ∧ sigma c S ≤ 1/2 + d')
    (hnone : ∀ S, S.card = 2 → ¬ P S) :
    ((univ : Finset (Fin 4)).powerset.filter P).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro S _hS hP'
  exact hnone S (card_eq_two_of_near_half hl hb hd hdd hd' (hP S hP').1 (hP S hP').2) hP'

/-- **`balanced_counts_window`.**  `KERNEL-PROVED`.  If the low exponent is inside twice the
window half-width, all six pair assignments sit in the product window. -/
theorem balanced_counts_window (hin : c.a ≤ 2 * d) :
    N1 c d d' = 0 ∧ N2 c d = 6 ∧ N3 c d d' = 0 := by
  have ha0 := hl.1
  refine ⟨?_, ?_, ?_⟩
  · refine count_eq_zero hl hb hd hdd hd' _ (fun S hS => ⟨hS.1, by linarith [hS.2]⟩)
      (fun S hS hcon => ?_)
    rw [sigma_pair hl hb S hS] at hcon
    linarith [hcon.2]
  · refine count_eq_six hl hb hd hdd hd' _
      (fun S hS => ⟨by linarith [hS.1], by linarith [hS.2]⟩) (fun S hS => ?_)
    rw [sigma_pair hl hb S hS]
    constructor <;> linarith
  · refine count_eq_zero hl hb hd hdd hd' _ (fun S hS => ⟨by linarith [hS.1], hS.2⟩)
      (fun S hS hcon => ?_)
    rw [sigma_pair hl hb S hS] at hcon
    linarith [hcon.1]

/-- **`balanced_counts_collar`.**  `KERNEL-PROVED`.  If the low exponent leaves the window but
stays inside the collar, all six pair assignments sit in the lower collar. -/
theorem balanced_counts_collar (hlo : 2 * d < c.a) (hhi : c.a ≤ 2 * d') :
    N1 c d d' = 6 ∧ N2 c d = 0 ∧ N3 c d d' = 0 := by
  have ha0 := hl.1
  refine ⟨?_, ?_, ?_⟩
  · refine count_eq_six hl hb hd hdd hd' _ (fun S hS => ⟨hS.1, by linarith [hS.2]⟩)
      (fun S hS => ?_)
    rw [sigma_pair hl hb S hS]
    constructor <;> linarith
  · refine count_eq_zero hl hb hd hdd hd' _
      (fun S hS => ⟨by linarith [hS.1], by linarith [hS.2]⟩) (fun S hS hcon => ?_)
    rw [sigma_pair hl hb S hS] at hcon
    linarith [hcon.1]
  · refine count_eq_zero hl hb hd hdd hd' _ (fun S hS => ⟨by linarith [hS.1], hS.2⟩)
      (fun S hS hcon => ?_)
    rw [sigma_pair hl hb S hS] at hcon
    linarith [hcon.1]

/-- **`balanced_counts_outside`.**  `KERNEL-PROVED`.  Outside the collar the cell is inert. -/
theorem balanced_counts_outside (hout : 2 * d' < c.a) :
    N1 c d d' = 0 ∧ N2 c d = 0 ∧ N3 c d d' = 0 := by
  have ha0 := hl.1
  refine ⟨?_, ?_, ?_⟩
  · refine count_eq_zero hl hb hd hdd hd' _ (fun S hS => ⟨hS.1, by linarith [hS.2]⟩)
      (fun S hS hcon => ?_)
    rw [sigma_pair hl hb S hS] at hcon
    linarith [hcon.1]
  · refine count_eq_zero hl hb hd hdd hd' _
      (fun S hS => ⟨by linarith [hS.1], by linarith [hS.2]⟩) (fun S hS hcon => ?_)
    rw [sigma_pair hl hb S hS] at hcon
    linarith [hcon.1]
  · refine count_eq_zero hl hb hd hdd hd' _ (fun S hS => ⟨by linarith [hS.1], hS.2⟩)
      (fun S hS hcon => ?_)
    rw [sigma_pair hl hb S hS] at hcon
    linarith [hcon.1]

/-- **`signSeparation_balanced`.**  `KERNEL-PROVED`.  Sign separation on the balanced chamber:
if either collar is occupied then the product window is empty. -/
theorem signSeparation_balanced (hocc : 0 < N1 c d d' + N3 c d d') : N2 c d = 0 := by
  rcases le_or_gt c.a (2 * d) with hcase | hcase
  · obtain ⟨e1, -, e3⟩ := balanced_counts_window hl hb hd hdd hd' hcase
    rw [e1, e3] at hocc; omega
  · rcases le_or_gt c.a (2 * d') with hcase' | hcase'
    · exact (balanced_counts_collar hl hb hd hdd hd' hcase hcase').2.1
    · exact (balanced_counts_outside hl hb hd hdd hd' hcase').2.1

/-- **`H_mem_balanced`.**  `KERNEL-PROVED`.  On the balanced chamber the invariant takes only
the three values `+6`, `0`, `-6`. -/
theorem H_mem_balanced : H c d d' = 6 ∨ H c d d' = 0 ∨ H c d d' = -6 := by
  rcases le_or_gt c.a (2 * d) with hcase | hcase
  · obtain ⟨e1, e2, e3⟩ := balanced_counts_window hl hb hd hdd hd' hcase
    left; rw [H, e1, e2, e3]; rfl
  · rcases le_or_gt c.a (2 * d') with hcase' | hcase'
    · obtain ⟨e1, e2, e3⟩ := balanced_counts_collar hl hb hd hdd hd' hcase hcase'
      right; right; rw [H, e1, e2, e3]; rfl
    · obtain ⟨e1, e2, e3⟩ := balanced_counts_outside hl hb hd hdd hd' hcase'
      right; left; rw [H, e1, e2, e3]; rfl

/-- **`H_abs_le_six_balanced`.**  `KERNEL-PROVED`. -/
theorem H_abs_le_six_balanced : |H c d d'| ≤ 6 := by
  rcases H_mem_balanced hl hb hd hdd hd' with h | h | h <;> rw [h] <;> decide

end Balanced

/-- The **separation cost** of a cell: the number of leaking divisor assignments. -/
def separationCost (c : Cell) (d d' : ℚ) : ℕ := N1 c d d' + N2 c d + N3 c d d'

/-- **`separationCost_le_six`.**  `KERNEL-PROVED`.  The separation-cost certificate on the
balanced chamber. -/
theorem separationCost_le_six {c : Cell} {d d' : ℚ} (hl : OneLowFourHigh c) (hb : Balanced c)
    (hd : 0 < d) (hdd : d < d') (hd' : d' ≤ 1/10) : separationCost c d d' ≤ 6 := by
  rcases le_or_gt c.a (2 * d) with hcase | hcase
  · obtain ⟨e1, e2, e3⟩ := balanced_counts_window hl hb hd hdd hd' hcase
    rw [separationCost, e1, e2, e3]
  · rcases le_or_gt c.a (2 * d') with hcase' | hcase'
    · obtain ⟨e1, e2, e3⟩ := balanced_counts_collar hl hb hd hdd hd' hcase hcase'
      rw [separationCost, e1, e2, e3]
    · obtain ⟨e1, e2, e3⟩ := balanced_counts_outside hl hb hd hdd hd' hcase'
      rw [separationCost, e1, e2, e3]; omega

/-! ## §65.5  The exact `+6` cell -/

/-- The explicit `+6` cell: low exponent `1/50`, four equal high exponents `49/200`. -/
def plusSixCell : Cell := ⟨1/50, fun _ => 49/200⟩

/-- Window half-width of the `+6` cell. -/
def plusSixDelta : ℚ := 1/20

/-- Collar half-width of the `+6` cell. -/
def plusSixDelta' : ℚ := 1/10

/-- **`plusSix_cell_legal`.**  `KERNEL-PROVED`.  The `+6` cell lies in the legal
one-low/four-high region and is balanced. -/
theorem plusSix_cell_legal : OneLowFourHigh plusSixCell ∧ Balanced plusSixCell := by
  refine ⟨⟨by norm_num [plusSixCell], by norm_num [plusSixCell], fun i => ?_, ?_⟩,
    fun i j => rfl⟩
  · constructor <;> norm_num [plusSixCell]
  · show (1/50 : ℚ) + ∑ _i : Fin 4, (49/200 : ℚ) = 1
    rw [Finset.sum_const, Finset.card_univ]
    norm_num

/-- **`plusSix_cell_counts`.**  `KERNEL-PROVED`.  The exact counts on the `+6` cell. -/
theorem plusSix_cell_counts :
    N1 plusSixCell plusSixDelta plusSixDelta' = 0 ∧
      N2 plusSixCell plusSixDelta = 6 ∧
      N3 plusSixCell plusSixDelta plusSixDelta' = 0 :=
  balanced_counts_window plusSix_cell_legal.1 plusSix_cell_legal.2
    (by norm_num [plusSixDelta]) (by norm_num [plusSixDelta, plusSixDelta'])
    (by norm_num [plusSixDelta']) (by norm_num [plusSixCell, plusSixDelta])

/-- **`plusSix_cell_H`.**  `KERNEL-PROVED`.  `H = +6` exactly on the physical cell. -/
theorem plusSix_cell_H : H plusSixCell plusSixDelta plusSixDelta' = 6 := by
  obtain ⟨e1, e2, e3⟩ := plusSix_cell_counts
  rw [H, e1, e2, e3]; rfl

/-- **`plusSix_separationCost`.**  `KERNEL-PROVED`.  Separation cost exactly `6`. -/
theorem plusSix_separationCost :
    separationCost plusSixCell plusSixDelta plusSixDelta' = 6 := by
  obtain ⟨e1, e2, e3⟩ := plusSix_cell_counts
  rw [separationCost, e1, e2, e3]

/-! ## §65.6  Sign separation genuinely needs the balanced chamber -/

/-- An explicit **unbalanced** legal cell whose pair exponents straddle the window edge. -/
def straddleCell : Cell := ⟨1/10, fun i => if (i : ℕ) ≤ 1 then 1/5 else 1/4⟩

/-- **`straddleCell_legal`.**  `KERNEL-PROVED`. -/
theorem straddleCell_legal : OneLowFourHigh straddleCell := by
  refine ⟨by norm_num [straddleCell], by norm_num [straddleCell], fun i => ?_, ?_⟩
  · fin_cases i <;> constructor <;> norm_num [straddleCell]
  · norm_num [straddleCell, Fin.sum_univ_four]

lemma sigma_straddle_01 : sigma straddleCell {0, 1} = 2/5 := by
  rw [sigma, Finset.sum_pair (by decide : (0 : Fin 4) ≠ 1)]
  norm_num [straddleCell]


lemma sigma_straddle_02 : sigma straddleCell {0, 2} = 9/20 := by
  rw [sigma, Finset.sum_pair (by decide : (0 : Fin 4) ≠ 2)]
  norm_num [straddleCell]

/-- **`straddle_witness`.**  `KERNEL-PROVED`.  On this legal but *unbalanced* cell both the
lower collar and the product window are occupied.  Hence sign separation
(`N1 + N3 > 0 → N2 = 0`) is **false** without the balanced-chamber hypothesis: the balanced
restriction in `signSeparation_balanced` is necessary, not cosmetic. -/
theorem straddle_witness :
    0 < N1 straddleCell plusSixDelta plusSixDelta' ∧ 0 < N2 straddleCell plusSixDelta := by
  constructor
  · refine Finset.card_pos.2 ⟨{0, 1}, ?_⟩
    simp only [mem_filter, mem_powerset, Finset.subset_univ, true_and, sigma_straddle_01,
      plusSixDelta, plusSixDelta']
    norm_num
  · refine Finset.card_pos.2 ⟨{0, 2}, ?_⟩
    simp only [mem_filter, mem_powerset, Finset.subset_univ, true_and, sigma_straddle_02,
      plusSixDelta]
    norm_num

/-! ## §65.7  Representation error on the `+6` cell -/

/-- The untwisted box sum of a weight over the assignments inside the product window. -/
def boxSum (c : Cell) (d : ℚ) (w : Finset (Fin 4) → ℚ) : ℚ :=
  ∑ S ∈ (univ : Finset (Fin 4)).powerset.filter
    (fun S => 1/2 - d ≤ sigma c S ∧ sigma c S ≤ 1/2 + d), w S

/-- **`plusSix_representation_exact`.**  `KERNEL-PROVED`.  *Representation error `= 0`.*  If
the six window cells carry a common weight `v` (the symmetry of the balanced cell), then the
box is exactly `6 · v`: the `6`-fold factored representation is exact, with no remainder. -/
theorem plusSix_representation_exact (w : Finset (Fin 4) → ℚ) (v : ℚ)
    (hw : ∀ S ∈ (univ : Finset (Fin 4)).powerset.filter
      (fun S => 1/2 - plusSixDelta ≤ sigma plusSixCell S ∧
        sigma plusSixCell S ≤ 1/2 + plusSixDelta), w S = v) :
    boxSum plusSixCell plusSixDelta w = 6 * v := by
  have hcard : ((univ : Finset (Fin 4)).powerset.filter
      (fun S => 1/2 - plusSixDelta ≤ sigma plusSixCell S ∧
        sigma plusSixCell S ≤ 1/2 + plusSixDelta)).card = 6 := plusSix_cell_counts.2.1
  rw [boxSum, Finset.sum_congr rfl hw, Finset.sum_const, hcard, nsmul_eq_mul]
  norm_num

/-! ## §65.8  Unique factorisation in disjoint prime boxes -/

/-- **`prodBox_injective`.**  `KERNEL-PROVED`.  Distinct primes generate distinct products:
the assignment `S ↦ ∏_{i ∈ S} p i` is injective. -/
theorem prodBox_injective {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) :
    Function.Injective (fun S : Finset (Fin n) => ∏ i ∈ S, p i) := by
  have key : ∀ (U V : Finset (Fin n)), (∏ i ∈ U, p i) = (∏ i ∈ V, p i) → U ⊆ V := by
    intro U V hUV i hi
    have hdvd : p i ∣ ∏ j ∈ U, p j := Finset.dvd_prod_of_mem _ hi
    rw [hUV] at hdvd
    obtain ⟨j, hjV, hj⟩ := (Nat.Prime.prime (hp i)).exists_mem_finset_dvd hdvd
    have hij : p i = p j := (Nat.prime_dvd_prime_iff_eq (hp i) (hp j)).1 hj
    rwa [hinj hij]
  intro S T hST
  simp only at hST
  exact Finset.Subset.antisymm (key S T hST) (key T S hST.symm)

/-- Five labelled prime boxes are *disjoint* when their index intervals are. -/
def DisjointBoxes (lo hi : Fin 5 → ℕ) : Prop :=
  ∀ i j, i ≠ j → (hi i < lo j ∨ hi j < lo i)

/-- **`fivePrimeBox_unique_factorisation`.**  `KERNEL-PROVED`.  Five primes taken from
pairwise disjoint labelled intervals factor uniquely: distinct subsets of the five labels
give distinct products.  This is the exact statement the leakage box needs in order to
identify each divisor assignment with a unique product of source primes. -/
theorem fivePrimeBox_unique_factorisation (lo hi : Fin 5 → ℕ) (hdis : DisjointBoxes lo hi)
    (p : Fin 5 → ℕ) (hp : ∀ i, (p i).Prime) (hmem : ∀ i, lo i ≤ p i ∧ p i ≤ hi i) :
    Function.Injective (fun S : Finset (Fin 5) => ∏ i ∈ S, p i) := by
  refine prodBox_injective p hp ?_
  intro i j hij
  by_contra hne
  rcases hdis i j hne with hcase | hcase
  · have h1 := (hmem i).2
    have h2 := (hmem j).1
    omega
  · have h1 := (hmem j).2
    have h2 := (hmem i).1
    omega

end SourceGeometry
end Erdos287
