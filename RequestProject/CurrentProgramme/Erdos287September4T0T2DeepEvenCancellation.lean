import RequestProject.CurrentProgramme.Erdos287September3TotTwoAdicMobiusPairing

/-!
# Erdős #287 — September-4 signed-floor bank, §3: `T⁰ − T²` deep-even cancellation

```
EXACT r = 2u REINDEXING (same physical n)          : KERNEL-PROVED
B_src(2m) = B_src(m) COLLAPSE (explicit hypothesis): KERNEL-PROVED
T⁰ − T² ODD / EVEN-COLLAR DECOMPOSITION            : KERNEL-PROVED
DEEP-EVEN EXACT CANCELLATION (t0t2DeepEvenCancellation45) : KERNEL-PROVED
COMPLETE SIGNED-FLOOR CLOSURE                      : NOT ASSERTED (firewall below)
```

This module is **append-only** and consumes the already kernel-proved September-3 source
split `T = T⁰ − T²` (`Erdos287.September3TwoAdicPairing.totLaneSourceSplit`); it re-proves
nothing of that layer and changes no earlier statement.

## Setting

Fix an **odd** modulus `d`, a finite set `R` of quotients `r` (so the physical variable is
`n = d·r`), a supplied source coefficient `κ(d; n)`, a supplied weight `Wt n` (physically
`W(n/X)` for the weight of §1), a supplied `B_src`, and a supplied split datum `Y n`
(physically `⌊n^γ⌋`).  Every indicator is written in the project's `if _ then 1 else 0`
style.

    T⁰ = ∑_{r ∈ R}                κ(d;dr) · Wt(dr) · B_src(dr) · 1_{d ≤ Y(dr)}
    T² = ∑_{r ∈ R, r even}        κ(d;dr) · Wt(dr) · B_src(dr) · 1_{2d ≤ Y(dr)}

The family-`2` index condition is `2d ∣ n`, which for odd `d` and `n = d·r` is *exactly*
`r` even (`two_mul_dvd_iff_even`), and the reindexing `r = 2u` identifies the even part of
`T⁰` with `T²` at the *same* physical `n = d·r = 2·d·u`, the *same* `κ(d;n)`, the *same*
supplied weight `Wt(n)` and — by the explicit hypothesis `B_src(2m) = B_src(m)` — the same
`B_src` value.

## Firewall

    deep-even cancellation  ≠  complete signed-floor closure.

The theorem below cancels exactly those even-`r` terms with `2d ≤ Y(dr)`.  The remaining
**even collar** `d ≤ Y(dr) < 2d` and the whole odd family survive; nothing in this file
bounds them, and no signed-floor bound is claimed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace September4T0T2

/-! ## §3.1  Source terms -/

/-- The project-style indicator of a decidable proposition. -/
def ind (P : Prop) [Decidable P] : ℝ := if P then 1 else 0

@[simp] theorem ind_true {P : Prop} [Decidable P] (h : P) : ind P = 1 := if_pos h

@[simp] theorem ind_false {P : Prop} [Decidable P] (h : ¬ P) : ind P = 0 := if_neg h

/-- The common physical source term at `n = d·r`:  `κ(d;n) · Wt(n) · B_src(n)`.
`T⁰` and `T²` differ **only** in the attached indicator. -/
def srcTerm (kappa : ℕ → ℕ → ℝ) (Wt B : ℕ → ℝ) (d r : ℕ) : ℝ :=
  kappa d (d * r) * Wt (d * r) * B (d * r)

/-- The family-`0` sum. -/
def T0 (kappa : ℕ → ℕ → ℝ) (Wt B : ℕ → ℝ) (Y : ℕ → ℕ) (d : ℕ) (R : Finset ℕ) : ℝ :=
  ∑ r ∈ R, srcTerm kappa Wt B d r * ind (d ≤ Y (d * r))

/-- The family-`2` sum: the index condition `2d ∣ n` has been rewritten as `r` even
(legitimate for odd `d`, see `two_mul_dvd_iff_even`). -/
def T2 (kappa : ℕ → ℕ → ℝ) (Wt B : ℕ → ℝ) (Y : ℕ → ℕ) (d : ℕ) (R : Finset ℕ) : ℝ :=
  ∑ r ∈ R.filter (fun r => Even r), srcTerm kappa Wt B d r * ind (2 * d ≤ Y (d * r))

/-! ## §3.2  The explicit source facts -/

/-- **`two_mul_dvd_iff_even`.**  `KERNEL-PROVED`.  For odd `d` and `n = d·r`, the family-`2`
index condition `2d ∣ n` is *exactly* the evenness of `r`. -/
theorem two_mul_dvd_iff_even {d r : ℕ} (hd : Odd d) : 2 * d ∣ d * r ↔ Even r := by
  constructor
  · rintro ⟨k, hk⟩
    have hd0 : d ≠ 0 := by rintro rfl; simp at hd
    have : r = 2 * k := by
      have : d * r = d * (2 * k) := by rw [hk]; ring
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd0) this
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hk]; ring⟩

/-- **`same_physical_n`.**  `KERNEL-PROVED`.  The reindexing `r = 2u` keeps the physical
variable: `n = d·r = 2·d·u`. -/
theorem same_physical_n (d u : ℕ) : d * (2 * u) = 2 * d * u := by ring

/-- **`kappa_reindex`.**  `KERNEL-PROVED`.  Consequently the source coefficient is the same
on both sides of the reindexing. -/
theorem kappa_reindex (kappa : ℕ → ℕ → ℝ) (d u : ℕ) :
    kappa d (d * (2 * u)) = kappa d (2 * d * u) := by rw [same_physical_n]

/-- **`weight_reindex`.**  `KERNEL-PROVED`.  The supplied weight `Wt` (physically `W(n/X)`)
is the same on both sides, because the physical `n` is the same. -/
theorem weight_reindex (Wt : ℕ → ℝ) (d u : ℕ) : Wt (d * (2 * u)) = Wt (2 * d * u) := by
  rw [same_physical_n]

/-- **`Bsrc_even_collapse`.**  `KERNEL-PROVED`.  Under the explicit source hypothesis
`B_src(2m) = B_src(m)`, the reindexed `B_src` value is the odd-part value. -/
theorem Bsrc_even_collapse {B : ℕ → ℝ} (hB : ∀ m, B (2 * m) = B m) (d u : ℕ) :
    B (d * (2 * u)) = B (d * u) := by
  rw [show d * (2 * u) = 2 * (d * u) by ring, hB]

/-- **`evenPart_reindex`.**  `KERNEL-PROVED`.  The exact `r = 2u` reindexing of a sum over
the even part of `R`. -/
theorem evenPart_reindex (R : Finset ℕ) (f : ℕ → ℝ) :
    ∑ r ∈ R.filter (fun r => Even r), f r
      = ∑ u ∈ (R.filter (fun r => Even r)).image (fun r => r / 2), f (2 * u) := by
  classical
  refine Finset.sum_nbij' (fun r => r / 2) (fun u => 2 * u) ?_ ?_ ?_ ?_ ?_
  · intro a ha; exact Finset.mem_image_of_mem _ ha
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨k, hk⟩ := (Finset.mem_filter.1 ha).2
    simp only
    have h2 : 2 * (a / 2) = a := by omega
    rw [h2]; exact ha
  · intro a ha
    obtain ⟨k, hk⟩ := (Finset.mem_filter.1 ha).2
    simp only
    omega
  · intro b _; simp only; omega
  · intro a ha
    obtain ⟨k, hk⟩ := (Finset.mem_filter.1 ha).2
    simp only
    have h2 : 2 * (a / 2) = a := by omega
    rw [h2]

/-! ## §3.3  The exact `T⁰ − T²` decomposition -/

/-- **`t0t2SourceDecomposition`.**  `KERNEL-PROVED`.  The exact decomposition

    T⁰ − T² = ∑_{r odd}  κ·Wt·B_src · 1_{d ≤ Y(dr)}
            + ∑_{r even} κ·Wt·B_src · 1_{d ≤ Y(dr) < 2d}.

No absolute value and no estimate is used; this is an identity of finite sums. -/
theorem t0t2SourceDecomposition (kappa : ℕ → ℕ → ℝ) (Wt B : ℕ → ℝ) (Y : ℕ → ℕ)
    (d : ℕ) (R : Finset ℕ) :
    T0 kappa Wt B Y d R - T2 kappa Wt B Y d R
      = (∑ r ∈ R.filter (fun r => ¬ Even r),
            srcTerm kappa Wt B d r * ind (d ≤ Y (d * r)))
        + ∑ r ∈ R.filter (fun r => Even r),
            srcTerm kappa Wt B d r * ind (d ≤ Y (d * r) ∧ Y (d * r) < 2 * d) := by
  classical
  have hsplit :
      T0 kappa Wt B Y d R
        = (∑ r ∈ R.filter (fun r => ¬ Even r),
              srcTerm kappa Wt B d r * ind (d ≤ Y (d * r)))
          + ∑ r ∈ R.filter (fun r => Even r),
              srcTerm kappa Wt B d r * ind (d ≤ Y (d * r)) := by
    rw [add_comm]
    exact (Finset.sum_filter_add_sum_filter_not R (fun r => Even r) _).symm
  rw [hsplit, T2, add_sub_assoc, ← Finset.sum_sub_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun r _ => ?_)
  rw [← mul_sub]
  congr 1
  by_cases h2 : 2 * d ≤ Y (d * r)
  · have h1 : d ≤ Y (d * r) := le_trans (by omega) h2
    simp [ind, h1, h2, not_lt.2 h2]
  · by_cases h1 : d ≤ Y (d * r)
    · simp [ind, h1, h2, not_le.1 h2]
    · simp [ind, h1, h2]

/-- **`deepTerm_cancel`.**  `KERNEL-PROVED`.  Termwise deep cancellation: once the split
datum is at depth `2d ≤ Y(dr)`, the `T⁰` and the `T²` contribution of that `r` are literally
equal, so their difference vanishes.  (Evenness of `r` is what places the term in the `T²`
index set in the first place; it is not needed for the termwise identity, and the aggregated
statement `t0t2DeepEvenCancellation45` below quantifies over the even family.) -/
theorem deepTerm_cancel (kappa : ℕ → ℕ → ℝ) (Wt B : ℕ → ℝ) (Y : ℕ → ℕ)
    (d r : ℕ) (hdeep : 2 * d ≤ Y (d * r)) :
    srcTerm kappa Wt B d r * ind (d ≤ Y (d * r))
      - srcTerm kappa Wt B d r * ind (2 * d ≤ Y (d * r)) = 0 := by
  have h1 : d ≤ Y (d * r) := le_trans (by omega) hdeep
  simp [ind, h1, hdeep]

/-- **`t0t2DeepEvenCancellation45`.**  `KERNEL-PROVED`.  *Deep-even cancellation.*  The part
of `T⁰ − T²` indexed by even `r` with `2d ≤ Y(dr)` vanishes **exactly**. -/
theorem t0t2DeepEvenCancellation45 (kappa : ℕ → ℕ → ℝ) (Wt B : ℕ → ℝ) (Y : ℕ → ℕ)
    (d : ℕ) (R : Finset ℕ) :
    ∑ r ∈ R.filter (fun r => Even r ∧ 2 * d ≤ Y (d * r)),
        (srcTerm kappa Wt B d r * ind (d ≤ Y (d * r))
          - srcTerm kappa Wt B d r * ind (2 * d ≤ Y (d * r))) = 0 := by
  classical
  refine Finset.sum_eq_zero fun r hr => ?_
  obtain ⟨-, -, hr2⟩ := Finset.mem_filter.1 hr
  exact deepTerm_cancel kappa Wt B Y d r hr2

/-- **Firewall.**  `KERNEL-PROVED`.  Deep-even cancellation is *not* a complete signed-floor
closure: the even collar `d ≤ Y(dr) < 2d` genuinely survives.  Witness: a single even `r`
whose split datum sits in the collar contributes a nonzero difference. -/
theorem deepEven_is_not_complete_closure :
    ∃ (kappa : ℕ → ℕ → ℝ) (Wt B : ℕ → ℝ) (Y : ℕ → ℕ) (d r : ℕ),
      Odd d ∧ Even r ∧ d ≤ Y (d * r) ∧ Y (d * r) < 2 * d ∧
        srcTerm kappa Wt B d r * ind (d ≤ Y (d * r))
          - srcTerm kappa Wt B d r * ind (2 * d ≤ Y (d * r)) ≠ 0 := by
  refine ⟨fun _ _ => 1, fun _ => 1, fun _ => 1, fun _ => 1, 1, 2, ⟨0, by norm_num⟩,
    ⟨1, by norm_num⟩, by norm_num, by norm_num, ?_⟩
  norm_num [srcTerm, ind]

end September4T0T2
end Erdos287
