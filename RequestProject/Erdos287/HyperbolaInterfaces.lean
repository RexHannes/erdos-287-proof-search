import Mathlib

/-!
# Erdős #287 effectivity — hyperbola interfaces `T_n = z/(en+b)` (§51)

```
STRICT ORIENTATION (T ANTITONE)        : KERNEL-PROVED
EXACT ENDPOINT REPARAMETRIZATION       : KERNEL-PROVED
INTEGER-INTERVAL FORM OF THE INDEX SET : KERNEL-PROVED
CONVEXITY OF THE PHYSICAL INDEX SET    : KERNEL-PROVED
HALF-OPEN vs CLOSED CONVENTION         : KERNEL-PROVED FIREWALL (they differ)
```

The hyperbola interface coordinate is

    T_n = z / (e·n + b),        e > 0, b > 0, z > 0.

`T` is strictly antitone in `n`, so the *physical* half-open window `A ≤ T_n < B`
reverses orientation and becomes the half-open `n`-window

    (z/B − b)/e  <  n  ≤  (z/A − b)/e,

which is `hyperbola_window_reparam`.  `physIndex_eq_Icc` turns this into an explicit
integer interval, and `physIndex_convex` records that the index set is an interval.
`window_convention_firewall` exhibits a concrete instance in which the closed convention
`A ≤ T_n ≤ B` contains an index the half-open convention excludes; the two conventions are
therefore **not** interchangeable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §51.1  The interface coordinate -/

/-- The hyperbola interface coordinate `T_n = z/(e n + b)`. -/
def Tn (z e b : ℚ) (n : ℕ) : ℚ := z / (e * n + b)

lemma Tn_denom_pos {e b : ℚ} (he : 0 < e) (hb : 0 < b) (n : ℕ) : 0 < e * n + b := by
  have : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
  nlinarith

/-- **`Tn_strictAnti`.**  `KERNEL-PROVED`.  The interface coordinate is strictly decreasing
in the index: the physical orientation is reversed by the reparametrization. -/
theorem Tn_strictAnti {z e b : ℚ} (hz : 0 < z) (he : 0 < e) (hb : 0 < b) {m n : ℕ}
    (h : m < n) : Tn z e b n < Tn z e b m := by
  have hm := Tn_denom_pos he hb m
  have hn := Tn_denom_pos he hb n
  have hlt : e * m + b < e * n + b := by
    have : (m : ℚ) < (n : ℚ) := by exact_mod_cast h
    nlinarith
  rw [Tn, Tn, div_lt_div_iff₀ hn hm]
  nlinarith

/-! ## §51.2  Exact endpoint reparametrization -/

/-- **`Tn_lower_iff`.**  `KERNEL-PROVED`.  `A ≤ T_n ↔ n ≤ (z/A − b)/e`. -/
theorem Tn_lower_iff {z e b A : ℚ} (he : 0 < e) (hb : 0 < b) (hA : 0 < A) (n : ℕ) :
    A ≤ Tn z e b n ↔ (n : ℚ) ≤ (z / A - b) / e := by
  have hden := Tn_denom_pos he hb n
  rw [Tn, le_div_iff₀ hden, le_div_iff₀ he, le_sub_iff_add_le, le_div_iff₀ hA]
  constructor <;> intro h <;> nlinarith

/-- **`Tn_upper_iff`.**  `KERNEL-PROVED`.  `T_n < B ↔ (z/B − b)/e < n`. -/
theorem Tn_upper_iff {z e b B : ℚ} (he : 0 < e) (hb : 0 < b) (hB : 0 < B) (n : ℕ) :
    Tn z e b n < B ↔ (z / B - b) / e < (n : ℚ) := by
  have hden := Tn_denom_pos he hb n
  rw [Tn, div_lt_iff₀ hden, div_lt_iff₀ he, sub_lt_iff_lt_add, div_lt_iff₀ hB]
  constructor <;> intro h <;> nlinarith

/-- The physical index set of the half-open window `A ≤ T_n < B`, truncated at `K`. -/
def physIndex (z e b A B : ℚ) (K : ℕ) : Finset ℕ :=
  (Finset.Icc 1 K).filter (fun n => A ≤ Tn z e b n ∧ Tn z e b n < B)

/-- **`hyperbola_window_reparam`.**  `KERNEL-PROVED`.  The exact reparametrization of the
physical half-open window as a half-open `n`-window with reversed orientation. -/
theorem hyperbola_window_reparam {z e b A B : ℚ} (he : 0 < e) (hb : 0 < b) (hA : 0 < A)
    (hB : 0 < B) (K : ℕ) :
    physIndex z e b A B K
      = (Finset.Icc 1 K).filter
          (fun n : ℕ => (z / B - b) / e < (n : ℚ) ∧ (n : ℚ) ≤ (z / A - b) / e) := by
  refine Finset.filter_congr fun n _ => ?_
  rw [Tn_lower_iff he hb hA n, Tn_upper_iff he hb hB n]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- **`physIndex_eq_Icc`.**  `KERNEL-PROVED`.  Integer-interval form of the physical index
set, with the strict lower endpoint converted by `⌊·⌋₊ + 1` and the inclusive upper endpoint
by `⌊·⌋₊`. -/
theorem physIndex_eq_Icc {z e b A B : ℚ} (he : 0 < e) (hb : 0 < b) (hA : 0 < A) (hB : 0 < B)
    (K : ℕ) (hlow : 0 ≤ (z / B - b) / e) (hhigh : 0 ≤ (z / A - b) / e) :
    physIndex z e b A B K
      = Finset.Icc (max 1 (⌊(z / B - b) / e⌋₊ + 1)) (min K ⌊(z / A - b) / e⌋₊) := by
  rw [hyperbola_window_reparam he hb hA hB K]
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff, max_le_iff]
  rw [Nat.floor_lt hlow |>.symm.trans (by rfl : (⌊(z / B - b) / e⌋₊ < n) ↔ (⌊(z / B - b) / e⌋₊ < n)),
    Nat.le_floor_iff hhigh]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, by omega⟩, h2, h4⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, h3⟩, by omega, h4⟩

/-- **`physIndex_convex`.**  `KERNEL-PROVED`.  The physical index set is an interval: if
`n₁ ≤ n ≤ n₂` and both `n₁, n₂` are physical, then so is `n`. -/
theorem physIndex_convex {z e b A B : ℚ} (hz : 0 < z) (he : 0 < e) (hb : 0 < b)
    {K n₁ n n₂ : ℕ} (h1 : n₁ ∈ physIndex z e b A B K) (h2 : n₂ ∈ physIndex z e b A B K)
    (hle₁ : n₁ ≤ n) (hle₂ : n ≤ n₂) : n ∈ physIndex z e b A B K := by
  simp only [physIndex, Finset.mem_filter, Finset.mem_Icc] at h1 h2 ⊢
  refine ⟨⟨le_trans h1.1.1 hle₁, le_trans hle₂ h2.1.2⟩, ?_, ?_⟩
  · rcases eq_or_lt_of_le hle₂ with h | h
    · exact h ▸ h2.2.1
    · exact le_trans h2.2.1 (le_of_lt (Tn_strictAnti hz he hb h))
  · rcases eq_or_lt_of_le hle₁ with h | h
    · exact h ▸ h1.2.2
    · exact lt_of_le_of_lt (le_of_lt (Tn_strictAnti hz he hb h)) h1.2.2

/-! ## §51.3  Convention firewall -/

/-- The closed-window index set `A ≤ T_n ≤ B`. -/
def physIndexClosed (z e b A B : ℚ) (K : ℕ) : Finset ℕ :=
  (Finset.Icc 1 K).filter (fun n => A ≤ Tn z e b n ∧ Tn z e b n ≤ B)

/-- **`window_convention_firewall`.**  `KERNEL-PROVED`.  The half-open and closed
conventions genuinely differ: for `z = 1`, `e = b = 1`, `A = 1/3`, `B = 1/2`, `K = 2` the
index `n = 1` lies in the closed window and not in the half-open window. -/
theorem window_convention_firewall :
    (1 : ℕ) ∈ physIndexClosed 1 1 1 (1/3) (1/2) 2 ∧
      (1 : ℕ) ∉ physIndex 1 1 1 (1/3) (1/2) 2 ∧
      physIndex 1 1 1 (1/3) (1/2) 2 ≠ physIndexClosed 1 1 1 (1/3) (1/2) 2 := by
  have hT : Tn 1 1 1 1 = 1 / 2 := by norm_num [Tn]
  have h1 : (1 : ℕ) ∈ physIndexClosed 1 1 1 (1/3) (1/2) 2 := by
    norm_num [physIndexClosed, Finset.mem_filter, Finset.mem_Icc, hT]
  have h2 : (1 : ℕ) ∉ physIndex 1 1 1 (1/3) (1/2) 2 := by
    norm_num [physIndex, Finset.mem_filter, Finset.mem_Icc, hT]
  exact ⟨h1, h2, fun h => h2 (h ▸ h1)⟩

end Effectivity
end Erdos287
