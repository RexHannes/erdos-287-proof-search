import Mathlib
import RequestProject.CurrentProgramme.Erdos287StrictCellCanonicalSingleton

/-!
# Semantic repair layer §6 — the repeated-prime physical sector

`REPEATED PRIME SECTOR : INCLUDED EXACTLY`.

The older product-weight bridge carried a field routing *repeated-prime* labelled vectors to
weight zero.  That routing is **not** the current physical source: repeated labelled primes
remain genuine physical source points, and the finite combinatorial `H`-value of a labelled
vector depends only on the number `r` of **distinct** prime values it carries.

This file is append-only and rewrites nothing.  It contains:

* `distinctPrimeCount` — the number of distinct prime values of a labelled seven-vector;
* `Hrepeat r = ∑_{j ≤ min 3 r} (−1)^j C(r,j)`, the finite depth-`3` alternating value;
* the exact closed form `Hrepeat r = −C(r−1, 3)` for `r ≥ 1`, with the `r = 0` convention
  recorded explicitly (`Hrepeat 0 = 1`);
* the table `r = 7,6,5,4 ↦ −20, −10, −4, −1` and `r ≤ 3 ↦ 0`;
* the firewall `repeatedPrimeZero_changes_total_mass`: zeroing repeated-prime vectors is a
  *different* source, not a normalisation — on the banked balanced certificate it destroys
  the entire mass.

**Firewall.**  `Hrepeat` is a finite combinatorial value.  It is *not* identified with the
literal Ford functional `H_{μ,σ*,g*}(P)`; that identification requires the physical
Ford-`H` binding of `Erdos287StrictCellSemanticRepair.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace RepeatedPrime

open Finset
open Erdos287.SP2Source
open Erdos287.StrictCellSingleton

/-! ## §1.  The distinct-prime count of a labelled vector -/

/-- **`distinctPrimeCount`** — the number of *distinct* prime values carried by a labelled
seven-slot vector.  Repeated labels are counted once; the vector itself is not discarded. -/
def distinctPrimeCount (pvec : Fin 7 → ℕ) : ℕ := (Finset.univ.image pvec).card

theorem distinctPrimeCount_le_seven (pvec : Fin 7 → ℕ) : distinctPrimeCount pvec ≤ 7 := by
  classical
  have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin 7))) (f := pvec)
  simpa [distinctPrimeCount] using h

/-- The count is `7` exactly when the labelled primes are pairwise distinct. -/
theorem distinctPrimeCount_eq_seven_iff (pvec : Fin 7 → ℕ) :
    distinctPrimeCount pvec = 7 ↔ Function.Injective pvec := by
  classical
  constructor
  · intro h
    have hcard : (Finset.univ.image pvec).card = (Finset.univ : Finset (Fin 7)).card := by
      simpa [distinctPrimeCount] using h
    have hinj : Set.InjOn pvec ((Finset.univ : Finset (Fin 7)) : Set (Fin 7)) :=
      Finset.injOn_of_card_image_eq hcard
    intro a b hab
    exact hinj (by simp) (by simp) hab
  · intro h
    have : (Finset.univ.image pvec).card = (Finset.univ : Finset (Fin 7)).card :=
      Finset.card_image_of_injective _ h
    simpa [distinctPrimeCount] using this

/-- A vector with a repeated label has distinct-prime count `< 7`. -/
theorem distinctPrimeCount_lt_seven_of_repeat {pvec : Fin 7 → ℕ} {i j : Fin 7}
    (hij : i ≠ j) (heq : pvec i = pvec j) : distinctPrimeCount pvec < 7 := by
  classical
  rcases lt_or_eq_of_le (distinctPrimeCount_le_seven pvec) with h | h
  · exact h
  · exact absurd (((distinctPrimeCount_eq_seven_iff pvec).mp h) heq) hij

/-! ## §2.  The finite alternating depth-3 value `Hrepeat` -/

/-- **`Hrepeat`** — the finite combinatorial value attached to a labelled vector carrying
`r` distinct primes:  `Hrepeat r = ∑_{j = 0}^{min(3,r)} (−1)^j C(r, j)`. -/
def Hrepeat (r : ℕ) : ℤ := ∑ j ∈ Finset.range (min 3 r + 1), (-1 : ℤ) ^ j * (r.choose j : ℤ)

/-- The truncation at `min(3,r)` is cosmetic: the binomials above `r` vanish. -/
theorem Hrepeat_eq_range_four (r : ℕ) :
    Hrepeat r = ∑ j ∈ Finset.range 4, (-1 : ℤ) ^ j * (r.choose j : ℤ) := by
  rcases Nat.lt_or_ge r 3 with h | h
  · rw [Hrepeat, min_eq_right h.le]
    refine Finset.sum_subset ?_ ?_
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    · intro j _ hj
      simp only [Finset.mem_range, not_lt] at hj
      have : r.choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [this]
  · rw [Hrepeat, min_eq_left h]

/-- **`alternating_partial_choose_sum`.**  `LEAN_PROVED`.

The classical partial alternating binomial identity
`∑_{j ≤ k} (−1)^j C(r,j) = (−1)^k C(r−1,k)` for `r ≥ 1`. -/
theorem alternating_partial_choose_sum {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * (r.choose j : ℤ)
      = (-1 : ℤ) ^ k * ((r - 1).choose k : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have hpascal : r.choose (k + 1) = (r - 1).choose k + (r - 1).choose (k + 1) := by
        obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
        simpa using Nat.choose_succ_succ m k
      rw [hpascal]
      push_cast
      ring

/-- **`Hrepeat_eq_neg_choose`.**  `LEAN_PROVED`.

The exact closed form:  `Hrepeat r = −C(r−1, 3)` for every `r ≥ 1`. -/
theorem Hrepeat_eq_neg_choose {r : ℕ} (hr : 1 ≤ r) :
    Hrepeat r = -(((r - 1).choose 3 : ℕ) : ℤ) := by
  rw [Hrepeat_eq_range_four, show (4 : ℕ) = 3 + 1 from rfl,
    alternating_partial_choose_sum hr 3]
  norm_num

/-- The `r = 0` convention is recorded, not hidden: the empty vector value is `1`, which is
the one place where the closed form `−C(r−1,3)` does not apply. -/
theorem Hrepeat_zero : Hrepeat 0 = 1 := by decide

theorem Hrepeat_seven : Hrepeat 7 = -20 := by decide
theorem Hrepeat_six : Hrepeat 6 = -10 := by decide
theorem Hrepeat_five : Hrepeat 5 = -4 := by decide
theorem Hrepeat_four : Hrepeat 4 = -1 := by decide
theorem Hrepeat_three : Hrepeat 3 = 0 := by decide
theorem Hrepeat_two : Hrepeat 2 = 0 := by decide
theorem Hrepeat_one : Hrepeat 1 = 0 := by decide

/-- The whole physical table in one statement. -/
theorem Hrepeat_table :
    Hrepeat 7 = -20 ∧ Hrepeat 6 = -10 ∧ Hrepeat 5 = -4 ∧ Hrepeat 4 = -1 ∧
      (∀ r : ℕ, 1 ≤ r → r ≤ 3 → Hrepeat r = 0) := by
  refine ⟨Hrepeat_seven, Hrepeat_six, Hrepeat_five, Hrepeat_four, ?_⟩
  intro r h1 h3
  interval_cases r
  · exact Hrepeat_one
  · exact Hrepeat_two
  · exact Hrepeat_three

/-- The value attached to a labelled vector through its distinct-prime count. -/
def HrepeatOfVector (pvec : Fin 7 → ℕ) : ℤ := Hrepeat (distinctPrimeCount pvec)

/-- On a vector with pairwise distinct labels the value is the balanced `−20`. -/
theorem HrepeatOfVector_of_injective {pvec : Fin 7 → ℕ} (h : Function.Injective pvec) :
    HrepeatOfVector pvec = -20 := by
  rw [HrepeatOfVector, (distinctPrimeCount_eq_seven_iff pvec).mpr h]
  exact Hrepeat_seven

/-! ## §3.  Firewall: the old repeated-prime-zero routing is a *different* source -/

/-- The old routing: repeated-prime vectors are given weight zero. -/
def zeroRepeatedRouting (w : (Fin 7 → ℕ) → ℤ) : (Fin 7 → ℕ) → ℤ :=
  fun v => if Function.Injective v then w v else 0

/-- On the banked balanced certificate (two admissible primes per slot) *every* labelled
vector repeats a prime, by pigeonhole. -/
theorem countermodel_every_vector_repeats (v : Fin 7 → ℕ)
    (hv : v ∈ cellVectors countermodelCert) : ¬ Function.Injective v := by
  classical
  intro hinj
  have hmem : ∀ i : Fin 7, v i ∈ ({2, 3} : Finset ℕ) := by
    intro i
    have := (Fintype.mem_piFinset).mp (by simpa [cellVectors] using hv) i
    simpa [countermodelCert] using this
  have hcard : (Finset.univ.image v).card ≤ ({2, 3} : Finset ℕ).card := by
    refine Finset.card_le_card ?_
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hmem i
  rw [Finset.card_image_of_injective _ hinj] at hcard
  simp at hcard

/-- **`repeatedPrimeZero_changes_total_mass`.**  `LEAN_PROVED`.

Zeroing repeated-prime vectors is **not** a harmless normalisation.  On the banked balanced
certificate the unit weight has total mass `128`, while the old zero-routing of the same
weight has total mass `0`.  Hence the two sources are propositionally different, and the old
routing may not be used in the current controlling bridge. -/
theorem repeatedPrimeZero_changes_total_mass :
    (∑ v ∈ cellVectors countermodelCert, unitWeight v) = 128 ∧
      (∑ v ∈ cellVectors countermodelCert, zeroRepeatedRouting unitWeight v) = 0 := by
  classical
  constructor
  · have hcard : (cellVectors countermodelCert).card = 128 := by
      rw [cellVectors_card countermodelCert]
      decide
    simp [unitWeight, hcard]
  · refine Finset.sum_eq_zero ?_
    intro v hv
    simp [zeroRepeatedRouting, countermodel_every_vector_repeats v hv]

/-- **`repeated_prime_sector_included_exactly`.**  `LEAN_PROVED`.

The current physical sector keeps repeated-prime vectors and assigns them their exact finite
value `Hrepeat r`, which is *nonzero* whenever `r ≥ 4`.  In particular the sector is not
empty and not zero. -/
theorem repeated_prime_sector_included_exactly :
    ∃ pvec : Fin 7 → ℕ, ¬ Function.Injective pvec ∧ HrepeatOfVector pvec ≠ 0 := by
  classical
  refine ⟨![3, 3, 5, 7, 11, 13, 17], ?_, ?_⟩
  · intro h
    have : (0 : Fin 7) = 1 := h (by decide)
    exact absurd this (by decide)
  · have hcount : distinctPrimeCount ![3, 3, 5, 7, 11, 13, 17] = 6 := by decide
    rw [HrepeatOfVector, hcount, Hrepeat_six]
    decide

end RepeatedPrime
end Erdos287
