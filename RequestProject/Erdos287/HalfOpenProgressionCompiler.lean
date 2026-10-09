import Mathlib
import RequestProject.Erdos287.SmallEllCRT

/-!
# Erdős #287 effectivity — exact half-open progression sums and the finite compiler (§57)

```
HALF-OPEN AP REPARAMETRIZATION T(A,B;r,m) : KERNEL-PROVED
EXACT AP COUNT                            : KERNEL-PROVED
PERIODIC WINDOW COMPILER                  : KERNEL-PROVED
FINITE COMPILER Q_ell(A,B;z)              : KERNEL-PROVED
```

The half-open convention is retained throughout: the window is `A ≤ s < B` and the
progression is `s ≡ r (mod m)`.  With

    k₀ = ⌈(A − r)/m⌉,   k₁ = ⌈(B − r)/m⌉,

the atoms of the progression are exactly `s = r + m k`, `k₀ ≤ k < k₁`
(`progression_reindex`), so **every** sum over the progression collapses to a sum over a
half-open integer `k`-window; in particular the count is `max 0 (k₁ − k₀)`.

`periodic_window_compiler` compiles a sum of any `m`-periodic function over a huge window
into `m` residue-class terms, and `Qell_compiler` is its instance for the small-`ℓ` local
formula: no iteration over the physical `s`-range appears in the statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §57.1  The half-open progression -/

/-- The atoms of the half-open progression `A ≤ s < B`, `s ≡ r (mod m)`. -/
def apSet (A B r : ℤ) (m : ℕ) : Finset ℤ :=
  (Finset.Ico A B).filter (fun s => (s - r) % (m : ℤ) = 0)

/-- Lower `k`-endpoint `k₀ = ⌈(A − r)/m⌉`. -/
def apLow (A r : ℤ) (m : ℕ) : ℤ := ⌈((A - r : ℤ) : ℚ) / (m : ℚ)⌉

/-- Upper `k`-endpoint `k₁ = ⌈(B − r)/m⌉`. -/
def apHigh (B r : ℤ) (m : ℕ) : ℤ := ⌈((B - r : ℤ) : ℚ) / (m : ℚ)⌉

lemma ap_injective {m : ℕ} (hm : 0 < m) (r : ℤ) :
    Function.Injective (fun k : ℤ => r + (m : ℤ) * k) := by
  intro x y hxy
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have h : (m : ℤ) * x = (m : ℤ) * y := by
    have hx : r + (m : ℤ) * x = r + (m : ℤ) * y := hxy
    linarith
  exact mul_left_cancel₀ hm' h

/-- **`progression_reindex`.**  `KERNEL-PROVED`.  Exact reparametrization of the half-open
progression by the half-open integer window `k₀ ≤ k < k₁`. -/
theorem progression_reindex {m : ℕ} (hm : 0 < m) (A B r : ℤ) :
    apSet A B r m = (Finset.Ico (apLow A r m) (apHigh B r m)).image (fun k => r + (m : ℤ) * k) := by
  have hmQ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  ext s
  simp only [apSet, Finset.mem_filter, Finset.mem_Ico, Finset.mem_image, apLow, apHigh]
  constructor
  · rintro ⟨⟨hA, hB⟩, hmod⟩
    obtain ⟨k, hk⟩ : (m : ℤ) ∣ (s - r) := Int.dvd_of_emod_eq_zero hmod
    refine ⟨k, ⟨?_, ?_⟩, by omega⟩
    · rw [Int.ceil_le, div_le_iff₀ hmQ]
      have h1 : (A - r : ℤ) ≤ (m : ℤ) * k := by rw [← hk]; omega
      have h2 : (A - r : ℤ) ≤ k * (m : ℤ) := by rw [mul_comm] at h1; exact h1
      exact_mod_cast h2
    · rw [Int.lt_ceil, lt_div_iff₀ hmQ]
      have h1 : (m : ℤ) * k < (B - r : ℤ) := by rw [← hk]; omega
      have h2 : k * (m : ℤ) < (B - r : ℤ) := by rw [mul_comm] at h1; exact h1
      exact_mod_cast h2
  · rintro ⟨k, ⟨hk0, hk1⟩, rfl⟩
    rw [Int.ceil_le, div_le_iff₀ hmQ] at hk0
    rw [Int.lt_ceil, lt_div_iff₀ hmQ] at hk1
    have h0 : (A - r : ℤ) ≤ k * (m : ℤ) := by exact_mod_cast hk0
    have h1 : k * (m : ℤ) < (B - r : ℤ) := by exact_mod_cast hk1
    rw [mul_comm] at h0 h1
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    simp

/-- **`progression_sum_reindex`.**  `KERNEL-PROVED`.  Every sum over the half-open
progression is exactly a sum over the half-open `k`-window. -/
theorem progression_sum_reindex {m : ℕ} (hm : 0 < m) (A B r : ℤ) (f : ℤ → ℚ) :
    ∑ s ∈ apSet A B r m, f s
      = ∑ k ∈ Finset.Ico (apLow A r m) (apHigh B r m), f (r + (m : ℤ) * k) := by
  rw [progression_reindex hm A B r]
  exact Finset.sum_image (fun x _ y _ hxy => ap_injective hm r hxy)

/-- **`apCount_exact`.**  `KERNEL-PROVED`.  The exact half-open progression count
`T(A,B;r,m) = max 0 (k₁ − k₀)`. -/
theorem apCount_exact {m : ℕ} (hm : 0 < m) (A B r : ℤ) :
    ((apSet A B r m).card : ℤ) = max 0 (apHigh B r m - apLow A r m) := by
  rw [progression_reindex hm A B r, Finset.card_image_of_injective _ (ap_injective hm r),
    Int.card_Ico]
  omega

/-! ## §57.2  The periodic window compiler -/

/-- The number of window points in the residue class `r`. -/
def residueCount (A B : ℤ) (m r : ℕ) : ℕ :=
  ((Finset.Ico A B).filter (fun s => (s % (m : ℤ)).toNat = r)).card

lemma periodic_of_shift {f : ℤ → ℚ} {m : ℕ} (hper : ∀ s, f (s + m) = f s) :
    ∀ s : ℤ, f s = f (s % (m : ℤ)) := by
  have hmul : ∀ (k : ℤ) (s : ℤ), f (s + (m : ℤ) * k) = f s := by
    intro k
    induction k using Int.induction_on with
    | zero => intro s; simp
    | succ n ih =>
        intro s
        have h1 : s + (m : ℤ) * ((n : ℤ) + 1) = (s + (m : ℤ) * (n : ℤ)) + m := by ring
        rw [h1, hper, ih]
    | pred n ih =>
        intro s
        have h1 : s + (m : ℤ) * (-(n : ℤ) - 1) = (s + (m : ℤ) * (-(n : ℤ))) - m := by ring
        rw [h1]
        have h2 := hper ((s + (m : ℤ) * (-(n : ℤ))) - m)
        simp only [sub_add_cancel] at h2
        rw [← h2, ih]
  intro s
  have hdef : s % (m : ℤ) = s - (m : ℤ) * (s / (m : ℤ)) := Int.emod_def s (m : ℤ)
  rw [hdef, show s - (m : ℤ) * (s / (m : ℤ)) = s + (m : ℤ) * (-(s / (m : ℤ))) by ring,
    hmul (-(s / (m : ℤ))) s]

/-- **`periodic_window_compiler`.**  `KERNEL-PROVED`.  A sum of an `m`-periodic function over
an arbitrary half-open window compiles into `m` residue-class terms.  No iteration over the
window appears. -/
theorem periodic_window_compiler {f : ℤ → ℚ} {m : ℕ} (hm : 0 < m)
    (hper : ∀ s, f (s + m) = f s) (A B : ℤ) :
    ∑ s ∈ Finset.Ico A B, f s
      = ∑ r ∈ Finset.range m, f (r : ℤ) * (residueCount A B m r : ℚ) := by
  classical
  have hmaps : ∀ s ∈ Finset.Ico A B, (s % (m : ℤ)).toNat ∈ Finset.range m := by
    intro s _
    have h1 : 0 ≤ s % (m : ℤ) := Int.emod_nonneg s (by exact_mod_cast hm.ne')
    have h2 : s % (m : ℤ) < (m : ℤ) := Int.emod_lt_of_pos s (by exact_mod_cast hm)
    simp only [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [residueCount, Finset.card_filter]
  push_cast
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : (s % (m : ℤ)).toNat = r
  · rw [if_pos h, if_pos h, mul_one]
    have h1 : 0 ≤ s % (m : ℤ) := Int.emod_nonneg s (by exact_mod_cast hm.ne')
    have hmod : s % (m : ℤ) = (r : ℤ) := by omega
    rw [periodic_of_shift hper s, hmod]
  · rw [if_neg h, if_neg h, mul_zero]

/-! ## §57.3  The finite compiler `Q_ℓ(A,B;z)` -/

/-- The finite compiler `Q_ℓ(A,B;z) = ∑_{r < ℓ} K_ℓ(r,z)·T(A,B;r,ℓ)`. -/
def Qell (ell : ℕ) (A B : ℤ) (z : ℤ) : ℚ :=
  ∑ r ∈ Finset.range ell, Kell ell (r : ℤ) z * (residueCount A B ell r : ℚ)

/-- **`Qell_compiler`.**  `KERNEL-PROVED`.  The physical window sum of the small-`ℓ` local
formula equals the finite compiler: at most `ℓ` residue-class evaluations, no iteration over
the `s`-range. -/
theorem Qell_compiler {ell : ℕ} (hell : 0 < ell) (A B z : ℤ) :
    ∑ s ∈ Finset.Ico A B, Kell ell s z = Qell ell A B z :=
  periodic_window_compiler hell (fun s => Kell_periodic ell s z) A B

end Effectivity
end Erdos287
