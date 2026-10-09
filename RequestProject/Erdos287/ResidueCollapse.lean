import Mathlib
import RequestProject.Erdos287.BsrcWeights

/-!
# Erdős #287 effectivity — complete residue-class collapse (§54)

```
JOINT e-RESIDUE / HYPERBOLA REASSEMBLY : KERNEL-PROVED
COLLAPSE TO s ≡ z (mod e)              : KERNEL-PROVED  (principal theorem)
TOP DIAGONAL s = z ABSENT               : KERNEL-PROVED
0-BASED INDEX FIREWALL                  : KERNEL-PROVED (the diagonal *does* appear)
```

The objects are the ones used by the current source, reconstructed exactly:

    N_e(I)(r)      = #{n ∈ I : n ≡ r (mod e)}                (hyperbola indices by e-class)
    S_{d,E}(a)     = ∑_{t ∣ a, d ∣ t, t ≤ E} β(t)             (truncated divisor coefficient)
    D_{d,E}(I)     = ∑_{n ∈ I} S_{d,E}(n)
    C_{M,I}(s)(r)  = ∑_{n ∈ I, n ≡ r (e)} 1_{s + e n ≡ z (e)} w(n)

`residue_class_collapse` is the exact identity: summing `C` over **all** `e`-residue classes
`r` leaves the single condition `s ≡ z (mod e)` — every other class contributes `0`, and on
the surviving class the total is the full weight `∑_{n ∈ I} w(n)`.

`top_diagonal_absent` is the second principal theorem: with the physical (1-based) index
convention the top diagonal `s = z` is **not** an atom of the reassembled sum.
`top_diagonal_zero_based_firewall` shows this is genuinely a consequence of the index
convention: with a `0`-based index set the diagonal reappears.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §54.1  The joint objects -/

/-- `N_e(I)(r)`: the number of hyperbola indices in `I` lying in the `e`-residue class `r`. -/
def NeCount (e : ℕ) (I : Finset ℕ) (r : ℕ) : ℕ := (I.filter fun n => n % e = r).card

/-- `S_{d,E}(a) = ∑_{t ∣ a, d ∣ t, t ≤ E} β(t)`, the truncated divisor coefficient. -/
def SdE (d E a : ℕ) : ℚ := ∑ t ∈ (Nat.divisors a).filter (fun t => d ∣ t ∧ t ≤ E), beta t

/-- `D_{d,E}(I) = ∑_{n ∈ I} S_{d,E}(n)`. -/
def DdE (d E : ℕ) (I : Finset ℕ) : ℚ := ∑ n ∈ I, SdE d E n

/-- `C_{M,I}(s)(r)`: the contribution of the `e`-residue class `r` of hyperbola indices to
the reassembled `s`-atom, with an arbitrary index weight `w`. -/
def CMI (I : Finset ℕ) (w : ℕ → ℚ) (e z s r : ℕ) : ℚ :=
  ∑ n ∈ I.filter (fun n => n % e = r),
    (if (s + e * n) % e = z % e then (1 : ℚ) else 0) * w n

/-! ## §54.2  The collapse identity -/

lemma shift_mod_eq (e s n : ℕ) : (s + e * n) % e = s % e := by
  simp [Nat.add_mul_mod_self_left]

/-- **`residue_class_collapse`.**  `KERNEL-PROVED`.  **Principal theorem.**  Summing the
joint `e`-residue / hyperbola-index contributions over all residue classes collapses every
class to the single congruence `s ≡ z (mod e)`. -/
theorem residue_class_collapse {e : ℕ} (he : 0 < e) (I : Finset ℕ) (w : ℕ → ℚ) (z s : ℕ) :
    ∑ r ∈ Finset.range e, CMI I w e z s r
      = (if s % e = z % e then (1 : ℚ) else 0) * ∑ n ∈ I, w n := by
  have hmaps : ∀ n ∈ I, n % e ∈ Finset.range e := by
    intro n _
    exact Finset.mem_range.2 (Nat.mod_lt _ he)
  have hpart :
      ∑ r ∈ Finset.range e, ∑ n ∈ I.filter (fun n => n % e = r),
          (if (s + e * n) % e = z % e then (1 : ℚ) else 0) * w n
        = ∑ n ∈ I, (if (s + e * n) % e = z % e then (1 : ℚ) else 0) * w n :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  rw [show (∑ r ∈ Finset.range e, CMI I w e z s r) =
      ∑ r ∈ Finset.range e, ∑ n ∈ I.filter (fun n => n % e = r),
        (if (s + e * n) % e = z % e then (1 : ℚ) else 0) * w n from rfl, hpart,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [shift_mod_eq]

/-- **`collapse_to_truncated_divisor_owner`.**  `KERNEL-PROVED`.  The collapse specialised
to the truncated-divisor owner weight: on the surviving class the reassembled sum is exactly
`D_{d,E}(I)`. -/
theorem collapse_to_truncated_divisor_owner {e : ℕ} (he : 0 < e) (I : Finset ℕ) (d E z s : ℕ)
    (hsz : s % e = z % e) :
    ∑ r ∈ Finset.range e, CMI I (SdE d E) e z s r = DdE d E I := by
  rw [residue_class_collapse he I (SdE d E) z s, if_pos hsz, one_mul, DdE]

/-- **`offdiagonal_classes_vanish`.**  `KERNEL-PROVED`.  Every `e`-residue class outside
`s ≡ z (mod e)` contributes exactly `0`. -/
theorem offdiagonal_classes_vanish (I : Finset ℕ) (w : ℕ → ℚ) (e z s r : ℕ)
    (hsz : s % e ≠ z % e) : CMI I w e z s r = 0 := by
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [shift_mod_eq, if_neg hsz, zero_mul]

/-! ## §54.3  The top diagonal -/

/-- The `s`-atom attached to the hyperbola index `n`: `s = z − e·n`. -/
def sAtom (e z n : ℕ) : ℕ := z - e * n

/-- The atom set of a physical index set. -/
def atomSet (e z : ℕ) (I : Finset ℕ) : Finset ℕ := I.image (sAtom e z)

/-- **`top_diagonal_absent`.**  `KERNEL-PROVED`.  **Principal theorem.**  With the physical
`1`-based hyperbola index convention (`0 ∉ I`) and `e ≥ 1`, `z ≥ 1`, the top diagonal `s = z`
is not an atom. -/
theorem top_diagonal_absent {e z : ℕ} {I : Finset ℕ} (he : 1 ≤ e) (hz : 1 ≤ z)
    (hI : ∀ n ∈ I, 1 ≤ n) : z ∉ atomSet e z I := by
  intro hmem
  rw [atomSet, Finset.mem_image] at hmem
  obtain ⟨n, hn, hval⟩ := hmem
  have hn1 : 1 ≤ n := hI n hn
  have : 1 ≤ e * n := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  rw [sAtom] at hval
  omega

/-- **`top_diagonal_zero_based_firewall`.**  `KERNEL-PROVED`.  The absence of the top
diagonal is a statement about the index convention, not a triviality: with the `0`-based
index set `{0}` the diagonal `s = z` **is** an atom. -/
theorem top_diagonal_zero_based_firewall (e z : ℕ) : z ∈ atomSet e z {0} := by
  rw [atomSet, Finset.mem_image]
  exact ⟨0, Finset.mem_singleton_self 0, by simp [sAtom]⟩

/-- **`NeCount_partitions`.**  `KERNEL-PROVED`.  The `e`-residue counts partition the index
set: `∑_{r < e} N_e(I)(r) = |I|`. -/
theorem NeCount_partitions {e : ℕ} (he : 0 < e) (I : Finset ℕ) :
    ∑ r ∈ Finset.range e, NeCount e I r = I.card := by
  classical
  have hmaps : Set.MapsTo (fun n => n % e) (I : Set ℕ) (Finset.range e : Set ℕ) := by
    intro n _
    simpa using Nat.mod_lt n he
  exact (Finset.card_eq_sum_card_fiberwise hmaps).symm

end Effectivity
end Erdos287
