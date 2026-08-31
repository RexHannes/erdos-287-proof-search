import Mathlib
import RequestProject.CurrentProgramme.Erdos287ReducedProjectivePair

/-!
# `b'`/`ℓ₀'` product-fibre energy — Erdős #287 (append-only)

This module is **append-only** and sits strictly after `Erdos287ReducedProjectivePair`.

The content is a *finite, generic* Cauchy–Schwarz statement: if a coefficient `ω` is supported
on a finite set `S` of pairs `(b', ℓ₀')` and one forms the product-fibre convolution

```
C(n) = ∑_{(b', ℓ₀') ∈ S, b' ℓ₀' = n} ω(b', ℓ₀'),
```

then the `ℓ²` energy of `C` is at most `D` times the one-row energy of `ω`, where `D` bounds the
**cardinality of each fibre** — not a pointwise divisor maximum, and not an average.  Two ways
of supplying `D` are given: directly, and from a finite set `L` of admissible `ℓ₀'` values
(fibres over `n ≠ 0` inject into `L`, since `ℓ₀'` then determines `b'`).

* §1  Fibres and the generic `L²` bound.
* §2  Fibre-cardinality bound from a finite second-coordinate set.
* §3  The instantiated bound, with `D = #L` and, in the intended application, `D = d₁'`.
* §4  Optional congruence filter (`u' ℓ₀' ≡ b' [MOD d₁']`): restricting the fibre only shrinks
  it, so the same bound holds.  No Möbius cancellation is used and `ω` is an arbitrary complex
  coefficient.
* §5  Analytic **interface** rows.  The implication “`d₁' ≤ L^K` ⟹ logarithmic loss” is stated
  as a conditional lemma with `d₁' ≤ L^K` as an explicit hypothesis.  The bound `d₁' ≤ L^K` is
  **not** asserted here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace BPrimeEnergy

open Finset

/-! ## §1  Product fibres and the generic `L²` bound -/

/-- The product fibre of `n` inside a finite set `S` of pairs `(b', ℓ₀')`. -/
def productFibre (S : Finset (ℕ × ℕ)) (n : ℕ) : Finset (ℕ × ℕ) :=
  S.filter (fun p => p.1 * p.2 = n)

/-- The product-fibre convolution `C(n) = ∑_{b' ℓ₀' = n} ω(b', ℓ₀')`. -/
noncomputable def fibreConv (S : Finset (ℕ × ℕ)) (omega : ℕ × ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ productFibre S n, omega p

/-- **`product_fibre_l2_bound_of_fibre_card`.**  `LEAN_PROVED`.  Generic finite Cauchy–Schwarz:
if every fibre over `N` has at most `D` elements, then

`∑_{n ∈ N} |C(n)|² ≤ D · ∑_{p ∈ S} |ω(p)|²`.

The hypothesis is a bound on the **fibre cardinality**; no divisor function, no multiplicity
maximum and no arithmetic structure of `S` is used. -/
theorem product_fibre_l2_bound_of_fibre_card
    (S : Finset (ℕ × ℕ)) (N : Finset ℕ) (omega : ℕ × ℕ → ℂ) (D : ℕ)
    (hfib : ∀ n ∈ N, (productFibre S n).card ≤ D) :
    ∑ n ∈ N, ‖fibreConv S omega n‖ ^ 2 ≤ (D : ℝ) * ∑ p ∈ S, ‖omega p‖ ^ 2 := by
  have key : ∀ n ∈ N, ‖fibreConv S omega n‖ ^ 2
      ≤ (D : ℝ) * ∑ p ∈ productFibre S n, ‖omega p‖ ^ 2 := by
    intro n hn
    have h1 : ‖fibreConv S omega n‖ ≤ ∑ p ∈ productFibre S n, ‖omega p‖ := norm_sum_le _ _
    have h2 : ‖fibreConv S omega n‖ ^ 2 ≤ (∑ p ∈ productFibre S n, ‖omega p‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (∑ p ∈ productFibre S n, ‖omega p‖) ^ 2
        ≤ ((productFibre S n).card : ℝ) * ∑ p ∈ productFibre S n, ‖omega p‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h4 : ((productFibre S n).card : ℝ) ≤ (D : ℝ) := by exact_mod_cast hfib n hn
    have h5 : (0 : ℝ) ≤ ∑ p ∈ productFibre S n, ‖omega p‖ ^ 2 :=
      Finset.sum_nonneg (fun p _ => by positivity)
    exact h2.trans (h3.trans (mul_le_mul_of_nonneg_right h4 h5))
  calc ∑ n ∈ N, ‖fibreConv S omega n‖ ^ 2
      ≤ ∑ n ∈ N, (D : ℝ) * ∑ p ∈ productFibre S n, ‖omega p‖ ^ 2 := Finset.sum_le_sum key
    _ = (D : ℝ) * ∑ n ∈ N, ∑ p ∈ productFibre S n, ‖omega p‖ ^ 2 := by rw [Finset.mul_sum]
    _ = (D : ℝ) * ∑ p ∈ S.filter (fun p => p.1 * p.2 ∈ N), ‖omega p‖ ^ 2 := by
        rw [show (∑ n ∈ N, ∑ p ∈ productFibre S n, ‖omega p‖ ^ 2)
              = ∑ n ∈ N, ∑ p ∈ S.filter (fun p => p.1 * p.2 = n), ‖omega p‖ ^ 2 from rfl,
          Finset.sum_fiberwise_eq_sum_filter]
    _ ≤ (D : ℝ) * ∑ p ∈ S, ‖omega p‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun p _ _ => by positivity)

/-! ## §2  Fibre cardinality from a finite second-coordinate set -/

/-- **`productFibre_card_le_of_second_mem`.**  `LEAN_PROVED`.  If every pair of `S` has its
second coordinate `ℓ₀'` in a finite set `L`, then for `n ≠ 0` the fibre over `n` has at most
`#L` elements: on such a fibre `ℓ₀' ≠ 0` and `b'` is determined by `ℓ₀'`. -/
theorem productFibre_card_le_of_second_mem
    (S : Finset (ℕ × ℕ)) (L : Finset ℕ) (hS : ∀ p ∈ S, p.2 ∈ L) {n : ℕ} (hn : n ≠ 0) :
    (productFibre S n).card ≤ L.card := by
  refine Finset.card_le_card_of_injOn (fun p => p.2) ?_ ?_
  · intro p hp
    exact hS p (Finset.mem_of_mem_filter p hp)
  · intro p hp q hq hpq
    simp only [productFibre, Finset.mem_coe, Finset.mem_filter] at hp hq
    have hp2 : p.2 ≠ 0 := fun h => hn (by simpa [h] using hp.2.symm)
    have hpq' : p.2 = q.2 := hpq
    have hmul : p.1 * p.2 = q.1 * p.2 := by rw [hp.2, hpq', hq.2]
    have h1 : p.1 = q.1 := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hp2) hmul
    exact Prod.ext h1 hpq'

/-! ## §3  The instantiated product-fibre energy bound -/

/-- **`product_fibre_l2_bound_of_second_cardinality`.**  `LEAN_PROVED`.  If the second
coordinates of `S` lie in a finite set `L` with `#L ≤ D`, and `N` avoids `0`, then

`∑_{n ∈ N} |C(n)|² ≤ D · ∑_{p ∈ S} |ω(p)|²`.

`D` bounds the number of admissible `ℓ₀'`, hence the fibre cardinality. -/
theorem product_fibre_l2_bound_of_second_cardinality
    (S : Finset (ℕ × ℕ)) (N : Finset ℕ) (L : Finset ℕ) (omega : ℕ × ℕ → ℂ) (D : ℕ)
    (hS : ∀ p ∈ S, p.2 ∈ L) (hL : L.card ≤ D) (hN : ∀ n ∈ N, n ≠ 0) :
    ∑ n ∈ N, ‖fibreConv S omega n‖ ^ 2 ≤ (D : ℝ) * ∑ p ∈ S, ‖omega p‖ ^ 2 :=
  product_fibre_l2_bound_of_fibre_card S N omega D
    (fun n hn => (productFibre_card_le_of_second_mem S L hS (hN n hn)).trans hL)

/-- **`bprime_h0_global_energy`.**  `LEAN_PROVED`.  The instantiation `D = d₁'` used by
`BPRIME-H0-GLOBALENERGY45`: the admissible `ℓ₀'` are the elements of a set `L` with
`#L ≤ d₁'`. -/
theorem bprime_h0_global_energy
    (S : Finset (ℕ × ℕ)) (N : Finset ℕ) (L : Finset ℕ) (omega : ℕ × ℕ → ℂ) (d1' : ℕ)
    (hS : ∀ p ∈ S, p.2 ∈ L) (hL : L.card ≤ d1') (hN : ∀ n ∈ N, n ≠ 0) :
    ∑ n ∈ N, ‖fibreConv S omega n‖ ^ 2 ≤ (d1' : ℝ) * ∑ p ∈ S, ‖omega p‖ ^ 2 :=
  product_fibre_l2_bound_of_second_cardinality S N L omega d1' hS hL hN

/-! ## §4  Optional congruence filter

Restricting the fibre to the pairs satisfying `u' ℓ₀' ≡ b' [MOD d₁']` only shrinks it, so the
same bound holds.  The coefficient `ω` remains an arbitrary complex function; no Möbius
cancellation is used. -/

/-- **`product_fibre_l2_bound_of_filtered`.**  `LEAN_PROVED`.  The energy bound for the fibre
restricted by an arbitrary decidable predicate `P` on pairs. -/
theorem product_fibre_l2_bound_of_filtered
    (S : Finset (ℕ × ℕ)) (N : Finset ℕ) (L : Finset ℕ) (omega : ℕ × ℕ → ℂ) (D : ℕ)
    (P : ℕ × ℕ → Prop) [DecidablePred P]
    (hS : ∀ p ∈ S, p.2 ∈ L) (hL : L.card ≤ D) (hN : ∀ n ∈ N, n ≠ 0) :
    ∑ n ∈ N, ‖fibreConv (S.filter P) omega n‖ ^ 2
      ≤ (D : ℝ) * ∑ p ∈ S, ‖omega p‖ ^ 2 := by
  have hsub : ∀ p ∈ S.filter P, p.2 ∈ L := fun p hp => hS p (Finset.mem_of_mem_filter p hp)
  refine (product_fibre_l2_bound_of_second_cardinality (S.filter P) N L omega D hsub hL hN).trans
    ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun p _ _ => by positivity)

/-- **`bprime_h0_global_energy_congruence_filter`.**  `LEAN_PROVED`.  The concrete congruence
filter `u' ℓ₀' ≡ b' [MOD d₁']`, with the same `d₁'` energy bound. -/
theorem bprime_h0_global_energy_congruence_filter
    (S : Finset (ℕ × ℕ)) (N : Finset ℕ) (L : Finset ℕ) (omega : ℕ × ℕ → ℂ) (d1' u' : ℕ)
    (hS : ∀ p ∈ S, p.2 ∈ L) (hL : L.card ≤ d1') (hN : ∀ n ∈ N, n ≠ 0) :
    ∑ n ∈ N,
        ‖fibreConv (S.filter (fun p => u' * p.2 ≡ p.1 [MOD d1'])) omega n‖ ^ 2
      ≤ (d1' : ℝ) * ∑ p ∈ S, ‖omega p‖ ^ 2 :=
  product_fibre_l2_bound_of_filtered S N L omega d1' _ hS hL hN

/-! ## §5  Analytic interface rows

The two lemmas below are *transfer* statements.  Neither asserts `d₁' ≤ L^K`; both take it as
an explicit hypothesis. -/

/-- **`energy_transfer_of_depth_bound`.**  `LEAN_PROVED`.  If the fibre parameter satisfies
`d₁' ≤ Lparam ^ K` then the `d₁'`-energy bound upgrades to an `Lparam^K` bound, i.e. to a
logarithmic loss whenever `Lparam` is a logarithm.  The hypothesis `d₁' ≤ Lparam ^ K` is
supplied by the caller; it is not proved here. -/
theorem energy_transfer_of_depth_bound
    {energy oneRowEnergy : ℝ} {d1' Lparam K : ℕ}
    (hE : energy ≤ (d1' : ℝ) * oneRowEnergy) (hOne : 0 ≤ oneRowEnergy)
    (hd : d1' ≤ Lparam ^ K) :
    energy ≤ ((Lparam : ℝ) ^ K) * oneRowEnergy := by
  refine hE.trans (mul_le_mul_of_nonneg_right ?_ hOne)
  exact_mod_cast hd

/-- **`bprime_h0_global_energy_with_depth_bound`.**  `LEAN_PROVED`.  Combination of the
unconditional finite energy lemma with the *hypothesised* depth bound `d₁' ≤ Lparam ^ K`. -/
theorem bprime_h0_global_energy_with_depth_bound
    (S : Finset (ℕ × ℕ)) (N : Finset ℕ) (L : Finset ℕ) (omega : ℕ × ℕ → ℂ)
    (d1' Lparam K : ℕ)
    (hS : ∀ p ∈ S, p.2 ∈ L) (hL : L.card ≤ d1') (hN : ∀ n ∈ N, n ≠ 0)
    (hd : d1' ≤ Lparam ^ K) :
    ∑ n ∈ N, ‖fibreConv S omega n‖ ^ 2
      ≤ ((Lparam : ℝ) ^ K) * ∑ p ∈ S, ‖omega p‖ ^ 2 :=
  energy_transfer_of_depth_bound
    (bprime_h0_global_energy S N L omega d1' hS hL hN)
    (Finset.sum_nonneg (fun p _ => by positivity)) hd

end BPrimeEnergy
end Erdos287
