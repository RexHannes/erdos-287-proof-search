import Mathlib
import RequestProject.CurrentProgramme.SevenBoxPrimeWeights

/-!
# CurrentProgramme (post-Balanced7 pass) §4 — exact fibre multiplicity for prime tuples

For weights supported on **primes** the labelled representation multiplicity of the `k`-fold
convolution is bounded by `k!`:

```
    representationMultiplicity 3 S N ≤ 3! = 6,
    representationMultiplicity 4 S N ≤ 4! = 24.
```

Repeated primes are *included*: the bound counts labelled tuples, and tuples with equal
entries are counted once each (they simply produce fewer than `k!` distinct labellings).

Combined with the finite collision bound of the main `3+4` algebra this gives the exact
finite Cauchy consequences

```
    ∑_n |a₃(n)|² ≤ 6  · ∏_{i<3} energy(ω_i),
    ∑_m |b₄(m)|² ≤ 24 · ∏_{i<4} energy(ω_i),
```

also in the complex-weight form used by the seven-box source.  The asymptotic research
targets remain external.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace PostBalanced7Pro

open Erdos287.CurrentProgramme

/-! ## §4.1  Two prime tuples with the same product are a permutation apart -/

/-- **`prime_tuple_perm`.**  `LEAN_PROVED`.

Unique factorisation in tuple form: two `k`-tuples of primes with the same product differ by
a permutation of the labels.  Repeated entries are allowed. -/
theorem prime_tuple_perm {k : ℕ} {t t' : Fin k → ℕ}
    (ht : ∀ i, (t i).Prime) (ht' : ∀ i, (t' i).Prime)
    (hprod : ∏ i, t i = ∏ i, t' i) :
    ∃ sigma : Equiv.Perm (Fin k), t' = t ∘ sigma := by
  classical
  set a : Fin k → ℕ := t ∘ (Tuple.sort t) with ha
  set b : Fin k → ℕ := t' ∘ (Tuple.sort t') with hb
  have hma : Monotone a := Tuple.monotone_sort t
  have hmb : Monotone b := Tuple.monotone_sort t'
  have hpa : (List.ofFn a).Pairwise (· ≤ ·) := by
    rw [List.pairwise_ofFn]; intro i j hij; exact hma hij.le
  have hpb : (List.ofFn b).Pairwise (· ≤ ·) := by
    rw [List.pairwise_ofFn]; intro i j hij; exact hmb hij.le
  have hproda : (List.ofFn a).prod = ∏ i, t i := by
    rw [List.prod_ofFn, ha]
    exact Fintype.prod_equiv (Tuple.sort t) _ _ (fun _ => rfl)
  have hprodb : (List.ofFn b).prod = ∏ i, t i := by
    rw [List.prod_ofFn, hb, hprod]
    exact Fintype.prod_equiv (Tuple.sort t') _ _ (fun _ => rfl)
  have hpra : ∀ p ∈ List.ofFn a, Nat.Prime p := by
    intro p hp; obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp; exact ht _
  have hprb : ∀ p ∈ List.ofFn b, Nat.Prime p := by
    intro p hp; obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp; exact ht' _
  have hperm : (List.ofFn a).Perm (List.ofFn b) :=
    (Nat.primeFactorsList_unique hproda hpra).trans
      (Nat.primeFactorsList_unique hprodb hprb).symm
  have hab : a = b :=
    List.ofFn_injective
      (List.Perm.eq_of_pairwise (fun _ _ _ _ hxy hyx => le_antisymm hxy hyx) hpa hpb hperm)
  refine ⟨(Tuple.sort t) * (Tuple.sort t')⁻¹, ?_⟩
  funext i
  have hval : t (Tuple.sort t ((Tuple.sort t')⁻¹ i)) = b ((Tuple.sort t')⁻¹ i) := by
    rw [← hab]; rfl
  simpa [hb, Function.comp] using hval.symm

/-! ## §4.2  The multiplicity bound `k!` -/

/-- **`card_prodFiber_le_factorial`.**  `LEAN_PROVED`.

For a prime support the labelled fibre of `n` has at most `k!` elements. -/
theorem card_prodFiber_le_factorial {k : ℕ} {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (n : ℕ) :
    (prodFiber k S n).card ≤ Nat.factorial k := by
  classical
  rcases Finset.eq_empty_or_nonempty (prodFiber k S n) with hempty | ⟨t0, ht0⟩
  · simp [hempty]
  obtain ⟨hmem0, hprod0⟩ := mem_prodFiber.1 ht0
  have hsub : prodFiber k S n ⊆
      (Finset.univ : Finset (Equiv.Perm (Fin k))).image
        (fun sigma : Equiv.Perm (Fin k) => (t0 ∘ (⇑sigma) : Fin k → ℕ)) := by
    intro t ht
    obtain ⟨hmem, hprod⟩ := mem_prodFiber.1 ht
    obtain ⟨sigma, hsigma⟩ :=
      prime_tuple_perm (fun i => hS _ (hmem0 i)) (fun i => hS _ (hmem i))
        (by rw [hprod0, hprod])
    exact Finset.mem_image.2 ⟨sigma, Finset.mem_univ _, hsigma.symm⟩
  calc (prodFiber k S n).card
      ≤ ((Finset.univ : Finset (Equiv.Perm (Fin k))).image
          (fun sigma : Equiv.Perm (Fin k) => (t0 ∘ (⇑sigma) : Fin k → ℕ))).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Equiv.Perm (Fin k))).card := Finset.card_image_le
    _ = Nat.factorial k := by
        rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

/-- **`representationMultiplicity_le_factorial`.**  `LEAN_PROVED`. -/
theorem representationMultiplicity_le_factorial {k : ℕ} {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) (N : Finset ℕ) :
    representationMultiplicity k S N ≤ Nat.factorial k := by
  refine Finset.sup_le ?_
  intro n _
  exact card_prodFiber_le_factorial hS n

/-- **`representationMultiplicity3_le_six`.**  `LEAN_PROVED`. -/
theorem representationMultiplicity3_le_six {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (N : Finset ℕ) : representationMultiplicity 3 S N ≤ 6 :=
  representationMultiplicity_le_factorial hS N

/-- **`representationMultiplicity4_le_twentyfour`.**  `LEAN_PROVED`. -/
theorem representationMultiplicity4_le_twentyfour {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (N : Finset ℕ) : representationMultiplicity 4 S N ≤ 24 :=
  representationMultiplicity_le_factorial hS N

/-! ## §4.3  Finite Cauchy consequences with the explicit constants -/

/-- **`a3_sq_sum_le_six`.**  `LEAN_PROVED`. -/
theorem a3_sq_sum_le_six {S N : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (w : Fin 3 → ℕ → ℝ)
    (hmaps : ∀ t ∈ Fintype.piFinset (fun _ : Fin 3 => S), (∏ i, t i) ∈ N) :
    ∑ n ∈ N, (a3 S w n) ^ 2 ≤ 6 * ∏ i, energy S (w i) := by
  refine le_trans (a3_sq_sum_le S N w hmaps) ?_
  have hmul : (representationMultiplicity 3 S N : ℝ) ≤ 6 := by
    exact_mod_cast representationMultiplicity3_le_six hS N
  have hnn : (0 : ℝ) ≤ ∏ i, energy S (w i) :=
    Finset.prod_nonneg fun i _ => energy_nonneg S (w i)
  exact mul_le_mul_of_nonneg_right hmul hnn

/-- **`b4_sq_sum_le_twentyfour`.**  `LEAN_PROVED`. -/
theorem b4_sq_sum_le_twentyfour {S N : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (w : Fin 4 → ℕ → ℝ)
    (hmaps : ∀ t ∈ Fintype.piFinset (fun _ : Fin 4 => S), (∏ i, t i) ∈ N) :
    ∑ m ∈ N, (b4 S w m) ^ 2 ≤ 24 * ∏ i, energy S (w i) := by
  refine le_trans (b4_sq_sum_le S N w hmaps) ?_
  have hmul : (representationMultiplicity 4 S N : ℝ) ≤ 24 := by
    exact_mod_cast representationMultiplicity4_le_twentyfour hS N
  have hnn : (0 : ℝ) ≤ ∏ i, energy S (w i) :=
    Finset.prod_nonneg fun i _ => energy_nonneg S (w i)
  exact mul_le_mul_of_nonneg_right hmul hnn

/-! ## §4.4  The complex-weight form -/

/-- The labelled `k`-fold convolution of **complex** box weights. -/
noncomputable def convWeightC {k : ℕ} (S : Finset ℕ) (w : Fin k → ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ t ∈ prodFiber k S n, ∏ i, w i (t i)

/-- **`norm_convWeightC_le`.**  `LEAN_PROVED`.

The modulus of a complex labelled convolution is dominated by the real convolution of the
moduli. -/
theorem norm_convWeightC_le {k : ℕ} (S : Finset ℕ) (w : Fin k → ℕ → ℂ) (n : ℕ) :
    ‖convWeightC S w n‖ ≤ convWeight S (fun i p => ‖w i p‖) n := by
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun t _ => ?_
  rw [norm_prod]

/-- **`convWeightC_sq_sum_le`.**  `LEAN_PROVED`.

The complex collision bound: the `ℓ²` mass of a complex labelled convolution obeys the same
multiplicity × energy bound, with the energies taken in the moduli. -/
theorem convWeightC_sq_sum_le {k : ℕ} (S N : Finset ℕ) (w : Fin k → ℕ → ℂ)
    (hmaps : ∀ t ∈ Fintype.piFinset (fun _ : Fin k => S), (∏ i, t i) ∈ N) :
    ∑ n ∈ N, ‖convWeightC S w n‖ ^ 2 ≤
      (representationMultiplicity k S N : ℝ) * ∏ i, energy S (fun p => ‖w i p‖) := by
  refine le_trans (Finset.sum_le_sum (fun n _ => ?_))
    (convWeight_sq_sum_le S N (fun i p => ‖w i p‖) hmaps)
  have h1 : ‖convWeightC S w n‖ ≤ convWeight S (fun i p => ‖w i p‖) n :=
    norm_convWeightC_le S w n
  have h2 : 0 ≤ ‖convWeightC S w n‖ := norm_nonneg _
  exact pow_le_pow_left₀ h2 h1 2

/-- **`seven_box_energy_bound`.**  `LEAN_PROVED`.

For the literal seven-box weights with a normalised profile, each box energy is at most the
size of the prime box. -/
theorem seven_box_energy_bound {V : ℝ → ℝ} {Y t : ℝ} (hV : ∀ x : ℝ, 0 ≤ V x ∧ V x ≤ 1)
    (S : Finset ℕ) : energy S (fun p => ‖omegaBox V Y t p‖) ≤ (S.card : ℝ) := by
  unfold energy
  calc ∑ p ∈ S, ‖omegaBox V Y t p‖ ^ 2 ≤ ∑ _p ∈ S, (1 : ℝ) := by
        refine Finset.sum_le_sum fun p _ => ?_
        have h1 : ‖omegaBox V Y t p‖ ≤ 1 := norm_omegaBox_le_one hV p
        nlinarith [norm_nonneg (omegaBox V Y t p)]
    _ = (S.card : ℝ) := by simp

end PostBalanced7Pro
end Erdos287
