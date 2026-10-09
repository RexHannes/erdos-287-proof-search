import Mathlib

/-!
# Erdős #287 — Maynard-style cross-coprime colouring partition (kernel-proved)

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

For a finite prime set `P` containing all prime factors of `a, b`, a *colouring* is a subset
`T ⊆ P` (the "red" primes).  The colour class of `T` consists of the pairs `(a, b)` with all
primes of `a` red and all primes of `b` not red.

* `colourClass_coprime` — inside every colour class the cross-coprimality `(a, b) = 1` holds.
* `colourings_card` — a coprime pair lies in exactly `2^{|P| - ω(a) - ω(b)}` classes.
* `coprime_indicator_identity` — the exact separation of the coprimality indicator:
  `1_{(a,b)=1} = 2^{ω(a)+ω(b)} / 2^{|P|} · #{T ⊆ P : (a,b) ∈ class(T)}`.
* `colour_weight_le` — the weight `2^{ω(a)+ω(b)}` is at most `4^K` when `ω(a), ω(b) ≤ K`
  (the bounded-number-of-prime-factors subpower cost).

This is the finite combinatorial core of the cross-coprime partition; it replaces the global
coprimality condition by a sum over `2^{|P|}` product classes in which the condition holds
automatically.
-/

open Finset

namespace Erdos287.SourceChain

/-- The colour-class predicate. -/
abbrev ColourClass (T : Finset ℕ) (a b : ℕ) : Prop :=
  a.primeFactors ⊆ T ∧ Disjoint b.primeFactors T

/-- Inside a colour class the cross-coprimality holds. -/
theorem colourClass_coprime {T : Finset ℕ} {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ColourClass T a b) : Nat.Coprime a b := by
  refine Nat.coprime_of_dvd (fun p hp hpa hpb => ?_)
  have h1 : p ∈ T := h.1 (Nat.mem_primeFactors.2 ⟨hp, hpa, ha⟩)
  exact Finset.disjoint_left.1 h.2 (Nat.mem_primeFactors.2 ⟨hp, hpb, hb⟩) h1

/-- The colourings containing a coprime pair are exactly `a.primeFactors ∪ U` with
`U ⊆ P \ (a.primeFactors ∪ b.primeFactors)`. -/
theorem colourings_eq {P : Finset ℕ} {a b : ℕ} (hab : Nat.Coprime a b)
    (hPa : a.primeFactors ⊆ P) :
    P.powerset.filter (fun T => ColourClass T a b) =
      (P \ (a.primeFactors ∪ b.primeFactors)).powerset.image (fun U => U ∪ a.primeFactors) := by
  have hdis : Disjoint a.primeFactors b.primeFactors := hab.disjoint_primeFactors
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image, ColourClass]
  constructor
  · rintro ⟨hTP, haT, hbT⟩
    refine ⟨T \ a.primeFactors, ?_, ?_⟩
    · intro p hp
      rw [Finset.mem_sdiff] at hp ⊢
      refine ⟨hTP hp.1, ?_⟩
      rw [Finset.mem_union, not_or]
      exact ⟨hp.2, fun hpb => Finset.disjoint_left.1 hbT hpb hp.1⟩
    · exact Finset.sdiff_union_of_subset haT
  · rintro ⟨U, hU, rfl⟩
    refine ⟨Finset.union_subset (hU.trans Finset.sdiff_subset) hPa,
      Finset.subset_union_right, ?_⟩
    rw [Finset.disjoint_union_right]
    refine ⟨Finset.disjoint_left.2 (fun p hpb hpU => ?_), hdis.symm⟩
    have := Finset.mem_sdiff.1 (hU hpU)
    exact this.2 (Finset.mem_union_right _ hpb)

/-- A coprime pair lies in exactly `2^{|P| - ω(a) - ω(b)}` colour classes. -/
theorem colourings_card {P : Finset ℕ} {a b : ℕ} (hab : Nat.Coprime a b)
    (hPa : a.primeFactors ⊆ P) (hPb : b.primeFactors ⊆ P) :
    (P.powerset.filter (fun T => ColourClass T a b)).card =
      2 ^ (P.card - a.primeFactors.card - b.primeFactors.card) := by
  have hdis : Disjoint a.primeFactors b.primeFactors := hab.disjoint_primeFactors
  rw [colourings_eq hab hPa, Finset.card_image_of_injOn, Finset.card_powerset,
    Finset.card_sdiff_of_subset (Finset.union_subset hPa hPb), Finset.card_union_of_disjoint hdis]
  · congr 1; omega
  · intro U hU V hV hUV
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
      Finset.coe_subset] at hU hV
    have hUa : Disjoint U a.primeFactors := Finset.disjoint_left.2 (fun p hp hpa =>
      (Finset.mem_sdiff.1 (hU hp)).2 (Finset.mem_union_left _ hpa))
    have hVa : Disjoint V a.primeFactors := Finset.disjoint_left.2 (fun p hp hpa =>
      (Finset.mem_sdiff.1 (hV hp)).2 (Finset.mem_union_left _ hpa))
    have h := congrArg (· \ a.primeFactors) hUV
    simp only [Finset.union_sdiff_right, hUa.sdiff_eq_left, hVa.sdiff_eq_left] at h
    exact h

/-- **Exact cross-coprime separation identity.** -/
theorem coprime_indicator_identity {P : Finset ℕ} {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hPa : a.primeFactors ⊆ P) (hPb : b.primeFactors ⊆ P) :
    (if Nat.Coprime a b then (1 : ℚ) else 0) =
      (2 : ℚ) ^ (a.primeFactors.card + b.primeFactors.card) / 2 ^ P.card *
        (P.powerset.filter (fun T => ColourClass T a b)).card := by
  split_ifs with hab
  · rw [colourings_card hab hPa hPb]
    have hdis : Disjoint a.primeFactors b.primeFactors := hab.disjoint_primeFactors
    have hle : a.primeFactors.card + b.primeFactors.card ≤ P.card := by
      rw [← Finset.card_union_of_disjoint hdis]
      exact Finset.card_le_card (Finset.union_subset hPa hPb)
    push_cast
    rw [div_mul_eq_mul_div, ← pow_add,
      show a.primeFactors.card + b.primeFactors.card +
        (P.card - a.primeFactors.card - b.primeFactors.card) = P.card by omega]
    exact (div_self (pow_ne_zero _ two_ne_zero)).symm
  · have hempty : P.powerset.filter (fun T => ColourClass T a b) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro T _ hT
      exact hab (colourClass_coprime ha hb hT)
    rw [hempty, Finset.card_empty]; simp

/-- The colouring weight is a bounded (subpower) cost when `ω(a), ω(b) ≤ K`. -/
theorem colour_weight_le {a b K : ℕ} (ha : a.primeFactors.card ≤ K)
    (hb : b.primeFactors.card ≤ K) : 2 ^ (a.primeFactors.card + b.primeFactors.card) ≤ 4 ^ K := by
  calc 2 ^ (a.primeFactors.card + b.primeFactors.card) ≤ 2 ^ (K + K) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 4 ^ K := by rw [← two_mul, pow_mul]; norm_num

end Erdos287.SourceChain
