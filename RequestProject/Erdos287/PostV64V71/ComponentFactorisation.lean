import RequestProject.Erdos287.PostQSigma.HardCore

/-!
# Erdős #287 — V67 free-component factorisation

**Status: BANK (LEAN PROVED).**

Forced selected sites `F` split the physical path `V = (a, M)` into free components.  For a
weight `b : ℕ → ℕ` (in the source, `b n = W/n`) and a finite set `C`:

* `compPoly b C = ∑_{E ⊆ C independent} z^{∑_{n∈E} b n}` (a polynomial with natural
  coefficients; this is the component polynomial `F_C(z)`);
* `compCount b C τ = #{E ⊆ C independent : ∑_{n∈E} b n = τ}` (`τ ∈ ℤ`).

Results:

* `compCount_eq_coeff` — `compCount b C τ = [z^τ] compPoly b C` for `τ ≥ 0`;
* `compCount_of_neg` — **immediate arithmetic death**: `τ < 0 ⇒ compCount = 0`;
* `compPoly_union` — for *separated* disjoint `C₁, C₂` (no element of one adjacent to an element
  of the other), `F_{C₁ ∪ C₂} = F_{C₁} · F_{C₂}`;
* `compPoly_biUnion` — the same for a pairwise separated family `(C_i)_{i ∈ s}`;
* `component_coefficient_factorization` — `N = [z^τ] ∏_i F_{C_i}` for the count of independent
  omission sets supported on `⋃ C_i` with mass `τ ≥ 0`;
* `forced_restricted_count_eq` — in the raw source, the number of `E ∈ Ω(a, M)` avoiding the
  forced selected set `F` with `X(E) = 0` equals `compCount (W/·) ((a,M) \ F) T`.

No universal coefficient vanishing is claimed.
-/

open scoped BigOperators
open Polynomial

namespace Erdos287.PostV64V71

open Erdos287.ExactSource Erdos287.PostQSigma

/-- The independent subsets of `C`. -/
noncomputable def indepSubsets (C : Finset ℕ) : Finset (Finset ℕ) := by
  classical exact C.powerset.filter Indep

theorem mem_indepSubsets {C E : Finset ℕ} : E ∈ indepSubsets C ↔ E ⊆ C ∧ Indep E := by
  classical
  unfold indepSubsets; simp

/-- The component polynomial `F_C(z) = ∑_{E ⊆ C indep} z^{b(E)}`. -/
noncomputable def compPoly (b : ℕ → ℕ) (C : Finset ℕ) : ℕ[X] :=
  ∑ E ∈ indepSubsets C, X ^ (∑ n ∈ E, b n)

/-- The exact count `#{E ⊆ C indep : b(E) = τ}`. -/
noncomputable def compCount (b : ℕ → ℕ) (C : Finset ℕ) (τ : ℤ) : ℕ := by
  classical exact ((indepSubsets C).filter (fun E => ((∑ n ∈ E, b n : ℕ) : ℤ) = τ)).card

/-- `compCount = [z^τ] F_C` for `τ ≥ 0`. -/
theorem compCount_eq_coeff (b : ℕ → ℕ) (C : Finset ℕ) {τ : ℤ} (hτ : 0 ≤ τ) :
    compCount b C τ = (compPoly b C).coeff τ.toNat := by
  classical
  unfold compCount compPoly
  rw [finset_sum_coeff]
  simp only [coeff_X_pow]
  rw [Finset.sum_boole]
  congr 1
  refine Finset.filter_congr fun E _ => ?_
  constructor
  · intro h; rw [← h, Int.toNat_natCast]
  · intro h; rw [← h, Int.toNat_of_nonneg hτ]

/-- **Immediate arithmetic death**: a negative target has no solution. -/
theorem compCount_of_neg (b : ℕ → ℕ) (C : Finset ℕ) {τ : ℤ} (hτ : τ < 0) :
    compCount b C τ = 0 := by
  classical
  unfold compCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro E _ h
  have : (0 : ℤ) ≤ ((∑ n ∈ E, b n : ℕ) : ℤ) := Int.natCast_nonneg _
  omega

/-- Two sets are *separated*: disjoint and no element of one is adjacent to an element of
the other. -/
def Separated (C₁ C₂ : Finset ℕ) : Prop :=
  Disjoint C₁ C₂ ∧ ∀ x ∈ C₁, ∀ y ∈ C₂, x + 1 ≠ y ∧ y + 1 ≠ x

theorem indep_union_iff {C₁ C₂ E₁ E₂ : Finset ℕ} (hsep : Separated C₁ C₂) (h1 : E₁ ⊆ C₁)
    (h2 : E₂ ⊆ C₂) : Indep (E₁ ∪ E₂) ↔ Indep E₁ ∧ Indep E₂ := by
  constructor
  · intro h
    exact ⟨fun x hx hx1 => h x (Finset.mem_union_left _ hx) (Finset.mem_union_left _ hx1),
      fun x hx hx1 => h x (Finset.mem_union_right _ hx) (Finset.mem_union_right _ hx1)⟩
  · rintro ⟨i1, i2⟩ x hx hx1
    rcases Finset.mem_union.1 hx with hx | hx <;> rcases Finset.mem_union.1 hx1 with hy | hy
    · exact i1 x hx hy
    · exact (hsep.2 x (h1 hx) (x + 1) (h2 hy)).1 rfl
    · exact (hsep.2 (x + 1) (h1 hy) x (h2 hx)).2 rfl
    · exact i2 x hx hy

/-- **Binary component factorisation**: `F_{C₁ ∪ C₂} = F_{C₁} · F_{C₂}` for separated sets. -/
theorem compPoly_union (b : ℕ → ℕ) {C₁ C₂ : Finset ℕ} (hsep : Separated C₁ C₂) :
    compPoly b (C₁ ∪ C₂) = compPoly b C₁ * compPoly b C₂ := by
  classical
  unfold compPoly
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun E => (E ∩ C₁, E ∩ C₂)) (fun p => p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
  · intro E hE
    rw [mem_indepSubsets] at hE
    simp only [Finset.mem_product, mem_indepSubsets]
    exact ⟨⟨Finset.inter_subset_right, fun x hx hx1 =>
        hE.2 x (Finset.mem_inter.1 hx).1 (Finset.mem_inter.1 hx1).1⟩,
      ⟨Finset.inter_subset_right, fun x hx hx1 =>
        hE.2 x (Finset.mem_inter.1 hx).1 (Finset.mem_inter.1 hx1).1⟩⟩
  · rintro ⟨E₁, E₂⟩ hp
    simp only [Finset.mem_product, mem_indepSubsets] at hp
    rw [mem_indepSubsets]
    exact ⟨Finset.union_subset_union hp.1.1 hp.2.1,
      (indep_union_iff hsep hp.1.1 hp.2.1).2 ⟨hp.1.2, hp.2.2⟩⟩
  · intro E hE
    rw [mem_indepSubsets] at hE
    simp only
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.2 hE.1]
  · rintro ⟨E₁, E₂⟩ hp
    simp only [Finset.mem_product, mem_indepSubsets] at hp
    have hd1 : E₂ ∩ C₁ = ∅ := Finset.disjoint_iff_inter_eq_empty.1
      (Finset.disjoint_of_subset_left hp.2.1 hsep.1.symm)
    have hd2 : E₁ ∩ C₂ = ∅ := Finset.disjoint_iff_inter_eq_empty.1
      (Finset.disjoint_of_subset_left hp.1.1 hsep.1)
    simp only [Finset.union_inter_distrib_right, Finset.inter_eq_left.2 hp.1.1,
      Finset.inter_eq_left.2 hp.2.1, hd1, hd2, Finset.union_empty, Finset.empty_union]
  · intro E hE
    rw [mem_indepSubsets] at hE
    rw [← pow_add]
    congr 1
    rw [← Finset.sum_union]
    · rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.2 hE.1]
    · exact Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right hsep.1)

/-- **Family factorisation**: for a pairwise separated family, `F_{⋃ C_i} = ∏ F_{C_i}`. -/
theorem compPoly_biUnion (b : ℕ → ℕ) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (C : ι → Finset ℕ) (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Separated (C i) (C j)) :
    compPoly b (s.biUnion C) = ∏ i ∈ s, compPoly b (C i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [compPoly, indepSubsets, Finset.filter_singleton, Indep]
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.prod_insert ha]
    have hsepA : Separated (C a) (s.biUnion C) := by
      refine ⟨?_, ?_⟩
      · rw [Finset.disjoint_biUnion_right]
        intro j hj
        exact (hsep a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj)
          (fun h => ha (h ▸ hj))).1
      · intro x hx y hy
        obtain ⟨j, hj, hyj⟩ := Finset.mem_biUnion.1 hy
        exact (hsep a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj)
          (fun h => ha (h ▸ hj))).2 x hx y hyj
    rw [compPoly_union b hsepA, ih (fun i hi j hj hij =>
      hsep i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)]

/-- **V67 coefficient factorisation**: `N_τ = [z^τ] ∏_i F_{C_i}` for `τ ≥ 0`. -/
theorem component_coefficient_factorization (b : ℕ → ℕ) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (C : ι → Finset ℕ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Separated (C i) (C j)) {τ : ℤ} (hτ : 0 ≤ τ) :
    compCount b (s.biUnion C) τ = (∏ i ∈ s, compPoly b (C i)).coeff τ.toNat := by
  rw [compCount_eq_coeff b _ hτ, compPoly_biUnion b s C hsep]

/-- In the raw source: omission sets avoiding the forced selected set `F` with `X(E) = 0` are
counted by `compCount (W/·) ((a, M) \ F) T`. -/
theorem forced_restricted_count_eq (a M : ℕ) (F : Finset ℕ) :
    ((Omega a M).filter (fun E => Disjoint E F ∧ Xd a M E = 0)).card =
      compCount (fun n => W a M ∅ / n) (Finset.Ioo a M \ F) (T a M ∅) := by
  classical
  unfold compCount
  congr 1
  ext E
  simp only [Finset.mem_filter, mem_Omega, mem_indepSubsets, Finset.subset_sdiff, Xd, Bm,
    sub_eq_zero]
  push_cast
  tauto

end Erdos287.PostV64V71
