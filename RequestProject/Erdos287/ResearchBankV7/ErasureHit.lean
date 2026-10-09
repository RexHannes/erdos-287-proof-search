import RequestProject.Erdos287.ResearchBankV7.Spine

/-!
# Erdős #287 — Research Bank V7: ERASURE-HIT (exact robustness of a certified spine)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Exact rational/integer robustness statement.  If a certified spine `𝒫` lies inside an intermediate
support, `𝒫 ⊆ T' ⊆ T`, then the certified lattice interval survives **any** treatment of the
remaining non-spine coordinates:

* `erasure_hit` — every certified lattice value is still hit by a subset of `T'` whose support is
  contained in the spine, i.e. all non-spine coordinates are erased (set to `0`);
* `erasure_hit_with_fixed_part` — if an arbitrary non-spine part `F ⊆ T' \ 𝒫` is instead fixed to
  `1`, the whole certified interval is hit *translated by the mass of `F`*, again exactly;
* `erasure_hit_complement` — the two-sided form.  Writing `W = ∑_{n ∈ T'} w n` for the total
  weight, if `g ∣ W` and the certified interval reaches at least half of the total weight
  (`W ≤ 2B`, the exact overlap condition), then **every** lattice point of `[A, W − A]` is an
  exact subset weight of `T'`.  In `J`-numerator units with `w n = J/n` this is precisely
  `[α, ∑_{n ∈ T'} 1/n − α] ∩ (1/J)ℤ`.
* `erasure_hit_rational` — the same statement in rational mass language.

**Terminology firewall.**  As in `IntervalLifting`, a failed overlap condition means the
certificate does not apply; it is *not* an UNSAT statement (`overlap_failure_is_not_unsat`).
-/

namespace Erdos287
namespace ResearchBankV7
namespace ErasureHit

open Finset IntervalLifting

/-! ## 1.  Erasing the non-spine coordinates -/

/-- **ERASURE-HIT (kernel).**  For `𝒫 ⊆ T'`, every value of the certified lattice interval is
still reached inside `T'`, by a subset of the spine: all remaining non-spine coordinates are
erased to `0`. -/
theorem erasure_hit {w : ℕ → ℤ} {P T' : Finset ℕ} {g A B : ℤ} (hPT : P ⊆ T')
    (hP : ReachesLattice w P g A B) :
    ∀ n : ℤ, g ∣ n → A ≤ n → n ≤ B → ∃ S, S ⊆ P ∧ S ⊆ T' ∧ ∑ x ∈ S, w x = n := by
  intro n hg hA hB
  obtain ⟨S, hS, hsum⟩ := hP n hg hA hB
  exact ⟨S, hS, hS.trans hPT, hsum⟩

/-- **ERASURE-HIT with an arbitrary fixed part (kernel).**  If the non-spine coordinates are not
erased but an arbitrary part `F` of them is fixed to `1`, the reachable values of `T'` contain the
certified interval translated by the weight of `F`, exactly. -/
theorem erasure_hit_with_fixed_part {w : ℕ → ℤ} {P T' F : Finset ℕ} {g A B : ℤ}
    (hPT : P ⊆ T') (hF : F ⊆ T' \ P) (hP : ReachesLattice w P g A B) :
    ∀ n : ℤ, g ∣ n → A ≤ n → n ≤ B →
      ∃ S ⊆ T', ∑ x ∈ S, w x = n + ∑ x ∈ F, w x := by
  intro n hg hA hB
  obtain ⟨S, hS, hsum⟩ := hP n hg hA hB
  have hdisj : Disjoint S F := by
    refine Finset.disjoint_left.2 ?_
    intro a haS haF
    exact (Finset.mem_sdiff.1 (hF haF)).2 (hS haS)
  refine ⟨S ∪ F, Finset.union_subset (hS.trans hPT) (hF.trans Finset.sdiff_subset), ?_⟩
  rw [Finset.sum_union hdisj, hsum]

/-! ## 2.  The two-sided (complement) form -/

/-- **ERASURE-HIT, two-sided (kernel).**  Let `W = ∑_{x ∈ T'} w x`.  If the certified spine
interval `[A, B]` satisfies the exact overlap condition `W ≤ 2B` and `g ∣ W`, then every lattice
point of `[A, W − A]` is an exact subset weight of `T'`. -/
theorem erasure_hit_complement {w : ℕ → ℤ} {P T' : Finset ℕ} {g A B : ℤ} (hPT : P ⊆ T')
    (hP : ReachesLattice w P g A B) (hW : g ∣ ∑ x ∈ T', w x)
    (hover : ∑ x ∈ T', w x ≤ 2 * B) :
    ReachesLattice w T' g A (∑ x ∈ T', w x - A) := by
  classical
  set W : ℤ := ∑ x ∈ T', w x with hWdef
  intro n hg hA hB
  by_cases hnB : n ≤ B
  · exact (hP.mono hPT) n hg hA hnB
  · push_neg at hnB
    have hgm : g ∣ W - n := dvd_sub hW hg
    obtain ⟨S, hS, hsum⟩ := hP (W - n) hgm (by omega) (by omega)
    refine ⟨T' \ S, Finset.sdiff_subset, ?_⟩
    rw [Finset.sum_sdiff_eq_sub (hS.trans hPT), hsum, ← hWdef]
    ring

/-! ## 3.  Rational mass form -/

/-- **ERASURE-HIT in rational mass language.**  With `w n = J / n` for denominators dividing `J`,
a certified lattice value `k` corresponds to the rational mass `k / J`; the statement above says
that every rational of the form `k/J` in the certified window is an exact subset mass of `T'`. -/
theorem erasure_hit_rational {w : ℕ → ℤ} {P T' : Finset ℕ} {g A B : ℤ} {J : ℕ} (hJ : 0 < J)
    (f : ℕ → ℚ) (hf : ∀ x, f x = (w x : ℚ) / J)
    (hPT : P ⊆ T') (hP : ReachesLattice w P g A B) :
    ∀ k : ℤ, g ∣ k → A ≤ k → k ≤ B →
      ∃ S ⊆ T', ∑ x ∈ S, f x = (k : ℚ) / J := by
  intro k hg hA hB
  obtain ⟨S, hSP, hST, hsum⟩ := erasure_hit hPT hP k hg hA hB
  refine ⟨S, hST, ?_⟩
  have hJ' : (J : ℚ) ≠ 0 := by positivity
  calc ∑ x ∈ S, f x = ∑ x ∈ S, ((w x : ℚ) / J) := Finset.sum_congr rfl (fun x _ => hf x)
    _ = (∑ x ∈ S, (w x : ℚ)) / J := by rw [Finset.sum_div]
    _ = (k : ℚ) / J := by rw [← Int.cast_sum, hsum]

/-! ## 4.  Terminology firewall -/

/-- **Firewall.**  A violated overlap condition (`2B < W`) only means that the two-sided form does
not apply; the one-sided certified interval is untouched and nothing is unsatisfiable. -/
theorem overlap_failure_is_not_unsat :
    ∃ (w : ℕ → ℤ) (P T' : Finset ℕ) (g A B : ℤ),
      P ⊆ T' ∧ ReachesLattice w P g A B ∧ 2 * B < ∑ x ∈ T', w x := by
  refine ⟨fun _ => 10, ∅, {1, 2}, 1, 0, 0, by simp, ?_, by decide⟩
  intro n _ hA hB
  exact ⟨∅, by simp, by simp; omega⟩

end ErasureHit
end ResearchBankV7
end Erdos287
