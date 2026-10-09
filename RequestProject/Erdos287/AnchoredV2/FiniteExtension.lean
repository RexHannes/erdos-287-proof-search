import RequestProject.Erdos287.AnchoredV2.CoupledBatchSupply

/-!
# Anchored V2 — the finite coupled extension theorem

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Given a feasible tracked-prime kernel and an explicit finite `CoupledBatchSupply`, a full
physical word exists which

* retains every kernel bit (it agrees with the given kernel witness on all retained positions);
* satisfies every retained kernel constraint — endpoint pins, forced zeros, shared-position
  equalities, no-`00` adjacency, inherited high-power equations and every already completed
  tracked prime-power component;
* selects exactly a chosen batch of repair sites, each of whose no-`00` adjacency conditions to
  its two neighbours is satisfied;
* realises the prescribed coupled batch charge: `0 (mod 2^e)` and `t (mod p)`.

The converse (restriction) direction is literal, so under a supply the two notions of
solvability are finitely equivalent.  Everything here is finite; **no** large-`M` asymptotic
theorem is used.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV2

open TrackedPrimeKernel

/-- A full physical solution for the tracked kernel `K` with the coupled batch supply `S` and
target `p`-charge `t`: the word `w`, the selected batch `I`, and all preserved constraints. -/
def FullTrackedSolution {K : TrackedPrimeKernel} {p e : ℕ} (S : CoupledBatchSupply K p e)
    (t : ZMod p) (w : ℕ → Bool) (I : Finset (Fin S.n)) : Prop :=
  K.Satisfies w ∧
  (∀ i, w (S.pos i) = decide (i ∈ I)) ∧
  (∀ i, (w (S.pos i) || w (S.left i)) = true ∧ (w (S.pos i) || w (S.right i)) = true) ∧
  (∑ i ∈ I, S.a i = 0) ∧ (∑ i ∈ I, S.b i = t)

/-- **`finite_coupled_extension`.**  The finite coupled-batch extension theorem: a feasible
tracked kernel together with an explicit finite coupled-batch supply extends to a full physical
word, preserving all retained kernel bits and constraints and realising the prescribed coupled
batch charge. -/
theorem finite_coupled_extension {K : TrackedPrimeKernel} {p e : ℕ} (hloc : K.Localised)
    (S : CoupledBatchSupply K p e) {w₀ : ℕ → Bool} (hw₀ : K.Satisfies w₀) (t : ZMod p) :
    ∃ (w : ℕ → Bool) (I : Finset (Fin S.n)),
      (∀ x ∈ K.positions, w x = w₀ x) ∧ FullTrackedSolution S t w I := by
  classical
  obtain ⟨I, hA, hB⟩ := coupled_subset_sum S.p_prime S.p_odd S.e_pos S.enough S.a S.b
    S.a_unit S.b_unit t
  set P : Finset ℕ := I.image S.pos with hPdef
  set Q : Finset ℕ := Finset.univ.image S.pos with hQdef
  set w : ℕ → Bool := fun x => if x ∈ P then true else if x ∈ Q then false else w₀ x with hwdef
  have hagree : ∀ x ∈ K.positions, w x = w₀ x := by
    intro x hx
    have h1 : x ∉ P := by
      intro hmem
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hmem
      exact S.pos_fresh i (hi ▸ hx)
    have h2 : x ∉ Q := by
      intro hmem
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hmem
      exact S.pos_fresh i (hi ▸ hx)
    simp [hwdef, h1, h2]
  have hpos : ∀ i, w (S.pos i) = decide (i ∈ I) := by
    intro i
    by_cases hi : i ∈ I
    · have hmem : S.pos i ∈ P := Finset.mem_image_of_mem _ hi
      simp [hwdef, hmem, hi]
    · have h1 : S.pos i ∉ P := by
        intro hmem
        obtain ⟨j, hj, hji⟩ := Finset.mem_image.1 hmem
        exact hi (S.pos_inj hji ▸ hj)
      have h2 : S.pos i ∈ Q := Finset.mem_image_of_mem _ (Finset.mem_univ i)
      simp [hwdef, h1, h2, hi]
  obtain ⟨hs, hpin, hz, hadj0, hhigh, hlay⟩ := hw₀
  obtain ⟨lp, lz, ls, la⟩ := hloc
  refine ⟨w, I, hagree, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hpos, ?_, hA, hB⟩
  · intro E hE
    rw [hagree _ (ls E hE).1, hagree _ (ls E hE).2]
    exact hs E hE
  · intro x hx
    rw [hagree x (lp x hx)]
    exact hpin x hx
  · intro x hx
    rw [hagree x (lz x hx)]
    exact hz x hx
  · intro E hE
    rw [hagree _ (la E hE).1, hagree _ (la E hE).2]
    exact hadj0 E hE
  · intro g hg
    rw [S.highPower_local g hg w w₀ hagree]
    exact hhigh g hg
  · intro q hq
    rw [S.layerEq_local q hq w w₀ hagree]
    exact hlay q hq
  · intro i
    have hl : w (S.left i) = true := by
      rw [hagree _ (S.nbr_retained i).1]
      exact hpin _ (S.nbr_pinned i).1
    have hr : w (S.right i) = true := by
      rw [hagree _ (S.nbr_retained i).2]
      exact hpin _ (S.nbr_pinned i).2
    exact ⟨by rw [hl]; exact Bool.or_true _, by rw [hr]; exact Bool.or_true _⟩

/-- **`feasible_of_fullTrackedSolution`.**  `KERNEL-PROVED`.  The restriction direction: a full
physical solution restricts to a feasible tracked kernel. -/
theorem feasible_of_fullTrackedSolution {K : TrackedPrimeKernel} {p e : ℕ}
    {S : CoupledBatchSupply K p e} {t : ZMod p} {w : ℕ → Bool} {I : Finset (Fin S.n)}
    (h : FullTrackedSolution S t w I) : K.Feasible :=
  ⟨w, h.1⟩

/-- **`fullTrackedSolution_iff_feasible`.**  The finite equivalence *under supply*: given an
explicit finite coupled-batch supply, a full tracked solution exists exactly when the tracked
kernel is feasible. -/
theorem fullTrackedSolution_iff_feasible {K : TrackedPrimeKernel} {p e : ℕ} (hloc : K.Localised)
    (S : CoupledBatchSupply K p e) (t : ZMod p) :
    (∃ (w : ℕ → Bool) (I : Finset (Fin S.n)), FullTrackedSolution S t w I) ↔ K.Feasible := by
  constructor
  · rintro ⟨w, I, h⟩
    exact feasible_of_fullTrackedSolution h
  · rintro ⟨w₀, hw₀⟩
    obtain ⟨w, I, -, h⟩ := finite_coupled_extension hloc S hw₀ t
    exact ⟨w, I, h⟩

end AnchoredV2
end Erdos287
