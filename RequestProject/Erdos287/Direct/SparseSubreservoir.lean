import RequestProject.Erdos287.Direct.LargePrimeCompletionFinite

/-!
# Route D — the sparse subreservoir lemma

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The claim under audit is: *under the inherited Fourier hypothesis, a subset of size
`k = ⌈128 J² log(2q)⌉` still attains every residue modulo `q`.*

What is kernel-proved here is everything deterministic around it:

* attainment is monotone in the reservoir (`attainsAllTargets_mono`);
* the exact information-theoretic necessary condition `q ≤ 2^{|C|}`
  (`card_ge_of_attainsAllTargets`), which in particular constrains any admissible `k`;
* the reduction of the sparse claim to an exponential-sum bound *on the sparse set*
  (`sparseSubreservoir_of_expSum`).

The sparse claim itself, at the stated size `sparseSize`, is an **open node**: it is defined as
a proposition (`SparseSubreservoirClaim`) and deliberately **not inhabited**.
-/

open scoped BigOperators

namespace Erdos287
namespace Direct

variable {q : ℕ}

/-! ## D.28  Monotonicity and the information-theoretic floor -/

/-- **`attainsAllTargets_mono`.**  `KERNEL-PROVED`.  Enlarging the reservoir preserves
attainment. -/
theorem attainsAllTargets_mono {C C' : Finset ℕ} (h : C ⊆ C') (hC : AttainsAllTargets q C) :
    AttainsAllTargets q C' := by
  intro t
  obtain ⟨S, hSC, hS⟩ := hC t
  exact ⟨S, hSC.trans h, hS⟩

/-- **`card_ge_of_attainsAllTargets`.**  `KERNEL-PROVED`.  A reservoir attaining every residue
must satisfy `q ≤ 2^{|C|}`: there are only `2^{|C|}` binary selections. -/
theorem card_ge_of_attainsAllTargets [NeZero q] {C : Finset ℕ} (h : AttainsAllTargets q C) :
    q ≤ 2 ^ C.card := by
  classical
  have hsurj : ∀ t : ZMod q, ∃ S ∈ C.powerset, ∑ n ∈ S, (n : ZMod q)⁻¹ = t := by
    intro t
    obtain ⟨S, hSC, hS⟩ := h t
    exact ⟨S, Finset.mem_powerset.2 hSC, hS⟩
  have hcard : (Finset.univ : Finset (ZMod q)).card ≤ C.powerset.card := by
    refine Finset.card_le_card_of_surjOn (fun S => ∑ n ∈ S, (n : ZMod q)⁻¹) ?_
    intro t _
    obtain ⟨S, hS, hSt⟩ := hsurj t
    exact ⟨S, hS, hSt⟩
  rwa [Finset.card_univ, ZMod.card, Finset.card_powerset] at hcard

/-! ## D.29  The sparse claim -/

/-- The size threshold `k = ⌈128 J² log(2q)⌉` of the sparse subreservoir claim. -/
noncomputable def sparseSize (J q : ℕ) : ℕ := ⌈(128 : ℝ) * (J : ℝ) ^ 2 * Real.log (2 * q)⌉₊

/-- **Open node.**  The sparse subreservoir claim: inside a reservoir `C` there is a subset of
size at most `sparseSize J q` attaining every residue.  Not inhabited anywhere. -/
def SparseSubreservoirClaim (q J : ℕ) (C : Finset ℕ) : Prop :=
  ∃ D ⊆ C, D.card ≤ sparseSize J q ∧ AttainsAllTargets q D

/-- **`sparseClaim_forces_size`.**  `KERNEL-PROVED`.  The sparse claim can only hold when the
threshold is information-theoretically large enough: `q ≤ 2^{sparseSize J q}`. -/
theorem sparseClaim_forces_size [NeZero q] {J : ℕ} {C : Finset ℕ}
    (h : SparseSubreservoirClaim q J C) : q ≤ 2 ^ sparseSize J q := by
  obtain ⟨D, -, hcard, hD⟩ := h
  exact le_trans (card_ge_of_attainsAllTargets hD) (Nat.pow_le_pow_right (by norm_num) hcard)

/-- **`sparseClaim_gives_full`.**  `KERNEL-PROVED`.  The sparse claim implies attainment by the
full reservoir. -/
theorem sparseClaim_gives_full {J : ℕ} {C : Finset ℕ} (h : SparseSubreservoirClaim q J C) :
    AttainsAllTargets q C := by
  obtain ⟨D, hDC, -, hD⟩ := h
  exact attainsAllTargets_mono hDC hD

/-- **`sparseSubreservoir_of_expSum`.**  `KERNEL-PROVED` reduction, `CONDITIONAL` on an
exponential-sum bound for the *sparse* set: any subset `D ⊆ C` of admissible size which
satisfies the reciprocal exponential-sum interface with `(q−1)·B < 2^{|D|}` witnesses the
sparse claim.  This isolates exactly what the analytic input has to deliver. -/
theorem sparseSubreservoir_of_expSum [NeZero q] {J : ℕ} {C D : Finset ℕ} {B : ℝ}
    (hDC : D ⊆ C) (hsize : D.card ≤ sparseSize J q)
    (hBG : ReciprocalExpSumInterface q D B) (hlt : ((q : ℝ) - 1) * B < 2 ^ D.card) :
    SparseSubreservoirClaim q J C :=
  ⟨D, hDC, hsize, allTargets_of_expSumInterface hBG hlt⟩

end Direct
end Erdos287
