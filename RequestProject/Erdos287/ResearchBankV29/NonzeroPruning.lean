import RequestProject.Erdos287.ResearchBankV29.KernelRealization

/-!
# Erdős #287 — Research Bank V29 §6: the nonzero pruning contract

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

## Audit finding

`NonzeroPruningContract Rnz Ds bs Γ P NU x` (V27) takes the nonzero-frequency value `Rnz : ℂ` as a
free argument.  In V28 it enters only through `NonzeroCleanRealization`, whose value is
`DEnz M (Λ)` for an UNINTERPRETED functional `DEnz`.  There is no physical operator `R_nonzero` in
V2–V28, so the exact decomposition `R_nonzero = P_clean + E_mixed + … + E_other` cannot be
reconstructed "from the physical operator".  **The contract is therefore NOT retired in V29**; it
remains inside the explicitly labelled internal glue owner (`ProviderElimination`).

## What is proved (LEAN BANK)

* `NonzeroSectorDecomposition` — the exact seven-sector decomposition shape required by §6
  (mixed, reference, shared-gcd, cross-gcd, short-difference, diagonal, other), with one bound per
  sector, stated BEFORE estimates as an exact identity;
* `nonzero_pruning_from_sector_decomposition` — any such exact sector decomposition whose sector
  bounds sum to at most `NU · x^{−347/836000}` yields `NonzeroPruningContract` (no combination by
  name: the seven norms are added by the triangle inequality);
* `pruning_contract_empty` / `nonzero_realization_zero` — for the value `0` the contract and the
  whole V28 clean realization are satisfied by the EMPTY clean family.  This is the formal reason the
  V28 `nonzero` field carries no source content while `DEnz` is uninterpreted (see `SameSourceChain`
  in V30);
* `pruning_contract_nontrivial` — the contract is not vacuous in general (`Rnz = 1`, empty family,
  `NU = 0` fails).
-/

namespace Erdos287
namespace ResearchBankV29
namespace NonzeroPruning

open Finset ResearchBankV27.DISpectral ResearchBankV27.CleanNonzero
  ResearchBankV27.GlobalConductorSum ResearchBankV28.RepairedAnalyticBundle

/-- The seven error sectors of the nonzero-frequency operator, with an EXACT identity and one
bound per sector (the shape demanded by task §6). -/
structure NonzeroSectorDecomposition {β : Type*} (Rnz : ℂ) (Ds : Finset ℕ) (bs : ℕ → Finset β)
    (Γ P : ℕ → β → ℂ) where
  Emixed : ℂ
  Eref : ℂ
  Eshared : ℂ
  Ecross : ℂ
  Eshort : ℂ
  Ediag : ℂ
  Eother : ℂ
  bmixed : ℝ
  bref : ℝ
  bshared : ℝ
  bcross : ℝ
  bshort : ℝ
  bdiag : ℝ
  bother : ℝ
  exact : Rnz = (∑ D ∈ Ds, ∑ b ∈ bs D, Γ D b * P D b) + Emixed + Eref + Eshared + Ecross +
    Eshort + Ediag + Eother
  hmixed : ‖Emixed‖ ≤ bmixed
  href : ‖Eref‖ ≤ bref
  hshared : ‖Eshared‖ ≤ bshared
  hcross : ‖Ecross‖ ≤ bcross
  hshort : ‖Eshort‖ ≤ bshort
  hdiag : ‖Ediag‖ ≤ bdiag
  hother : ‖Eother‖ ≤ bother

/-- **Pruning contract from an exact sector decomposition** (LEAN BANK). -/
theorem nonzero_pruning_from_sector_decomposition {β : Type*} {Rnz : ℂ} {Ds : Finset ℕ}
    {bs : ℕ → Finset β} {Γ P : ℕ → β → ℂ} {NU x : ℝ}
    (S : NonzeroSectorDecomposition Rnz Ds bs Γ P)
    (hsum : S.bmixed + S.bref + S.bshared + S.bcross + S.bshort + S.bdiag + S.bother ≤
      NU * x ^ (-(347 / 836000 : ℝ))) :
    NonzeroPruningContract Rnz Ds bs Γ P NU x := by
  refine ⟨⟨S.Emixed + S.Eref + S.Eshared + S.Ecross + S.Eshort + S.Ediag + S.Eother, ?_, ?_⟩⟩
  · have := S.exact
    linear_combination this
  · have h1 := norm_add_le (S.Emixed + S.Eref + S.Eshared + S.Ecross + S.Eshort + S.Ediag) S.Eother
    have h2 := norm_add_le (S.Emixed + S.Eref + S.Eshared + S.Ecross + S.Eshort) S.Ediag
    have h3 := norm_add_le (S.Emixed + S.Eref + S.Eshared + S.Ecross) S.Eshort
    have h4 := norm_add_le (S.Emixed + S.Eref + S.Eshared) S.Ecross
    have h5 := norm_add_le (S.Emixed + S.Eref) S.Eshared
    have h6 := norm_add_le S.Emixed S.Eref
    linarith [S.hmixed, S.href, S.hshared, S.hcross, S.hshort, S.hdiag, S.hother]

/-- The contract for value `0` with any family is satisfied by `E = −(clean aggregate)` only if
that is small; for the EMPTY family it holds outright (LEAN BANK). -/
theorem pruning_contract_empty {β : Type*} (bs : ℕ → Finset β) (Γ P : ℕ → β → ℂ) {NU x : ℝ}
    (hNU : 0 ≤ NU) (hx : 0 ≤ x) : NonzeroPruningContract (0 : ℂ) ∅ bs Γ P NU x :=
  ⟨⟨0, by simp, by simpa using mul_nonneg hNU (Real.rpow_nonneg hx _)⟩⟩

/-- **The contract is not vacuous** (FINITE REGRESSION). -/
theorem pruning_contract_nontrivial {β : Type*} (bs : ℕ → Finset β) (Γ P : ℕ → β → ℂ) (x : ℝ) :
    ¬ NonzeroPruningContract (1 : ℂ) ∅ bs Γ P 0 x := by
  rintro ⟨E, hE, hb⟩
  simp only [sum_empty, zero_add] at hE
  subst hE
  norm_num at hb

/-- **The V28 clean realization holds for the value `0` with the empty clean family** (LEAN BANK),
for EVERY `DIClass`. -/
theorem nonzero_realization_zero (DIClass : KloostermanData → Prop) {x Cnz : ℝ} (hx : 0 ≤ x)
    (hC : 0 ≤ Cnz) : NonzeroCleanRealization DIClass x 0 Cnz := by
  refine ⟨Empty, 0, 0, 0, ∅, fun _ => ∅, fun _ b => b.elim, fun _ _ => 0, 0, le_rfl, hC,
    by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, pruning_contract_empty _ _ _ le_rfl hx, by simp⟩
  · intro D hD; simp at hD
  · intro D hD; simp at hD
  · intro D hD; simp at hD
  · intro D hD; simp at hD
  · intro D hD; simp at hD
  · exact ⟨by simpa using Real.rpow_nonneg hx _⟩

end NonzeroPruning
end ResearchBankV29
end Erdos287
