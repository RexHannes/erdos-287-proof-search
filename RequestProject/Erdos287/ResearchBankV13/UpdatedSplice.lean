import RequestProject.Erdos287.ResearchBankV13.AuditedEndpoint

/-!
# Erdős #287 — Research Bank V13 §26: the updated finite/eventual splice

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* **`finite_eventual_splice`** (generic, natural numbers): `P M` for all `M ≤ U`, `P M` for all
  `M ≥ M_an`, and `M_an ≤ U + 1` ⟹ `P M` for all `M`.  All off-by-one cases are handled exactly:
  `splice_exact_boundary` (`M_an = U + 1` closes), `splice_gap_fixture` (`M_an = U + 2` leaves
  exactly the integer `U + 1` uncovered).
* `erdos287_of_splice` — the specialization to exact Erdős #287 counterexamples.
* **Two distinct finite routes.**  `OldFiniteArchitectureProvider` is the historical V11 contract
  (`FiniteArchitectureProvider`: an eventual exclusion engine through graph/CRT edges, still
  **OPEN**, `currentArchitecture = none`).  `FiniteIntervalCertificate` is a bounded exclusion
  engine.  `certificate_does_not_instantiate_architecture`: a certificate exists in the bank while
  no architecture provider is recorded.
* Firewall (c) `finite_certificate_not_eventual`: exclusion up to `U` does not give exclusion of
  all `M`.  Firewall (d) `eventual_without_threshold_does_not_splice` (V9, re-used).
-/

namespace Erdos287
namespace ResearchBankV13
namespace UpdatedSplice

open FiniteRepresentationModel IntervalCertificate

/-- **The generic finite/eventual splice.** -/
theorem finite_eventual_splice {P : ℕ → Prop} {U M_an : ℕ} (hfin : ∀ M ≤ U, P M)
    (hev : ∀ M, M_an ≤ M → P M) (hU : M_an ≤ U + 1) : ∀ M, P M := by
  intro M
  rcases le_or_gt M U with h | h
  · exact hfin M h
  · exact hev M (by omega)

/-- **Specialization**: finite exclusion to `U`, eventual exclusion from `M_an`, and
`M_an ≤ U + 1` give the full statement "no exact Erdős #287 counterexample". -/
theorem erdos287_of_splice {U M_an : ℕ} (hfin : NoCounterexampleUpTo U)
    (hev : ∀ M, M_an ≤ M → NoCounterexampleAt M) (hU : M_an ≤ U + 1) :
    ∀ A : Finset ℕ, ¬ Erdos287Counterexample A :=
  noCounterexample_all_iff.1 (finite_eventual_splice hfin hev hU)

/-- **Fixture 7: `M_an = U + 1` closes exactly.** -/
theorem splice_exact_boundary {P : ℕ → Prop} (U : ℕ) (hfin : ∀ M ≤ U, P M)
    (hev : ∀ M, U + 1 ≤ M → P M) : ∀ M, P M :=
  finite_eventual_splice hfin hev le_rfl

/-- **Fixture 6: `M_an = U + 2` leaves exactly one uncovered integer** (`U + 1`): the predicate
"`M ≠ U + 1`" holds up to `U` and from `U + 2` on, but not everywhere. -/
theorem splice_gap_fixture (U : ℕ) :
    (∀ M ≤ U, M ≠ U + 1) ∧ (∀ M, U + 2 ≤ M → M ≠ U + 1) ∧ ¬ (∀ M, M ≠ U + 1) ∧
      ∀ M, (M ≤ U ∨ U + 2 ≤ M) ↔ M ≠ U + 1 := by
  refine ⟨fun M h => by omega, fun M h => by omega, fun h => h (U + 1) rfl, fun M => by omega⟩

/-- **Firewall (c): a finite certificate to `U` does not prove arbitrary-large exclusion.** -/
theorem finite_certificate_not_eventual (U : ℕ) :
    ¬ ∀ P : ℕ → Prop, (∀ M ≤ U, P M) → ∀ M, P M := by
  intro h
  exact absurd (h (fun M => M ≤ U) (fun M hM => hM) (U + 1)) (by omega)

/-- **Firewall (d): an eventual theorem without an explicit threshold does not splice.** -/
theorem eventual_without_threshold_does_not_splice (U : ℕ) :
    ¬ ∀ bad : ℕ → Prop, (∃ M₀, ∀ M ≥ M₀, ¬ bad M) → (∀ M ≤ U, ¬ bad M) → ∀ M, ¬ bad M :=
  ResearchBankV9.Splice.asymptotic_without_threshold_does_not_splice U

/-! ## Two distinct finite routes -/

/-- The historical V11 finite-architecture contract (graph/CRT edges, eventual exclusion). -/
abbrev OldFiniteArchitectureProvider :=
  ResearchBankV11.FiniteArchitectureFrontier.FiniteArchitectureProvider

/-- The historical V11 contract still yields eventual exclusion (re-used). -/
theorem oldProvider_eventual {arch c M_geom ai aj t}
    (h : OldFiniteArchitectureProvider arch c M_geom ai aj t) :
    ResearchBankV9.Splice.EventualNoCounterexampleFrom M_geom :=
  ResearchBankV11.FiniteArchitectureFrontier.eventual_exclusion_of_architecture h

/-- **The new finite certificate does not instantiate the old architecture provider**: the bank
contains finite interval certificates, while the V11 architecture record is still `none`. -/
theorem certificate_does_not_instantiate_architecture :
    Nonempty FiniteIntervalCertificate ∧
      ResearchBankV11.FiniteArchitectureFrontier.currentArchitecture = none :=
  ⟨⟨DemonstrationPayload.demoCertificate⟩, rfl⟩

/-- The two routes have different conclusions: a certificate gives a *bounded* statement
(`NoCounterexampleUpTo last`), a provider an *eventual* one. -/
theorem routes_have_different_shapes (C : FiniteIntervalCertificate) :
    NoCounterexampleUpTo C.last := C.sound

/-- **Fixture 5 (V13 form): a splice input needs an explicit analytic threshold.** -/
structure SpliceInputV13 (A : ℝ) where
  M_an : ℕ
  M_an_current : ResearchBankV11.AnalyticActivation.current_M_an A = some M_an
  eventual : ∀ M, M_an ≤ M → NoCounterexampleAt M
  cert : FiniteIntervalCertificate
  overlap : M_an ≤ cert.last + 1

/-- A complete V13 splice input would close Erdős #287. -/
theorem spliceInputV13_sound {A : ℝ} (I : SpliceInputV13 A) :
    ∀ S : Finset ℕ, ¬ Erdos287Counterexample S :=
  erdos287_of_splice I.cert.sound I.eventual I.overlap

/-- **Missing numerical `M_an` blocks the splice** (for every target exponent). -/
theorem missing_M_an_blocks_splice (A : ℝ) : IsEmpty (SpliceInputV13 A) :=
  ⟨fun I => by
    have := I.M_an_current
    rw [ResearchBankV11.AnalyticActivation.current_M_an_eq_none] at this
    cases this⟩

end UpdatedSplice
end ResearchBankV13
end Erdos287
