import RequestProject.Erdos287.ResearchBankV13.EffectiveFrontier

/-!
# Erdős #287 — Research Bank V13: status ledger (append-only) and closure firewall

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `v13Ledger = v12Ledger ++ v13New` (V12 row type; no V12 row is re-interpreted);
* `v13_preserves_v12_ledger` — the V12 ledger is a prefix of the V13 ledger (and hence every
  V11 row, including the historical "viable finite architecture / overlapping finite certificate:
  OPEN" row, is preserved verbatim);
* `v13_status_ledger` — the required current statuses:
  concrete Type-II/HB geometry: LEAN BANK; analytic spectral/SW/BV inputs: EXTERNAL PROVIDERS;
  conditional asymptotic composition: LEAN COMPOSITION FROM PROVIDERS; generic finite interval
  certificate theorem: LEAN BANK; concrete 10^500 payload: EXTERNAL AUDITED CERTIFICATE;
  explicit `M_an`: NONE; overlap test: PENDING `M_an`; Erdős #287: OPEN;
* `no_ledger_path_closes_erdos287_v13` — no closure-DAG path reaches #287: the splice edge needs
  an explicit `M_an` **and** the overlap `M_an ≤ U + 1`, neither of which is a base row.
-/

namespace Erdos287
namespace ResearchBankV13
namespace Ledger

open Erdos287.ResearchBankV8.Ledger ResearchBankV12.Ledger

/-- The new V13 rows. -/
def v13New : List RowV12 :=
  [ ⟨"concrete repaired Type-II/HB geometry", .finiteCertificate, .leanBank, .kernelProof⟩
  , ⟨"analytic spectral/SW/BV inputs", .finiteCertificate, .externalProvider,
      .externalInterface⟩
  , ⟨"conditional asymptotic composition", .finiteCertificate, .leanComposition,
      .conditionalOnInterfaces⟩
  , ⟨"prime-layer lemma", .finiteCertificate, .leanBank, .kernelProof⟩
  , ⟨"harmonic two-hole theorem", .finiteCertificate, .leanBank, .kernelProof⟩
  , ⟨"Family A interval theorem (p = 2q+1)", .finiteCertificate, .leanBank, .kernelProof⟩
  , ⟨"Family B interval theorem (p = 4q+1)", .finiteCertificate, .leanBank, .kernelProof⟩
  , ⟨"Proth / Pocklington witness soundness", .finiteCertificate, .leanBank, .kernelProof⟩
  , ⟨"generic finite interval certificate theorem", .finiteCertificate, .leanBank, .kernelProof⟩
  , ⟨"demonstration payload (generated in V13, Lean-replayed, endpoint < 10^61)",
      .finiteCertificate, .leanBank, .kernelProof⟩
  , ⟨"concrete 10^500 payload", .finiteCertificate, .externalAuditedCertificate, .metadata⟩
  , ⟨"finite/eventual splice with exact U+1 boundary", .finiteCertificate, .leanBank,
      .kernelProof⟩
  , ⟨"explicit M_an", .finiteCertificate, .old .none, .researchRecord⟩
  , ⟨"overlap test M_an <= U+1", .finiteCertificate, .pendingMan, .researchRecord⟩
  , ⟨"current global splice", .finiteCertificate, .old (.old .blocked), .researchRecord⟩
  , ⟨"Erdős #287", .finiteCertificate, .old (.old .open), .researchRecord⟩ ]

/-- The complete V13 ledger. -/
def v13Ledger : List RowV12 := v12Ledger ++ v13New

/-- **V13 preserves the V12 ledger** (prefix; every row unchanged). -/
theorem v13_preserves_v12_ledger :
    v13Ledger.take v12Ledger.length = v12Ledger ∧ ∀ r ∈ v12Ledger, r ∈ v13Ledger :=
  ⟨List.take_left, fun _ hr => List.mem_append_left _ hr⟩

/-- **The historical V11 finite-architecture status is preserved rather than rewritten.** -/
theorem v11_finite_architecture_history_preserved_v13 :
    embed ⟨"viable finite architecture / overlapping finite certificate", .effectiveHandoff,
      .old .open, .researchRecord⟩ ∈ v13Ledger :=
  List.mem_append_left _ v11_finite_architecture_history_preserved

theorem v13New_no_closed : ∀ r ∈ v13New, r.status ≠ .old (.old .closed) := by decide

/-- **The V13 status ledger.** -/
theorem v13_status_ledger :
    (∃ r ∈ v13New, r.name = "concrete repaired Type-II/HB geometry" ∧ r.status = .leanBank) ∧
    (∃ r ∈ v13New, r.name = "analytic spectral/SW/BV inputs" ∧ r.status = .externalProvider) ∧
    (∃ r ∈ v13New, r.name = "conditional asymptotic composition" ∧
      r.status = .leanComposition) ∧
    (∃ r ∈ v13New, r.name = "generic finite interval certificate theorem" ∧
      r.status = .leanBank) ∧
    (∃ r ∈ v13New, r.name = "concrete 10^500 payload" ∧
      r.status = .externalAuditedCertificate) ∧
    (∃ r ∈ v13New, r.name = "explicit M_an" ∧ r.status = .old .none) ∧
    (∃ r ∈ v13New, r.name = "overlap test M_an <= U+1" ∧ r.status = .pendingMan) ∧
    (∀ r ∈ v13New, r.name = "Erdős #287" → r.status = .old (.old .open)) := by
  decide

theorem v13_leanBank_implies_kernel :
    ∀ r ∈ v13New, r.status = .leanBank → r.evidence = .kernelProof := by decide

/-- The external audited payload row is never recorded as a kernel proof. -/
theorem v13_payload_not_kernel :
    ∀ r ∈ v13New, r.status = .externalAuditedCertificate → r.evidence ≠ .kernelProof := by decide

/-- The V13 closure DAG: the splice needs an explicit `M_an` and the overlap. -/
def closureDAG : List ResearchBankV9.Ledger.Edge :=
  [ ⟨["conditional asymptotic composition", "analytic spectral/SW/BV inputs",
      "numerical external constants"], "explicit M_an"⟩
  , ⟨["explicit M_an", "generic finite interval certificate theorem",
      "overlap test M_an <= U+1", "finite/eventual splice with exact U+1 boundary"],
      "current global splice"⟩
  , ⟨["current global splice"], "Erdős #287"⟩ ]

/-- Base nodes: the V12 and V13 `LEAN BANK` rows. -/
def baseNodes : List String :=
  ((v12New ++ v13New).filter fun r => r.status = .leanBank).map (·.name)

def step (S : List String) : List String :=
  S ++ (closureDAG.filter fun e => e.premises.all fun p => p ∈ S).map (·.conclusion)

def derivable : ℕ → List String
  | 0 => baseNodes
  | n + 1 => step (derivable n)

theorem step_baseNodes : step baseNodes = baseNodes := by decide

theorem derivable_eq (n : ℕ) : derivable n = baseNodes := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [derivable, ih, step_baseNodes]

/-- **No V13 ledger path closes Erdős #287** (nor `M_an`, nor the global splice). -/
theorem no_ledger_path_closes_erdos287_v13 (n : ℕ) :
    "Erdős #287" ∉ derivable n ∧ "explicit M_an" ∉ derivable n ∧
      "current global splice" ∉ derivable n := by
  rw [derivable_eq]; decide

/-! ## §31 Regression fixtures (bundle) -/

/-- **All ten regression fixtures, in one statement.** -/
theorem all_regression_fixtures (U : ℕ) :
    -- 1. endpoint-only HB internal counterfixture
    (¬ ∀ θ r s ν : ℚ, ResearchBankV12.EndpointCounterfixture.InOldWFSupport θ r s →
      r ≤ ResearchBankV12.ConcreteParameters.rStar ν →
      s ≤ ResearchBankV12.ConcreteParameters.sStar ν →
      0 ≤ ResearchBankV12.EndpointCounterfixture.oldMargin2
        (ResearchBankV12.ConcreteParameters.rStar ν)
        (ResearchBankV12.ConcreteParameters.sStar ν) ν →
      0 ≤ ResearchBankV12.EndpointCounterfixture.oldMargin2 r s ν) ∧
    -- 2. old |k|d alpha-count failure
    (ResearchBankV12.CompatibleCellsConcrete.fixtureA.detectorClasses.card ≠
      ResearchBankV12.CompatibleCellsConcrete.fixtureA.K *
        ResearchBankV12.CompatibleCellsConcrete.fixtureA.d) ∧
    -- 3. low-H smaller-norm-without-prefactor failure
    (¬ ∀ Plo Phi nlo nhi : ℝ, 0 < Plo → 0 < Phi → 0 < nlo → nlo < nhi →
      Plo ^ 2 * nlo < Phi ^ 2 * nhi) ∧
    -- 4. well-factorable truncation failure
    (¬ ∀ (lam : ℕ → ℤ) (D D' : ℕ), D' ≤ D →
      ResearchBankV10.WellFactorableCutoff.WellFactorable lam D →
      ResearchBankV10.WellFactorableCutoff.WellFactorable
        (ResearchBankV10.WellFactorableCutoff.truncate lam D') D') ∧
    -- 5. missing numerical M_an blocks the splice
    (∀ A : ℝ, IsEmpty (UpdatedSplice.SpliceInputV13 A)) ∧
    -- 6. M_an = U + 2 leaves one uncovered integer
    (¬ (∀ M, M ≠ U + 1) ∧ ∀ M, (M ≤ U ∨ U + 2 ≤ M) ↔ M ≠ U + 1) ∧
    -- 7. M_an = U + 1 closes exactly
    (∀ P : ℕ → Prop, (∀ M ≤ U, P M) → (∀ M, U + 1 ≤ M → P M) → ∀ M, P M) ∧
    -- 8. malformed Proth witness rejected
    (PrimeCertificates.prothCheck 5 2 2 = false) ∧
    -- 9. malformed Pocklington witness rejected
    (PrimeCertificates.pocklingtonCheck 3 173 2 10 = false) ∧
    -- 10. a non-contiguous interval list fails the certificate interface
    (¬ IntervalCertificate.Chain 0 [IntervalCertificate.gapStep1, IntervalCertificate.gapStep2]
      10) :=
  ⟨ResearchBankV12.EndpointCounterfixture.topCorner_check_does_not_cover,
    ResearchBankV12.CompatibleCellsConcrete.old_count_fails_concrete.1,
    ResearchBankV12.RestoredTypeIIEnvelope.lowH_without_prefactor_fails.1,
    ResearchBankV12.HBFullSupportConcrete.wf_truncation_firewall,
    UpdatedSplice.missing_M_an_blocks_splice,
    ⟨(UpdatedSplice.splice_gap_fixture U).2.2.1, (UpdatedSplice.splice_gap_fixture U).2.2.2⟩,
    fun _ h1 h2 => UpdatedSplice.splice_exact_boundary U h1 h2,
    PrimeCertificates.malformed_proth_rejected.1,
    PrimeCertificates.malformed_pocklington_rejected.1,
    IntervalCertificate.noncontiguous_rejected⟩

end Ledger
end ResearchBankV13
end Erdos287
