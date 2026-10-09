import RequestProject.Erdos287.ResearchBankV7.Ledger

/-!
# Erdős #287 — Research Bank V8: epoch-aware status ledger

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Bookkeeping plus *proved* meta-statements only.  Historical status labels are metadata: a row is
data and never inhabits a mathematical proposition.

* `StatusV8` — the status scale `PROVED / CONDITIONAL / OPEN / KILLED METHOD /
  KILLED SUFFICIENT HYPOTHESIS / SUPERSEDED / FALSE / FINITE FIXTURE / FINITE SOURCE KILL /
  BLOCKED / HISTORICAL METADATA / CLOSED` (the last is forbidden);
* `EvidenceV8` — kernel proof / conditional on explicit interfaces / external interface /
  finite fixture / **research record** (status imported from the programme's written record and
  *not* machine-checked here);
* `EpochV8` — the V7 epochs plus the post-V7 ENTRY/window epoch and the GOOD-M epoch;
* the frozen V7 ledger is re-recorded verbatim through an injective verdict embedding
  (`v7_classifications_preserved`);
* machine-checked: no `CLOSED` row (`v8_no_closed`), Erdős #287 is `OPEN` (`v8_erdos287_open`),
  `PROVED ⟹ kernel proof` (`v8_proved_implies_kernel`), research-record rows are never `PROVED`
  (`v8_record_rows_not_proved`), and `OLD_WHOLE_PARENT_CAP` is a killed *sufficient hypothesis*
  while target-scale ENTRY is `OPEN`, not `FALSE` (`v8_cap_killed_entry_open`).
-/

namespace Erdos287
namespace ResearchBankV8
namespace Ledger

open Erdos287.ResearchBankV7.Epochs Erdos287.ResearchBankV7.Ledger

/-- The V8/V9 status scale. -/
inductive StatusV8
  | proved
  | conditional
  | «open»
  | killedMethod
  | killedSufficientHypothesis
  | superseded
  | falseStatement
  | finiteFixture
  | finiteSourceKill
  | blocked
  | historicalMetadata
  | closed
  deriving DecidableEq, Repr

/-- Evidence kinds. -/
inductive EvidenceV8
  /-- A Lean kernel proof in this bank (standard axioms only). -/
  | kernelProof
  /-- A Lean implication whose analytic premises are explicit, uninhabited hypotheses. -/
  | conditionalOnInterfaces
  /-- An external analytic statement, represented only as an uninhabited interface. -/
  | externalInterface
  /-- A finite fixture / counterfixture checked by the kernel; certifies no asymptotic claim. -/
  | finiteFixture
  /-- Status imported from the programme's written research record; **not** machine-checked. -/
  | researchRecord
  /-- Pure metadata (dates, numerical sizes, historical labels). -/
  | metadata
  deriving DecidableEq, Repr

/-- Research epochs: the V7 epochs plus the post-V7 epochs of V8 and V9. -/
inductive EpochV8
  | v7 (e : Epoch)
  | postV7Entry
  | goodM
  | directExclusion
  | asraFullWrittenCandidate
  | asraCorrected
  deriving DecidableEq, Repr

/-- Chronological index. -/
def EpochV8.index : EpochV8 → ℕ
  | .v7 e => e.index
  | .postV7Entry => 4
  | .goodM => 5
  | .directExclusion => 6
  | .asraFullWrittenCandidate => 7
  | .asraCorrected => 8

theorem epochV8_chronology :
    (EpochV8.v7 Epoch.entryFirst).index < EpochV8.postV7Entry.index ∧
    EpochV8.postV7Entry.index < EpochV8.goodM.index ∧
    EpochV8.goodM.index < EpochV8.directExclusion.index ∧
    EpochV8.directExclusion.index < EpochV8.asraFullWrittenCandidate.index ∧
    EpochV8.asraFullWrittenCandidate.index < EpochV8.asraCorrected.index := by decide

/-- A ledger row (pure decidable data). -/
structure RowV8 where
  name : String
  epoch : EpochV8
  status : StatusV8
  evidence : EvidenceV8
  deriving DecidableEq, Repr

/-- The V7 verdicts embed injectively into the V8 scale. -/
def ofV7 : VerdictV7 → StatusV8
  | .kernelBanked => .proved
  | .conditionalBanked => .conditional
  | .counterfixture => .finiteFixture
  | .finiteSourceKill => .finiteSourceKill
  | .ownerOpen => .open
  | .superseded => .superseded
  | .closed => .closed

theorem ofV7_injective : Function.Injective ofV7 := by
  intro a b h; cases a <;> cases b <;> simp_all [ofV7]

/-- The V7 evidence discipline, mapped (not reinterpreted: each V5 kind has its own image). -/
def ofV5Evidence : ResearchBankV5.EvidenceKind → EvidenceV8
  | .kernelProof => .kernelProof
  | .externalAnalyticBank => .externalInterface
  | .conditionalInterface => .conditionalOnInterfaces
  | .finiteRegressionOnly => .finiteFixture
  | .researchConjecture => .researchRecord

/-- The frozen V7 ledger, re-recorded verbatim. -/
def v7Frozen : List RowV8 :=
  v7Ledger.map fun r =>
    { name := r.name, epoch := .v7 r.epoch, status := ofV7 r.verdict,
      evidence := ofV5Evidence r.evidence }

/-- **Every V7 classification is preserved.** -/
theorem v7_classifications_preserved :
    ∀ r ∈ v7Ledger, ∃ r' ∈ v7Frozen, r'.name = r.name ∧ r'.status = ofV7 r.verdict ∧
      r'.epoch = .v7 r.epoch := by
  intro r hr
  exact ⟨_, List.mem_map_of_mem hr, rfl, rfl, rfl⟩

/-- The new V8 rows. -/
def v8New : List RowV8 :=
  [ ⟨"OLD whole-parent SEED-CAP (entry + |F_p| ≤ C N_p/(log N_p)^a, a>1)", .postV7Entry,
      .killedSufficientHypothesis, .conditionalOnInterfaces⟩
  , ⟨"whole-parent cap: finite forced-neighbour counting identities", .postV7Entry,
      .proved, .kernelProof⟩
  , ⟨"canonical saturation x*_n = 1 iff n | L_T (0→1, endpoints, no-00, entry, forbidden shrink)",
      .postV7Entry, .proved, .kernelProof⟩
  , ⟨"non-divisor count |{n ∈ I : n ∤ L_T}| = o(M)", .postV7Entry, .conditional,
      .externalInterface⟩
  , ⟨"rough multiplier uniqueness, disjoint supports, LCM gluing, endpoint-loss gcd formula",
      .postV7Entry, .proved, .kernelProof⟩
  , ⟨"rough labels pairwise coprime (false strengthening)", .postV7Entry, .falseStatement,
      .finiteFixture⟩
  , ⟨"RoughLabelSupply → LocalDeletionInput → SharedGridOutput (gluing implication)",
      .postV7Entry, .conditional, .conditionalOnInterfaces⟩
  , ⟨"weak-cutoff T=M/2 seed family (WEAK_CUTOFF_ENTRY_EXISTENCE)", .postV7Entry, .proved,
      .kernelProof⟩
  , ⟨"weak cutoff T=M/2 transfers to T=M/(2H)", .postV7Entry, .falseStatement, .finiteFixture⟩
  , ⟨"seed zero set o(M) and mass → log 3", .postV7Entry, .conditional, .externalInterface⟩
  , ⟨"target-scale ENTRY", .postV7Entry, .open, .researchRecord⟩
  , ⟨"exact prime-power entry system: p-local entry ⟺ full row congruence mod p^(r_p+1)",
      .postV7Entry, .proved, .kernelProof⟩
  , ⟨"top digit (mod p) suffices for the row congruence", .postV7Entry, .falseStatement,
      .finiteFixture⟩
  , ⟨"active-residue DP: state exactness, forgetting rule, resource exhaustion ≠ UNSAT",
      .postV7Entry, .proved, .kernelProof⟩
  , ⟨"boundary-bit-only DP as exact interface", .postV7Entry, .killedMethod, .finiteFixture⟩
  , ⟨"pairwise compatibility sufficiency", .postV7Entry, .killedMethod, .finiteFixture⟩
  , ⟨"raw sparse-owner SAT principle", .postV7Entry, .killedMethod, .researchRecord⟩
  , ⟨"rigid K2 obstruction (finite/logical core)", .postV7Entry, .proved, .kernelProof⟩
  , ⟨"K2 prime supply (infinitely many rigid contacts)", .postV7Entry, .conditional,
      .externalInterface⟩
  , ⟨"rigid K2 refutes the κ≥1 pseudoforest/orientation theorem", .postV7Entry, .falseStatement,
      .kernelProof⟩
  , ⟨"GOOD-M averaging bookkeeping (exact count, first-moment implication)", .goodM, .proved,
      .kernelProof⟩
  , ⟨"GOOD-M survivor-supply inequalities (|C_X|>0, completeness, first moment)", .goodM, .open,
      .researchRecord⟩
  , ⟨"certificate source interval C_Q(M)=[a,b] ⟺ M ∈ J(Q;a,b)", .goodM, .proved, .kernelProof⟩
  , ⟨"virtual edge = new physical contact", .goodM, .falseStatement, .finiteFixture⟩
  , ⟨"ternary blocker fixture (pairwise extendible, ternary UNSAT)", .postV7Entry,
      .finiteFixture, .finiteFixture⟩
  , ⟨"Erdős #287", .goodM, .open, .researchRecord⟩ ]

/-- The complete V8 ledger: the frozen V7 ledger followed by the new rows. -/
def v8Ledger : List RowV8 := v7Frozen ++ v8New

/-- **No `CLOSED` row.** -/
theorem v8_no_closed : ∀ r ∈ v8Ledger, r.status ≠ .closed := by decide

/-- **Erdős #287 is listed only as `OPEN`** among the new rows, and the frozen V7 block lists it
as `OPEN` and never as `CLOSED`. -/
theorem v8_erdos287_open :
    (∀ r ∈ v8New, r.name = "Erdős #287" → r.status = .open) ∧
    (∃ r ∈ v7Frozen, r.name = "Erdős #287" ∧ r.status = .open) ∧
    (∀ r ∈ v8Ledger, r.status ≠ .closed) := by
  refine ⟨by decide, ?_, v8_no_closed⟩
  obtain ⟨r, hr, hn, hv, -⟩ := erdos287_ownerOpen
  exact ⟨_, List.mem_map_of_mem hr, hn, by simp [ofV7, hv]⟩

/-- Among the new rows, `PROVED` requires a kernel proof. -/
theorem v8_proved_implies_kernel :
    ∀ r ∈ v8New, r.status = .proved → r.evidence = .kernelProof := by decide

/-- Research-record rows are never `PROVED`. -/
theorem v8_record_rows_not_proved :
    ∀ r ∈ v8Ledger, r.evidence = .researchRecord → r.status ≠ .proved := by decide

/-- External-interface rows are never `PROVED`. -/
theorem v8_external_not_proved :
    ∀ r ∈ v8Ledger, r.evidence = .externalInterface → r.status ≠ .proved := by decide

/-- **`OLD_WHOLE_PARENT_CAP` is a killed sufficient hypothesis; ENTRY is `OPEN`, not `FALSE`.** -/
theorem v8_cap_killed_entry_open :
    (∃ r ∈ v8New, r.status = .killedSufficientHypothesis) ∧
    (∃ r ∈ v8New, r.name = "target-scale ENTRY" ∧ r.status = .open) ∧
    ¬ ∃ r ∈ v8New, r.name = "target-scale ENTRY" ∧ r.status = .falseStatement := by decide

/-- A killed sufficient hypothesis is a different status from `FALSE` of its conclusion. -/
theorem killedSufficient_ne_false : StatusV8.killedSufficientHypothesis ≠ .falseStatement := by
  decide

/-- `SUPERSEDED` is a different status from `FALSE`. -/
theorem superseded_ne_false : StatusV8.superseded ≠ .falseStatement := by decide

end Ledger
end ResearchBankV8
end Erdos287
