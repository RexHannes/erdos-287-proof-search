import RequestProject.Erdos287.ResearchBankV11.Ledger

/-!
# Erdős #287 — Research Bank V12: ledger (append-only) and closure firewall

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `StatusV12`, `EpochV12`, `RowV12` — V12 scales, extending the V10/V11 scales by a verbatim
  constructor `old` (so no V11 status or epoch is re-interpreted);
* `v12Ledger = (v11Ledger.map embed) ++ v12New`;
* `v12_preserves_v11_ledger` — the embedded V11 ledger is a prefix of the V12 ledger and `embed`
  is injective (every V11 row, hence every V2–V10 row, keeps its name, epoch, status, evidence);
* `v12_frontier` — the V12 status statements (concrete Type-II/HB geometry: LEAN BANK; spectral
  estimate: EXTERNAL PROVIDER; composition: LEAN COMPOSITION FROM PROVIDERS; endpoint-only HB
  argument: FALSE; Erdős #287: OPEN);
* `no_ledger_path_closes_erdos287_v12` — no closure-DAG path from V12 base rows reaches #287.
-/

namespace Erdos287
namespace ResearchBankV12
namespace Ledger

open Erdos287.ResearchBankV8.Ledger Erdos287.ResearchBankV10.Ledger

/-- V12/V13 status scale. -/
inductive StatusV12
  | old (s : StatusV10)
  /-- Kernel-proved in the Lean bank. -/
  | leanBank
  /-- Explicit external analytic provider (hypothesis structure, never constructed). -/
  | externalProvider
  /-- Lean composition from visible external providers. -/
  | leanComposition
  /-- Externally audited certificate, not replayed by Lean. -/
  | externalAuditedCertificate
  /-- Pending an explicit numerical `M_an`. -/
  | pendingMan
  /-- Formula not supplied to the formalization. -/
  | notSupplied
  deriving DecidableEq, Repr

/-- V12/V13 epochs. -/
inductive EpochV12
  | old (e : EpochV10)
  | concreteTypeIIHB
  | finiteCertificate
  deriving DecidableEq, Repr

/-- A V12 row. -/
structure RowV12 where
  name : String
  epoch : EpochV12
  status : StatusV12
  evidence : EvidenceV8
  deriving DecidableEq, Repr

/-- Verbatim embedding of a V10/V11 row. -/
def embed (r : RowV10) : RowV12 := ⟨r.name, .old r.epoch, .old r.status, r.evidence⟩

theorem embed_injective : Function.Injective embed := by
  intro a b h
  cases a; cases b
  simp only [embed, RowV12.mk.injEq, EpochV12.old.injEq, StatusV12.old.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  subst h1 h2 h3 h4; rfl

/-- The frozen V11 ledger, embedded verbatim. -/
def v11Frozen : List RowV12 := ResearchBankV11.Ledger.v11Ledger.map embed

/-- The new V12 rows. -/
def v12New : List RowV12 :=
  [ ⟨"concrete repaired parameters and exact gates (78/145, 145/39)", .concreteTypeIIHB,
      .leanBank, .kernelProof⟩
  , ⟨"endpoint-only HB coverage claim", .concreteTypeIIHB, .old (.old .falseStatement),
      .finiteFixture⟩
  , ⟨"compatible-cell saving d (not |k|d)", .concreteTypeIIHB, .leanBank, .kernelProof⟩
  , ⟨"restored Type-II envelope exponent algebra", .concreteTypeIIHB, .leanBank, .kernelProof⟩
  , ⟨"restored Type-II spectral estimate", .concreteTypeIIHB, .externalProvider,
      .externalInterface⟩
  , ⟨"high-H / low-H prefactor and diagonal comparison", .concreteTypeIIHB, .leanBank,
      .kernelProof⟩
  , ⟨"Case II whole-rectangle Type-II margins", .concreteTypeIIHB, .leanBank, .kernelProof⟩
  , ⟨"HB three-way selection", .concreteTypeIIHB, .leanBank, .kernelProof⟩
  , ⟨"Case I Type-I routing (reserve mu-3theta-s >= zeta)", .concreteTypeIIHB, .leanBank,
      .kernelProof⟩
  , ⟨"frozen Type-I five domain margins (exact list)", .concreteTypeIIHB, .notSupplied,
      .researchRecord⟩
  , ⟨"Case III overlap and g1 > 0 on the Type-II window", .concreteTypeIIHB, .leanBank,
      .kernelProof⟩
  , ⟨"Case III g1 >= 4/13-mu+theta0/2+(337/2)zeta on r+s >= d*", .concreteTypeIIHB, .leanBank,
      .kernelProof⟩
  , ⟨"Case III g1 >= ...+(337/2)zeta on the full window r+s >= d*-zeta", .concreteTypeIIHB,
      .old (.old .falseStatement), .finiteFixture⟩
  , ⟨"Case III g1 >= ...+(337/2)zeta at the top corner of the lambda branch of d*",
      .concreteTypeIIHB, .old (.old .falseStatement), .finiteFixture⟩
  , ⟨"Case I rapid-decay margin mu-theta-r-s >= zeta (r < theta)", .concreteTypeIIHB,
      .leanBank, .kernelProof⟩
  , ⟨"Case III Type-I reserve G5 >= 19 zeta", .concreteTypeIIHB, .notSupplied,
      .researchRecord⟩
  , ⟨"full repaired HB support routing", .concreteTypeIIHB, .leanBank, .kernelProof⟩
  , ⟨"well-factorable truncation shortcut", .concreteTypeIIHB, .old (.old .falseStatement),
      .finiteFixture⟩
  , ⟨"rough-seed convolution identities", .concreteTypeIIHB, .leanBank, .kernelProof⟩
  , ⟨"rough-seed Siegel-Walfisz estimate", .concreteTypeIIHB, .externalProvider,
      .externalInterface⟩
  , ⟨"concrete asymptotic composition", .concreteTypeIIHB, .leanComposition,
      .conditionalOnInterfaces⟩
  , ⟨"Erdős #287", .concreteTypeIIHB, .old (.old .open), .researchRecord⟩ ]

/-- The complete V12 ledger. -/
def v12Ledger : List RowV12 := v11Frozen ++ v12New

/-- **V12 preserves the V11 ledger**: the embedded V11 ledger is a prefix, `embed` is injective,
and every V11 row appears verbatim (up to the embedding). -/
theorem v12_preserves_v11_ledger :
    v12Ledger.take ResearchBankV11.Ledger.v11Ledger.length =
        ResearchBankV11.Ledger.v11Ledger.map embed ∧
      Function.Injective embed ∧
      ∀ r ∈ ResearchBankV11.Ledger.v11Ledger, embed r ∈ v12Ledger := by
  refine ⟨?_, embed_injective, fun r hr => List.mem_append_left _ (List.mem_map_of_mem hr)⟩
  unfold v12Ledger v11Frozen
  rw [List.take_append_of_le_length (by simp)]
  simp

/-- The historical V11 status of the finite architecture is preserved verbatim. -/
theorem v11_finite_architecture_history_preserved :
    embed ⟨"viable finite architecture / overlapping finite certificate", .effectiveHandoff,
      .old .open, .researchRecord⟩ ∈ v12Ledger := by
  apply List.mem_append_left
  apply List.mem_map_of_mem
  unfold ResearchBankV11.Ledger.v11Ledger
  apply List.mem_append_right
  simp [ResearchBankV11.Ledger.v11New]

theorem v12New_no_closed : ∀ r ∈ v12New, r.status ≠ .old (.old .closed) := by decide

/-- **The V12 frontier.** -/
theorem v12_frontier :
    (∃ r ∈ v12New, r.name = "full repaired HB support routing" ∧ r.status = .leanBank) ∧
    (∃ r ∈ v12New, r.name = "restored Type-II spectral estimate" ∧
      r.status = .externalProvider) ∧
    (∃ r ∈ v12New, r.name = "concrete asymptotic composition" ∧ r.status = .leanComposition) ∧
    (∃ r ∈ v12New, r.name = "endpoint-only HB coverage claim" ∧
      r.status = .old (.old .falseStatement)) ∧
    (∀ r ∈ v12New, r.name = "Erdős #287" → r.status = .old (.old .open)) := by
  decide

theorem v12_leanBank_implies_kernel :
    ∀ r ∈ v12New, r.status = .leanBank → r.evidence = .kernelProof := by decide

theorem v12_external_not_kernel :
    ∀ r ∈ v12New, r.status = .externalProvider → r.evidence ≠ .kernelProof := by decide

/-- The V12 closure DAG. -/
def closureDAG : List ResearchBankV9.Ledger.Edge :=
  [ ⟨["concrete asymptotic composition", "restored Type-II spectral estimate",
      "rough-seed Siegel-Walfisz estimate", "numerical external constants"],
      "explicit numerical M_an"⟩
  , ⟨["explicit numerical M_an", "finite exclusion through U", "overlap M_an <= U+1"],
      "effective finite splice"⟩
  , ⟨["effective finite splice"], "Erdős #287"⟩ ]

/-- Base nodes: the V12 `LEAN BANK` rows. -/
def baseNodes : List String := (v12New.filter fun r => r.status = .leanBank).map (·.name)

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

/-- **No V12 ledger path closes Erdős #287.** -/
theorem no_ledger_path_closes_erdos287_v12 (n : ℕ) :
    "Erdős #287" ∉ derivable n ∧ "explicit numerical M_an" ∉ derivable n ∧
      "effective finite splice" ∉ derivable n := by
  rw [derivable_eq]; decide

end Ledger
end ResearchBankV12
end Erdos287
