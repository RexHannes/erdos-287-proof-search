import RequestProject.Erdos287.ResearchBankV8.Ledger

/-!
# Erdős #287 — Research Bank V9: epoch-aware status ledger and closure firewall

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Extends the V8 ledger (which itself freezes V7) with the direct-exclusion / graph / ASRA /
splice rows.  Machine-checked:

* `v9_no_closed` — no row of the complete V9 ledger is `CLOSED`;
* `v9_erdos287_open` — Erdős #287 is listed only as `OPEN`;
* `asra_epochs` — the historical "ASRA = full written candidate" row is `SUPERSEDED`
  (certification rollback) in the historical epoch, while the current `full ASRA` row is `OPEN`,
  and the two open ASRA interfaces are `OPEN`;
* `splice_blocked` — the effective finite splice is `BLOCKED`, eventual exclusion `CONDITIONAL`;
* `no_ledger_path_closes_erdos287` — along the recorded closure DAG, propagation from the
  `PROVED` rows (a node becomes derivable when all premises of one of its edges are derivable)
  reaches a fixpoint that does **not** contain Erdős #287, for every number of steps.
-/

namespace Erdos287
namespace ResearchBankV9
namespace Ledger

open Erdos287.ResearchBankV8.Ledger

/-- The new V9 rows. -/
def v9New : List RowV8 :=
  [ ⟨"gcd-clique CRT core (gcd identity, general CRT, compatibility ⟺ clique)", .directExclusion,
      .proved, .kernelProof⟩
  , ⟨"prescribed-shape gcd clique: box placement (union-bound argument)", .directExclusion,
      .open, .researchRecord⟩
  , ⟨"Maynard prime supply on the clique (PrimeValuesOnClique)", .directExclusion, .conditional,
      .externalInterface⟩
  , ⟨"affine contact identity and adjacent physical locations", .directExclusion, .proved,
      .kernelProof⟩
  , ⟨"circular annulus graph: α(G(n,r)) = r+1 and χ_f = n/(r+1)", .directExclusion, .proved,
      .kernelProof⟩
  , ⟨"graph-selective occupancy", .directExclusion, .proved, .kernelProof⟩
  , ⟨"145/39 graph gate (G(145,38): α=39, χ_f=145/39; 26/7 < 145/39)", .directExclusion,
      .proved, .kernelProof⟩
  , ⟨"7/13 − 78/145 = 1/1885", .directExclusion, .proved, .kernelProof⟩
  , ⟨"localization constant 39/106 > 1/e (106/39 < e)", .directExclusion, .proved,
      .kernelProof⟩
  , ⟨"graph localization ⟹ no #287 representation (given edge data)", .directExclusion, .proved,
      .kernelProof⟩
  , ⟨"graph architecture upper limit χ_f ≤ ρ+1", .directExclusion, .proved, .kernelProof⟩
  , ⟨"three-group A<3 architecture", .directExclusion, .superseded, .researchRecord⟩
  , ⟨"arbitrary-F A≥3 moment route", .directExclusion, .killedMethod, .researchRecord⟩
  , ⟨"Chen parameter tuning below 3", .directExclusion, .killedMethod, .researchRecord⟩
  , ⟨"ASRA = FULL WRITTEN CANDIDATE (pending hostile referee)", .asraFullWrittenCandidate,
      .superseded, .researchRecord⟩
  , ⟨"CRT/collision/prime-slot algebra", .asraCorrected, .proved, .kernelProof⟩
  , ⟨"polynomial-root CRT normalization (roots ↔ slot allocations)", .asraCorrected, .proved,
      .kernelProof⟩
  , ⟨"within-product collision zero", .asraCorrected, .proved, .kernelProof⟩
  , ⟨"correct main modulus lcm(B,D,d); clean totient normalization", .asraCorrected, .proved,
      .kernelProof⟩
  , ⟨"prime-slot truncation identity; upper-sieve majorization step", .asraCorrected, .proved,
      .kernelProof⟩
  , ⟨"Iwaniec/Maynard analytic upper sieve", .asraCorrected, .conditional, .externalInterface⟩
  , ⟨"large-overlap divisor decomposition", .asraCorrected, .proved, .kernelProof⟩
  , ⟨"large-overlap Shiu input", .asraCorrected, .conditional, .externalInterface⟩
  , ⟨"zero-mode density and centred kernel", .asraCorrected, .proved, .kernelProof⟩
  , ⟨"ratio-BV Zheng input", .asraCorrected, .conditional, .externalInterface⟩
  , ⟨"rational-root bilinear clearing (with base progression)", .asraCorrected, .proved,
      .kernelProof⟩
  , ⟨"ASRA_NonzeroFrequencyTransfer", .asraCorrected, .open, .researchRecord⟩
  , ⟨"ASRA_SignedSieveMainTerm", .asraCorrected, .open, .researchRecord⟩
  , ⟨"ASRA assembly implication (components ⟹ ASRA)", .asraCorrected, .conditional,
      .conditionalOnInterfaces⟩
  , ⟨"full ASRA", .asraCorrected, .open, .researchRecord⟩
  , ⟨"graph-selective occupancy + localization chain (edge supply)", .asraCorrected,
      .conditional, .conditionalOnInterfaces⟩
  , ⟨"eventual all-large exclusion", .asraCorrected, .conditional, .conditionalOnInterfaces⟩
  , ⟨"effective analytic threshold M_an", .asraCorrected, .open, .researchRecord⟩
  , ⟨"finite verification through M0-1", .asraCorrected, .open, .researchRecord⟩
  , ⟨"effective finite splice", .asraCorrected, .blocked, .researchRecord⟩
  , ⟨"historical finite endpoint ≈ 6.125×10^120", .asraCorrected, .historicalMetadata,
      .metadata⟩
  , ⟨"Erdős #287", .asraCorrected, .open, .researchRecord⟩ ]

/-- The complete V9 ledger. -/
def v9Ledger : List RowV8 := v8Ledger ++ v9New

set_option maxRecDepth 100000

/-- No V9 row is `CLOSED`. -/
theorem v9New_no_closed : ∀ r ∈ v9New, r.status ≠ .closed := by decide

/-- **No `CLOSED` row anywhere.** -/
theorem v9_no_closed : ∀ r ∈ v9Ledger, r.status ≠ .closed := by
  intro r hr
  rcases List.mem_append.1 hr with h | h
  · exact v8_no_closed r h
  · exact v9New_no_closed r h

/-- **Erdős #287 is listed only as `OPEN`** among the V9 rows (and never `CLOSED` anywhere). -/
theorem v9_erdos287_open :
    (∀ r ∈ v9New, r.name = "Erdős #287" → r.status = .open) ∧
    (∃ r ∈ v9New, r.name = "Erdős #287" ∧ r.status = .open) ∧
    (∀ r ∈ v9Ledger, r.status ≠ .closed) :=
  ⟨by decide, by decide, v9_no_closed⟩

/-- Research-record and external-interface rows are never `PROVED`. -/
theorem v9_record_external_not_proved :
    ∀ r ∈ v9New, (r.evidence = .researchRecord ∨ r.evidence = .externalInterface) →
      r.status ≠ .proved := by decide

/-- `PROVED` requires a kernel proof. -/
theorem v9_proved_implies_kernel :
    ∀ r ∈ v9New, r.status = .proved → r.evidence = .kernelProof := by decide

/-- **ASRA epochs**: the historical full-written-candidate row is `SUPERSEDED`, the current
full ASRA and its two open interfaces are `OPEN`. -/
theorem asra_epochs :
    (∃ r ∈ v9New, r.epoch = .asraFullWrittenCandidate ∧ r.status = .superseded) ∧
    (∃ r ∈ v9New, r.name = "full ASRA" ∧ r.epoch = .asraCorrected ∧ r.status = .open) ∧
    (∃ r ∈ v9New, r.name = "ASRA_NonzeroFrequencyTransfer" ∧ r.status = .open) ∧
    (∃ r ∈ v9New, r.name = "ASRA_SignedSieveMainTerm" ∧ r.status = .open) := by decide

/-- **Splice status**: effective finite splice `BLOCKED`, eventual exclusion `CONDITIONAL`. -/
theorem splice_blocked :
    (∃ r ∈ v9New, r.name = "effective finite splice" ∧ r.status = .blocked) ∧
    (∃ r ∈ v9New, r.name = "eventual all-large exclusion" ∧ r.status = .conditional) := by
  decide

/-! ## The closure DAG and the no-closing-path firewall -/

/-- A closure edge: all premises together yield the conclusion (schematic research DAG). -/
structure Edge where
  premises : List String
  conclusion : String
  deriving DecidableEq, Repr

/-- The recorded closure DAG of the direct-exclusion route. -/
def closureDAG : List Edge :=
  [ ⟨["ASRA_NonzeroFrequencyTransfer", "ASRA_SignedSieveMainTerm", "large-overlap Shiu input",
      "ratio-BV Zheng input", "CRT/collision/prime-slot algebra"], "full ASRA"⟩
  , ⟨["full ASRA", "graph-selective occupancy",
      "prescribed-shape gcd clique: box placement (union-bound argument)",
      "Maynard prime supply on the clique (PrimeValuesOnClique)"],
      "eventual all-large exclusion"⟩
  , ⟨["eventual all-large exclusion", "effective analytic threshold M_an",
      "finite verification through M0-1"], "effective finite splice"⟩
  , ⟨["effective finite splice"], "Erdős #287"⟩ ]

/-- The nodes of `v9New` with status `PROVED`. -/
def provedNodes : List String := (v9New.filter fun r => r.status = .proved).map (·.name)

/-- One propagation step. -/
def step (S : List String) : List String :=
  S ++ (closureDAG.filter fun e => e.premises.all fun p => p ∈ S).map (·.conclusion)

/-- `n` propagation steps from the proved nodes. -/
def derivable : ℕ → List String
  | 0 => provedNodes
  | n + 1 => step (derivable n)

/-- The proved set is already a fixpoint: no edge fires. -/
theorem step_provedNodes : step provedNodes = provedNodes := by decide

theorem derivable_eq (n : ℕ) : derivable n = provedNodes := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [derivable, ih, step_provedNodes]

/-- **No ledger path closes Erdős #287.** -/
theorem no_ledger_path_closes_erdos287 (n : ℕ) : "Erdős #287" ∉ derivable n := by
  rw [derivable_eq]; decide

/-- The open premise blocking each edge: every edge of the DAG has a non-`PROVED` premise. -/
theorem every_edge_has_open_premise :
    ∀ e ∈ closureDAG, ∃ p ∈ e.premises, p ∉ provedNodes := by decide

end Ledger
end ResearchBankV9
end Erdos287
