# Erdős #287 — Research Bank V13 report (finite interval certificate + updated splice)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 remains OPEN.**

The historical V11 finite-architecture status is preserved rather than rewritten.

The new finite interval certificate is a distinct finite-exclusion route.

A generic Lean-verified certificate checker is not the same as replaying the actual 1,274-record certificate payload.

No numerical M_an is currently available.

The decisive splice condition is M_an <= U + 1.

Erdős #287 remains OPEN.

---

## 0. Headline status

* **ConcreteFinitePayload = NOT SUPPLIED.**  The workspace (and the whole filesystem) was searched
  for `certificate.json`, `endpoint.txt`, `VERIFICATION.txt` and any finite-audit-extension
  package; none is present.  Hence **no** `auditedFiniteEndpoint` is defined and **no** Lean theorem
  about `10^500` is claimed.  The audited report's claims (all `M ≤ 10^500` excluded; endpoint
  `≈ 5.2096050287860520666 · 10^500`; 1,274 records) are kept only as external metadata strings
  (`AuditedEndpoint.auditedReportMetadata`).
* **Generic certificate format is Lean-proved sound** (`FiniteIntervalCertificate.sound`,
  `checkChain_sound`).
* **The actual 10^500 payload has NOT been replayed by Lean.**
* Formal finite theorem architecture = AVAILABLE; actual 10^500 payload = EXTERNALLY AUDITED BUT
  NOT LEAN-REPLAYED (`EffectiveFrontier.finiteSideStatus`, `finiteSide_not_blurred`).
* Additional (not requested, clearly separated): `DemonstrationPayload.lean` contains a **small
  117-record payload generated in this run** (Family A/B records with Proth + Pocklington
  witnesses) which the Lean kernel checks with ordinary `decide` (no `native_decide`).  It yields
  the unconditional theorem `demo_noCounterexampleUpTo : NoCounterexampleUpTo demoEndpoint` with
  `demoEndpoint ≈ 2.45 · 10^60` (`demoEndpoint_lt : demoEndpoint < 10^61`).  **This is not the
  audited payload** and says nothing about `10^500`; it only demonstrates that the checker runs end
  to end in the kernel.  It starts from the project's already banked unconditional range
  `M ≤ 4·10^9` (`noCounterexampleUpTo_4e9`).
* `current_M_an = none`; the current global splice is **blocked**, now for the reason
  "explicit analytic activation threshold unavailable".

## 1. Files (append-only)

All new; no pre-existing file modified; `ARISTOTLE_SUMMARY.md` not edited.

* `RequestProject/Erdos287/ResearchBankV13.lean` (aggregator)
* `RequestProject/Erdos287/ResearchBankV13/`
  `FiniteRepresentationModel`, `PrimeLayer`, `HarmonicTwoHole`, `AdjacentPrimeLayer`,
  `PrimeCertificates`, `FiniteIntervalCertificate`, `DemonstrationPayload` (extra),
  `AuditedEndpoint`, `UpdatedSplice`, `EffectiveFrontier`, `Ledger`, `AxiomAudit` (`.lean`)

Namespaces `Erdos287.ResearchBankV13.<File>`, except that `FiniteIntervalCertificate.lean` uses
namespace `Erdos287.ResearchBankV13.IntervalCertificate` (so that the structure
`FiniteIntervalCertificate` does not clash with the namespace name).

## 2. Principal theorems

### §18 `FiniteRepresentationModel`
Uses the project's exact type `Erdos287Counterexample A` (integers `> 1`, reciprocal sum 1,
consecutive gaps `≤ 2`, endpoint `M = max A`) — no change of convention.
`NoCounterexampleAt M`, `NoCounterexampleUpTo U`, `noCounterexampleUpTo_iff_finiteVerified`
(= V9 `FiniteVerifiedThrough`), `noCounterexample_all_iff` (`∀ M, NoCounterexampleAt M` is exactly
the full statement), `NoCounterexampleUpTo.mono`, `noCounterexampleUpTo_4e9`.

### §19 `PrimeLayer`
`L J = lcm(1..J)`, `A J = ∑_{j ≤ J} L J / j`.  **`primeLayer_exclusion`**: if `r` is prime,
`max A < (J+1) r` and `A J < r`, no element of a counterexample is divisible by `r` (proved in the
rational model via `r`-adic valuation, following the requested skeleton: `r_multiples`,
`coprime_L`, `num_le_A`, `C_le_A`).  Values: `L_2 = 2`, `A_2 = 3`, `L_5 = 60`, `A_5 = 137`,
`L_10 = 2520`, `A_10 = 7381` (kernel `decide`).

### §20 `HarmonicTwoHole`
`eta = 685/252`; **`eta_lt_exp`** (`685/252 < exp 1`, from Mathlib's `Real.exp_one_gt_d9`),
`log_eta_lt_one`, `harmonic_tail_le_log` (`∑_{n=H+1}^{M} 1/n ≤ log(M/H)`), `etaFloor`,
**`cannot_cross_two_holes`**, **`two_hole_exclusion`** (adjacent forbidden `h, h+1`,
`h ≤ M ≤ ⌊η (h+1)⌋` ⇒ contradiction), **`interval_exclusion_of_adjacent_holes`** (generic interval
theorem).  The literal log argument is used; the final interval theorem is not weakened.

### §21 `AdjacentPrimeLayer`
**`familyA_interval`** (`p = 2q+1`, both prime, `q > 137`: every `M ∈ [p−1, ⌊(685/252)p⌋]` is
excluded; hole `p−1 = 2q` via the `q`-layer with `J = 5` (`A 5 = 137 < q`, `M < 6q`), hole `p` via
the `p`-layer with `J = 2`), **`familyB_interval`**
(`p = 4q+1`, `q > 7381`; `J = 10` for `q`, `J = 2` for `p`), **`familyB_outside_goodPrimeHalf`**
(for `q > 3`: `(p−1)/2 = 2q` is composite and `3 ∣ (p+1)/2 = 2q+1 > 3`), `familyA_instance`.

### §23 `PrimeCertificates`
Mathlib has Lucas/Pocklington-style results only for specific forms and no ready witness checker,
so generic soundness lemmas were proved directly:
**`proth_sound`** (`q = u·2ⁿ+1`, `0 < u < 2ⁿ`, `a^((q−1)/2) ≡ −1 (mod q)` ⇒ `q` prime; `u` odd is
not needed), **`pocklington_sound`** (`q` prime, `p = c q + 1`, `c ≥ 1` (covers `c ∈ {2,4}`),
`p < q²`, `b^(p−1) ≡ 1`, `gcd(b^c − 1, p) = 1` ⇒ `p` prime), Boolean checkers `prothCheck`,
`pocklingtonCheck` with `prothCheck_sound`, `pocklingtonCheck_sound` (binary modular exponentiation
`Pratt.powMod` from the project's Pratt engine, proved correct, evaluated by the kernel; the Proth
checker also enforces `u` odd as part of the format), fixtures `prime_13/97/173/347`,
`malformed_proth_rejected`, `malformed_pocklington_rejected`, `familyA_from_certificates`.
No `native_decide`, no `bv_decide`, no probable-prime routine, no primality axiom.

### §22 `FiniteIntervalCertificate` (namespace `IntervalCertificate`)
`FiniteIntervalStep` (`lower`, `upper`, `proofExcluded`), `Chain` (contiguity),
`FiniteIntervalCertificate` (`first`, `last`, `steps`, `contiguous`, `initialCoverage`,
`finalEndpoint`), **`FiniteIntervalCertificate.sound`** (`NoCounterexampleUpTo C.last`).
Data level: `IntervalRecord`, `IntervalRecord.check`, `IntervalRecord.sound`, `checkChain`,
**`checkChain_sound`**, `noCounterexampleUpTo_of_records`, `certificateOfRecords`.
Fixture 10: `noncontiguous_rejected`, `checkChain_rejects_gap`.

### §24–25 `AuditedEndpoint`
`concreteFinitePayload = .notSupplied`, `ExternalAuditRecord`, `auditedReportMetadata`,
`externalRecord_not_theorem` (firewall e), `checker_is_not_payload_replay` (firewall f),
`bankLeanReplayedEndpoint = demoEndpoint` with `bankLeanReplayedEndpoint_sound`.

### §26 `UpdatedSplice`
**`finite_eventual_splice`**: `(∀ M ≤ U, P M) → (∀ M ≥ M_an, P M) → M_an ≤ U + 1 → ∀ M, P M`.
`erdos287_of_splice`, `splice_exact_boundary` (`M_an = U+1` closes), `splice_gap_fixture`
(`M_an = U+2` leaves exactly `U+1` uncovered), `finite_certificate_not_eventual` (firewall c),
`eventual_without_threshold_does_not_splice` (firewall d), `OldFiniteArchitectureProvider`,
`certificate_does_not_instantiate_architecture`, `routes_have_different_shapes`, `SpliceInputV13`,
`spliceInputV13_sound`, `missing_M_an_blocks_splice`.

### §27–28 `EffectiveFrontier`
`current_M_an_none`, `effectiveOverlap U M_an := M_an ≤ U + 1`,
**`splice_closes_of_future_constants`** (a future `NumericalExternalConstants` instance producing
`M_an` with `effectiveOverlap U M_an` closes the splice; no instance is created),
`overlap_needed`, `v11BlockReasons` / `v13BlockReasons`, `v11_reasons_preserved`,
`v13_reason_updated`, `v13_reason_justified`, **`current_global_splice_blocked`**,
`finiteSideStatus`, `finiteSide_not_blurred`, `overlap_test_pending`.

### Ledger
**`v13_preserves_v12_ledger`**, `v11_finite_architecture_history_preserved_v13`,
`v13_status_ledger`, `v13New_no_closed`, `v13_leanBank_implies_kernel`, `v13_payload_not_kernel`,
`no_ledger_path_closes_erdos287_v13`, **`all_regression_fixtures`** (bundles fixtures 1–10 of §31).

## 3. Status ledger (V13)

| item | status |
|---|---|
| concrete repaired Type-II/HB geometry | LEAN BANK |
| analytic spectral / SW / BV inputs | EXTERNAL PROVIDERS |
| conditional asymptotic composition | LEAN COMPOSITION FROM PROVIDERS |
| generic finite interval certificate theorem | LEAN BANK |
| concrete 10^500 payload | EXTERNAL AUDITED CERTIFICATE (not imported, not replayed) |
| demonstration payload to `≈ 2.45·10^60` (extra) | LEAN BANK |
| explicit `M_an` | NONE |
| overlap test | PENDING M_an |
| Erdős #287 | OPEN |

No theorem combines "a finite certificate exists" with "an eventual theorem exists" without the
hypothesis `M_an ≤ U + 1`.

## 4. Semantic firewalls (§30)

(a) `spectralProvider_not_automatic` (V12); (b) `composition_does_not_construct_constants` (V12);
(c) `finite_certificate_not_eventual`; (d) `eventual_without_threshold_does_not_splice`,
`missing_M_an_blocks_splice`; (e) `externalRecord_not_theorem`; (f) `checker_is_not_payload_replay`.

## 5. Regression fixtures (§31)

1 `endpointOnlyHBArgument_false`; 2 `old_count_fails_concrete`; 3 `lowH_without_prefactor_fails`;
4 `wf_truncation_firewall`; 5 `missing_M_an_blocks_splice`; 6 `splice_gap_fixture`;
7 `splice_exact_boundary`; 8 `malformed_proth_rejected`; 9 `malformed_pocklington_rejected`;
10 `noncontiguous_rejected`.  All bundled in `Ledger.all_regression_fixtures`.

## 6. Build, axioms, external checker

### Build (§34)

| command | result |
|---|---|
| `lake build RequestProject.Erdos287.ResearchBankV12` (+ `.AxiomAudit`) | success, **8201 jobs**, exit 0, 0 errors; 9 warnings, all in pre-existing files (`AnchoredV2/CapacityCertificate`, `AnchoredV3/ConditionalClosure`, `Window`, `ResearchBankV7/Numerics`), 0 in V12/V13 |
| `lake build RequestProject.Erdos287.ResearchBankV13` (+ `.AxiomAudit`) | success, **8223 jobs**, exit 0, 0 errors; the same 9 historical warnings, 0 in V12/V13 |
| `lake build` (full) | success, **8709 jobs**, exit 0; 26 warnings, all in pre-existing files (`CurrentProgramme/Erdos287September3TotFixedResidueArithmetic`, `AnchoredV2/CapacityCertificate`, `AnchoredV3/ConditionalClosure`, `CeilingCRT`, `CurrentStatusLatest`, `Reflection`, `ResearchBankV7/Numerics`, `RoughPrime`, `Window`, `TrustedBank/Erdos287/GoodPrime`), 0 in V12/V13 |

`git diff --name-status` against the pre-V12 commit lists 30 files, all `A` (added); no existing
file is modified.

### Axiom audit (§32)

* V12 `AxiomAudit.lean`: `#print axioms` for all **126** V12 theorems.
* V13 `AxiomAudit.lean`: `#print axioms` for all **92** V13 theorems.
* Union of reported axioms over both: `{propext, Classical.choice, Quot.sound}` (many theorems use a
  proper subset or none).  No `sorryAx`, no `Lean.ofReduceBool`, no `Lean.trustCompiler`, no native
  evaluation axiom, no custom axiom.
* Token scan of all new files for `sorry, admit, axiom, unsafe, native_decide, bv_decide, opaque,
  implemented_by, debug.skipKernelTC`: hits only in comments/docstrings (statements that these are
  *not* used) and in the `#print axioms` commands.  Only ordinary kernel `decide` is used (on the
  ledger lists, small constants such as `A 10 = 7381`, the prime fixtures, and the 117-record
  demonstration payload).  No 500-digit number is certified by any computation.

### External checker (§33)

| command | exit | output | wall time |
|---|---|---|---|
| `lake env leanchecker RequestProject.Erdos287.ResearchBankV12` | 0 | none | 2m30s |
| `lake env leanchecker RequestProject.Erdos287.ResearchBankV13` | 0 | none | 2m15s |
| `lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV13` | 0 | none | 34m18s |

