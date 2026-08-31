# ERDŐS #287 — V22 SOURCE-FORENSICS SAFE BANK REPORT

`BALANCED7-OMEGA-FM723-SOURCE-ADAPTER45` / `BADCHAR-D2-RELEDGER45`

Append-only continuation of V20 + V21.  Nothing earlier was deleted, rewritten or silently
mutated; `ARISTOTLE_SUMMARY.md` was not modified.

---

## A. Baseline

V21 head, `lake build` clean.  V21 left three source pins open, in this order:

1. `BALANCED7-PRIMEBOX-L1-NORMALIZATION45` — no physical `ω_i(p)` in the repository;
2. `3221-HIGHPROJECTOR-CUTOFF-COMPAT45`;
3. `3221-PHYSICAL-LOG-PREFAC45`.

V22 attacks (1) and the log arithmetic that the safe bad-character repair invalidated.

---

## B. The safe bad-character log re-ledger

File: `RequestProject/Erdos287/BadCharacterLogLedger3221.lean` (namespace
`Erdos287.V22Ledger`).

The V21 repair replaced the heuristic `#Bad ≪ D·τ(q)` by the proved finite bound
`#Bad ≤ (D+1)²` — **two** powers of the cutoff.  Any compiler whose log arithmetic assumed
one power of `D` is therefore wrong, and V22 re-ledgers it with the cutoff exponent kept
abstract, `D = (log X)^{B0}`:

```
2·AA exponent       = 10
2·BB exponent       = 20 − 8 B0
2·BA (= AB) exponent = 15 − 4 B0
2·C_var(B0)         = min(10, 15 − 4B0, 20 − 8B0)
```

Declarations: `cutoffOfB0`, `cutoffOfB0_eq_sharedCutoff` (it *is* the V21 shared cutoff),
`aaDoubledExponent`, `bb_logExponent`, `ba_logExponent`,
`highProjectorVarianceLogExponent`, `cvar`, `cvar_doubled`, `cvar_le_channels`.

Kernel-checked samples: `cvar_at_one : C_var(1) = 5`, `cvar_at_two : C_var(2) = 2`,
`cvar_at_three : C_var(3) = −2`, and `cvar_decreasing_sample`.  In particular the budget
is genuinely `B0`-dependent and goes **negative** at `B0 = 3`.  `B0 < 5` is nowhere
hard-coded.

---

## C. The Ford-(7.23) candidate source adapter

File: `RequestProject/Erdos287/Ford723BalancedSevenAdapter3221.lean` (namespace
`Erdos287.V22Ford`).

`Ford723CoefficientData` is pure data; `BalancedSevenOmegaFord723Adapter3221` is the
transcription obligation identifying the physical slot `ω_i` with a Ford coefficient,
supplying prime support and the pointwise law `|ω_i(p)| ≤ 1`.  It is a `structure`, not an
axiom, and **uninhabited** (`ford723Adapter_not_automatic`).  Only the transfer lemmas are
proved: `ford723Adapter_transfers_prime_support`, `ford723Adapter_transfers_pointwise`.

**Provenance note.**  The later SP-2 forensics pass concluded that the Ford-(7.23) family
is *not* the literal Balanced7 source and retracted this adapter as controlling.  The file
is preserved; the retraction is machine status data in `Erdos287.SP2Status`.

---

## D. Prime-box `L¹` normalization

File: `RequestProject/Erdos287/PrimeBoxL1Normalization3221.lean` (namespace
`Erdos287.V22PrimeBoxL1`).

Three ingredients, kept apart:

* **(A)** source dictionary — uninhabited;
* **(B)** `PrimeBoxCardinality3221Input` (`#box_i ≤ C₁ Y/log Y`) — external prime counting,
  uninhabited (`primeBoxCardinality_not_automatic`);
* **(C)** the formal compiler `V21PrimeBox.primeBoxL1_of_pointwise_and_count` — proved.

`primeBoxL1_of_ford723Adapter : (A) + (B) ⇒ BalancedSevenPrimeBoxNormalization3221 Dat 1 C1 Y`
— the pointwise constant is exactly `1`, so the `L¹` constant is the prime-counting
constant itself.

Anti-circularity: `primeBoxL1_compiler_cannot_construct_cardinality`,
`primeBoxL1_not_automatic_v22`.

Status: `BALANCED7-PRIMEBOX-L1-NORMALIZATION45` remains **SOURCE_OPEN**.

---

## E. The physical closure criterion

File: `RequestProject/Erdos287/TwoProjectorPhysicalClosure3221.lean` (namespace
`Erdos287.V22Closure`).

```
netLogExponent C_var C_ext = −(2 + C_var)/2 + C_ext
netLogExponent < −1  ⟺  C_var > 2 C_ext          (netLogExponent_lt_neg_one_iff)
```

Capacity of the *repaired* ledger, proved sample by sample:

| `B0` | `C_var` | closes iff |
|---|---|---|
| 1 | 5 | `2 C_ext < 5` (`closure_capacity_B0_one`) |
| 2 | 2 | `C_ext < 1` (`closure_capacity_B0_two`) |
| 3 | −2 | never, for `C_ext ≥ 0` (`closure_fails_B0_three`) |

`TwoProjectorPhysical3221Inputs` bundles the source dictionary, the prime count, the sieve
and Shiu interfaces, the outer `L²` input, the shared-cutoff firewall, the ledger
inequality and the V21 numeric budget layer.  `twoProjectorPhysical3221_closes_logVar`
concludes the log-variance interface **and** the strict closure inequality; it has no
inhabitant.  `physicalClosure_cannot_construct_comparison` keeps comparison independent.

---

## F. Machine status

`RequestProject/Status/Erdos287V22Status.lean` — kernel-decidable ledger with
`badCharacter_d2_reledger_finite_pass`, `ford723_adapter_is_candidate_only`,
`first_exact_residual_v22`, `comparison_still_not_first_residual_v22`,
`terminal_nodes_open_v22`, `external_interfaces_uninhabited_v22`.

`RequestProject/Status/AxiomAuditErdos287V22.lean` — `#print axioms` for all 36 principal
V22 declarations; all report exactly `[propext, Classical.choice, Quot.sound]`.

---

## REQUIRED FINAL BLOCK

```
FILES ADDED:
RequestProject/Erdos287/BadCharacterLogLedger3221.lean
RequestProject/Erdos287/Ford723BalancedSevenAdapter3221.lean
RequestProject/Erdos287/PrimeBoxL1Normalization3221.lean
RequestProject/Erdos287/TwoProjectorPhysicalClosure3221.lean
RequestProject/Status/Erdos287V22Status.lean
RequestProject/Status/AxiomAuditErdos287V22.lean
ERDOS287_V22_SOURCE_FORENSICS_SAFE_BANK_REPORT.md

FILES MODIFIED:
RequestProject/Main.lean   (import lines appended only)

V20 / V21 PRESERVED:
YES

SAFE BAD-CHARACTER LOG LEDGER:
FINITE PASS — C_var(B0) = min(5, 15/2 − 2B0, 10 − 4B0); C_var(1)=5, C_var(2)=2, C_var(3)=−2

FM723 SOURCE ADAPTER:
CANDIDATE / UNINHABITED  (retracted as controlling by the later SP-2 pass; file preserved)

PRIMEBOX CARDINALITY INPUT:
EXTERNAL ANALYTIC INTERFACE / UNINHABITED

PRIMEBOX L1 NORMALIZATION:
SOURCE_OPEN — conditional compiler only

CUTOFF COMPATIBILITY:
SOURCE_OPEN

PHYSICAL LOG PREFACTOR:
SOURCE_OPEN

TWO-PROJECTOR PHYSICAL CLOSURE:
CONDITIONAL / UNINHABITED

3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45:
OPEN / CONDITIONAL

SIXTH MOMENT:
OPEN STRONGER SUFFICIENT FALLBACK

COMPARISON:
SOURCE_OPEN

BALANCED7:
OPEN

ERDOS287:
OPEN

FIRST EXACT RESIDUAL:
BALANCED7-PRIMEBOX-L1-NORMALIZATION45 : SOURCE_OPEN

LAKE BUILD:
SUCCESS — 0 errors; V22 modules emit 0 warnings

TRUST SCAN:
ZERO occurrences of sorry / admit / axiom / opaque / unsafe / native_decide /
@[implemented_by] in all new V22 files

PUBLIC-MAIN SYNC:
RequestProject/Main.lean extended with the V22 imports only
```

### FINAL FIREWALL

```
No source-open or external analytic interface was inhabited merely to make
the compiler execute.

No statement in V22 proves Erdős #287.

No statement in V22 proves Balanced7.
```
