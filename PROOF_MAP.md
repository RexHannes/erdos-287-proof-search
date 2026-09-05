# Erdős Problem #287 — Canonical Proof / Proof-Search Map

> **Global status: OPEN. No solution is claimed.**

This is the canonical dependency map for deciding **what is proved, what is merely candidate, what is currently worth attacking, and what should not be reopened**.

It deliberately separates two questions:

1. **evidence status** — kernel-proved, finite-certified, audited analytic, candidate, open;
2. **strategic status** — controlling, downstream, retired, superseded.

A theorem can be mathematically unresolved in an old coordinate system yet no longer be a required independent node after a source-exact reassembly. Conversely, “no longer controlling” never means “proved”.

## Status vocabulary

| Mark | Meaning |
|---|---|
| **BANKED** | trusted at a precisely stated evidence scope |
| **CANDIDATE** | substantial live result awaiting independent promotion |
| **OPEN** | genuine live missing theorem / estimate / instantiation |
| **SUPERSEDED** | old coordinate or compiler no longer independently controlling |
| **RETIRED** | route should not be reused as a controlling theorem |
| **FALSE** | explicit counterexample / contradiction / retraction |

Evidence class is recorded separately as `KERNEL-PROVED`, `FINITE-CERTIFIED`, `ANALYTICALLY-PROVED`, `AUDITED`, `CONDITIONAL`, or `CANDIDATE`.

---

# 1. Current source-minimal route

```text
                               ERDŐS #287
                                   |
                                   v
                         BANKED SOURCE / ALGEBRA
                                   |
             +---------------------+---------------------+
             |                     |                     |
             v                     v                     v
      B_src normalization     odd half-divisor      c=1 / c=2 splice
            BANKED                BANKED                BANKED
             |                     |                     |
             +---------------------+---------------------+
                                   |
                          full unselected parent
                                   |
                         Z(s,s)=0 at banked scope
                                   |
                                   v
                         AUDITED EFFECTIVITY BANK
                                   |
                   certified subtotal 5.257263872e-7
                   remaining capacity 3.603386128e-7
                                   |
                                   v
                          corrected selector Γ
                                   |
              +--------------------+-------------------+
              |                    |                   |
              v                    v                   v
           j >= 4                j = 3        j = 0 + j = 1 + active j=2
      CANDIDATE-EMPTY      CANDIDATE-CLOSED          CURRENT PARENT
                            |R_3| < 3e-9 B_X             OPEN
              |                    |                   |
              +--------------------+-------------------+
                                   |
                                   v
                                  R_012
                                   |
                 +-----------------+------------------+
                 |                 |                  |
                 v                 v                  v
        complete low fibres   incomplete fibres    active j=2
         exact cancellation        OPEN          source census reduced
                                                c=1: 71 prefixes
                                                c=2: 37 prefixes
                                   |
                                   +-- rough defect                         OPEN
                                   +-- selector-sensitive Perron/hyperbola OPEN
                                   +-- large ratio-frequency decay          OPEN
                                   |
                                   v
                            R_012 CLOSED ?
                                   |
                                   v
                              SIGNED FLOOR
                                  OPEN
                                   |
                                   v
                         MAYNARD EFFECTIVIZATION
                               NOT ENTERED
                                   |
                                   v
                        FINITE / ASYMPTOTIC SPLICE
                               NOT ENTERED
                                   |
                                   v
                               ERDŐS #287
                                  OPEN
```

The current hard theorem is therefore **not** “close medium-`k` independently”. It is the source-exact signed `R_012` parent, whose live analytic content is concentrated in incomplete fibres, rough defect, selector-sensitive Perron/hyperbola terms, and large ratio-frequency decay.

The current-parent detail lives at [`frontier/current-parent/`](frontier/current-parent/).

---

# 2. What is genuinely banked

The following foundation is retained without being compressed away:

- physical `B_src` normalization, including the single-global-singular-series-factor firewall;
- corrected odd half-divisor algebra and its parity boundary;
- the `c=1/c=2` reflection/splice;
- full unselected `Z(s,s)=0` at the exact formal/analytic scope recorded in the audited bank;
- Perron variable-change algebra and secondary-pole bookkeeping, distinct from the directed truncation estimate;
- `V<1000` finite closure;
- complete-period endpoint/Farey covariance main;
- exact all-`q` identities and other transformations where banked at their stated scope;
- the audited R12 capacity ledger.

Evidence is indexed by class under [`banked/`](banked/). The canonical detailed audited baseline remains the R12 release at [`paper/audited-release/2026-09-05-r12/`](paper/audited-release/2026-09-05-r12/).

---

# 3. R12 versus the newer proof-search reassembly

R12 remains the latest independently audited numerical/effectivity baseline. In R12 coordinates the controlling sufficient residual was

```text
C_F + 2 C_ED + C_DD + C_S < 283/37500,
```

with medium-`k` still strictly reduced/open.

Later source work showed that several such objects are better understood as **different coordinate charts of one signed triangular physical parent**. The live proof search therefore does not require `F`, `ED`, `DD`, `S`, all-`q`, medium-`k`, and two-high to be closed one after another as independent gates.

This is a **dependency recompile**, not a retrospective claim that the R12 residual theorem was separately proved. R12 remains valid as an audited checkpoint and quantitative baseline.

---

# 4. Selector diagonal zero: what changed and what did not

For the full unselected parent, the banked diagonal identity remains

```text
Z(s,s)=0.
```

For the active selector `Theta`, the live source develops the defect

```text
Z_{Theta,c}(s,s) = -H_c(s).
```

A candidate auxiliary completion

```text
Ztilde_c = Z_{Theta,c} + H_c
```

restores

```text
Ztilde_c(s,s)=0,
```

with a reported finite-height auxiliary correction `<2.4e-13 B_X`.

That repairs the diagonal zero only. It **does not** close the large ratio-frequency / incomplete-fibre signed estimate. Until independently audited, this selected completion remains in [`frontier/candidate-results/`](frontier/candidate-results/).

---

# 5. Superseded as independent frontiers

The following should not be treated as mandatory standalone next theorems:

```text
F / ED / DD / S separately
all-q discrepancy separately
moving Ramanujan window
static r>200 tail as the top-level controlling coordinate
medium-k as an independent sequential gate
medium-k -> two-high sequential DAG
```

Their mathematics has not vanished. It has been reassembled into, or remains diagnostically useful for, the signed parent. See [`graveyard/superseded/`](graveyard/superseded/).

The old static-Ramanujan candidate snapshot is preserved at [`frontier/2026-09-05-static-ramanujan/`](frontier/2026-09-05-static-ramanujan/) for research archaeology but is no longer the canonical frontier.

---

# 6. False / retired routes

Two distinctions are mandatory:

- **FALSE** means an actual counterexample or retraction;
- **RETIRED** means “do not use as the controlling route”, which need not imply falsity.

Examples include the false uniform unweighted `C_joint<=0.09`, the retracted deleted-gap `a<=180` claim from the latest route audit, and several source-mismatched or overstrong compilers. See [`graveyard/`](graveyard/) and [`CORRECTIONS_AND_RETRACTIONS.md`](CORRECTIONS_AND_RETRACTIONS.md).

---

# 7. Repository reading order

For any future human or model doing proof search:

```text
README.md
   -> PROOF_MAP.md
   -> CURRENT_STATUS.md / CLAIMS_LEDGER.md
   -> banked/      (what can be consumed)
   -> frontier/    (what should be attacked)
   -> graveyard/   (what should not be reopened)
   -> archive/     (full historical provenance)
```

The technical source stores `RequestProject/`, `paper/`, `certificates/`, `reviews/`, and `scripts/` remain in place for reproducibility. They are evidence backends, not competing proof ontologies.

**ERDŐS PROBLEM #287 REMAINS OPEN.**
