# Erdős #287 — September-2 two-lane master source / one-slot Perron / hard-`U` adapter frontier

**Append-only safe-bank round.**  No historical file was deleted or rewritten, no analytic
theorem was proved, no research socket was inhabited, and **Erdős #287 is not claimed**.
Twin Prime / HSTAR material is not imported and is not a dependency of anything added here.

## Files added

| file | content |
|---|---|
| `RequestProject/CurrentProgramme/Erdos287September2TaggedTwoLaneSource.lean` | §1–§2: the tagged two-lane source `RawIndex = ({tot} × TotDiscIndex) ⊎ ({u} × UDiscIndex)`; lane dichotomy, fibre disjointness, `Finset` census split, the equivalence with the plain disjoint union; the algebraic split identity for supplied lane weights; the recorded intended semantics (`tot ↦ T_X`, `u ↦ L_X`); the explicit witness that **source-tag disjointness is not physical `n`-support disjointness**; the selected-`E` **typing guard** (`TotDiscIndex` has no such field, so no constructor can attach the datum to a `Tot` row). |
| `RequestProject/CurrentProgramme/Erdos287September2OneSlotPerron.lean` | §4: the one-slot abscissa/height `c = X^{-200}`, `T = X^{200}`, `T/c = X^{400}`; the recorded **false** step `arsinh t < log 2t` (its negation is kernel-proved) and the repaired chain `arsinh t ≤ log(5t/2) < 401 log X` for `X ≥ 3`; hence `perronMassOne X < 128 log X`.  §5: `ε = 5·10⁻²²`, `γ = 1/2 − ε`, `⌈1/(1−γ)⌉ = 2`, `N = kℓ + r + s ≤ 112` (sharp), nonempty coordinate subsets `≤ 2^112 − 1`, and the record that this ceiling is not an effectivity closure. |
| `RequestProject/CurrentProgramme/Erdos287September2LedgerAdaptersAndCompilers.lean` | §6 the typed Perron/nuclear ledger socket (**uninhabited**; the contract is a genuine constraint and provably does *not* store the desired mass conclusion); §7 the hard-`U` → shared-Ford literal source-equality socket (**uninhabited**; component-wise consequences proved, and the selected-`E` clause shown load-bearing); §8 the direct-provider / b-diagonal bypass as a *conditional* implication with an unasserted antecedent; §9 the conditional `E_L` bound; §11 `C_pair = 11`; the generic four-loss positivity lemma, renamed `fourLossSurvivalPositivity` so that it cannot be mistaken for a sieve-survival bridge; and §11.1 the genuine `PrimePairSieve.primePairSieveSurvival45`, the elementary physical inclusion theorem over the banked window data (`Q = X/(2M)`, `I(M) ⊆ (Q,2Q]`, `H = |I(M) ∩ ℤ| ≤ Q+1`, `z = H^(49/100)`, long sector `H − 1 > H^(49/100)`), with the finite chains `q > Q ≥ H − 1 > z` and `2Mq + s ≥ 2Mq − 1 > q > z` and the consequence that a simultaneous-prime pair `(q, 2Mq+s)` has no prime factor below `z`; plus consistency of the window hypotheses and the firewall that surviving the `z`-sieve is not primality; §12 `2·X_N2 > 4·10⁹`; §13 the four-error algebraic interface and its budget-is-an-input firewall. |
| `RequestProject/Status/CurrentStatusErdos287September2TwoLaneMaster.lean` | §14: the strictly later authoritative status layer over 18 nodes, with the §0 vocabulary; firewalls (`paperClosedExternal ≠ kernelProved`, `sourcePinOpen ≠ kernelProved`, no row closes #287, open/conditional rows exist, Twin Prime is not a node), and five rows explicitly *backed* by the kernel theorems they label. |
| `RequestProject/Status/AxiomAuditErdos287September2TwoLaneMaster.lean` | §15: `#print axioms` on every principal declaration of the layer. |

`RequestProject/Main.lean` gained the five corresponding imports.

## Corrected step (audit finding)

The requested chain

```
asinh(X^400) < log(2 X^400) < 401 log X
```

has a **false first step**: `arsinh t = log(t + √(1+t²)) > log(2t)` for every `t > 0`, since
`√(1+t²) > t`.  This is recorded and kernel-proved as
`September2OneSlotPerron.arsinh_gt_log_two_mul`.  The chain is repaired with the constant
`5/2` in place of `2` (valid because `√(1+t²) ≤ (3/2)t` for `t ≥ 1`), which yields exactly the
intended conclusion `perronMassOne X < 128 log X` for `X ≥ 3` (using `401 < 128π`).

## STRICT OUTPUT

```
TWO-LANE TAGGED SOURCE:        KERNEL-PROVED
SELECTED-E TYPE FIREWALL:      KERNEL-PROVED
ONE-SLOT PERRON:               KERNEL-PROVED (chain repaired; false step recorded)
N<=112 ARITHMETIC:             KERNEL-PROVED
COMPLETE PERRON LEDGER:        UNINHABITED
E_T:                           PAPER_CLOSED_EXTERNAL
HARD-U SHARED-FORD ADAPTER:    UNINHABITED
E_L:                           CONDITIONAL / OPEN
b-DIAGONAL BYPASS:             CONDITIONAL (antecedent not asserted)
E_M:                           PAPER_CLOSED_EXTERNAL
N2 (Bordignon–Lee analytics):  PAPER_CLOSED_EXTERNAL
PRIME-PAIR-SIEVE-SURVIVAL45:   KERNEL-PROVED (elementary inclusion bridge only)
CURRENT N2 FINITE SPLICE:      FAIL (2·X_N2 > 4·10⁹ kernel-proved)
FOUR-ERROR ASYMPTOTIC FCL:     CONDITIONAL
GLOBAL EFFECTIVITY:            OPEN
ERDOS287:                      OPEN
TWIN/HSTAR CONTAMINATION:      NONE
SORRYAX:                       NONE
CUSTOM AXIOM:                  NONE
OVERCLAIM AUDIT:               PASS
```

Independent external checker / comparator: **NOT RUN** (not claimed).

STOP.
