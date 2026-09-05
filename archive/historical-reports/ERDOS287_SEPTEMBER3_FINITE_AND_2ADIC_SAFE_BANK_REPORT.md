# ERDŐS #287 — SEPTEMBER-3 SAFE BANK REPORT
## Finite-chain kernel replay / 2-adic Möbius pairing / odd-`d` + `4d` fixed residue /
## conditional Tot-lane AP compiler

**Append-only.**  No existing `RequestProject` theorem, status row, or report was deleted,
rewritten, weakened, or reinterpreted.  No new analytic prime-distribution theorem is
asserted anywhere.  Maynard Theorem 1.1, Bombieri–Vinogradov, Wright and Bordignon–Lee are
**not** asserted, and are not represented even as fields — the only analytic input is an
external hypothesis socket for which this development constructs **no inhabitant**.
Erdős #287 is **not** claimed; it stays `open`.

---

## 1. Files added

| file | content |
|---|---|
| `RequestProject/CurrentProgramme/Erdos287September3PrattEngine.lean` | kernel-checkable recursive (Pratt/Lucas) primality certificates: the fuel-driven binary modular exponentiation `powMod` with its **proved** correctness theorem `powMod_eq`, and `prime_of_certificate` |
| `RequestProject/CurrentProgramme/Erdos287September3PrattCertificateBank.lean` | 72 leaf primes (`norm_num` trial division, all `< 10^9`) and **52 recursive Pratt certificates**, bottom-up, for every prime used by the new windows (largest: `33554428169375797`) |
| `RequestProject/CurrentProgramme/Erdos287September3FiniteExtension24Window.lean` | the **24 new window certificates** and the extended finite bank up to `67108856338751594` |
| `RequestProject/CurrentProgramme/Erdos287September3TotTwoAdicMobiusPairing.lean` | the 2-adic Möbius pair coefficient, the exact odd-divisor Tot source identity, the split `T = T⁰ − T²`, the termwise-triangle loss witness |
| `RequestProject/CurrentProgramme/Erdos287September3TotFixedResidueArithmetic.lean` | family-0 (`modulus d`) and family-2 (`modulus 4d`) fixed-residue congruences and the converse integrality statement |
| `RequestProject/CurrentProgramme/Erdos287September3TotFixedResidueConditionalCompiler.lean` | the physical slot algebra, the **uninhabited** external AP socket, and the conditional `E_T` compiler |
| `RequestProject/CurrentProgramme/Erdos287September3CanonicalSplitFourInterval.lean` | (optional Priority C) abstract monotone crossing lemma, two thresholds per window, ≤ 4 interval indicators, exact `ν = 1/2` numerical instance |
| `RequestProject/Status/CurrentStatusErdos287September3SourceBank.lean` | append-only status layer with firewalls and row-backing theorems |
| `RequestProject/Status/AxiomAuditErdos287September3SourceBank.lean` | `#print axioms` on every principal new declaration |
| `scripts/search_windows.py`, `scripts/gen_certs.py`, `scripts/gen_lean.py` | the (untrusted) generators that produced the window and certificate data; they produce Lean text only — nothing they compute is trusted, every statement is re-proved by the Lean kernel |

`RequestProject/Main.lean` gained the nine new imports (append-only, at the end of the
import block).

---

## 2. Declarations added (principal)

**Certificate engine** — `Erdos287.Pratt`:
`powMod`, `powMod_eq`, `prodPow`, `AllPrimeFst`, `AllWitness`, `allPrimeFst_of_mem`,
`allWitness_of_mem`, `exists_mem_of_prime_dvd`, `natCast_pow_eq_one_iff`,
`prime_of_certificate`.

**Certificate bank** — `Erdos287.Certificates`: 72 leaf primality theorems `prime_<p>` and
52 Pratt-certified `prime_<p>`.

**Finite extension** — `Erdos287`:
`extendedCeiling`, `Gap2CE.windowStepExt_0 … windowStepExt_23`,
`Gap2CE.no_of_M_le_extendedCeiling`,
`no_Erdos287Counterexample_of_max_le_extendedCeiling`,
`no_Erdos287Counterexample_of_max_le_extendedCeiling'`,
`arithmeticCoverage_exceeds_twoExp375`.

**2-adic pairing** — `Erdos287.September3TwoAdicPairing`:
`moebius_two_mul_odd`, `odd_of_all_prime_factors_gt_two`, `odd_mul_of_odd_odd`, `kappaEps`,
`sigmaEps`, `sigmaEps_odd`, `twoAdicMobiusPairCoefficient`, `oddDivisorTotSourceIdentity`,
`oddDivisorTotSourceIdentity_filtered`, `totSource`, `totSourceFamily0`, `totSourceFamily2`,
`totLaneSourceSplit`, `termwise_triangle_loses_pairing`.

**Fixed-residue arithmetic** — `Erdos287.September3FixedResidue`:
`family0_fixedResidue`, `family0_fixedResidue_pm`, `isCoprime_two_of_odd`,
`family0_integrality`, `family0_integrality_witness`, `family2_fixedResidue`,
`family2_fixedResidue_pm`, `fixedResidueFamilies_replace_generic_modulus`.

**Conditional compiler** — `Erdos287.September3ConditionalCompiler`:
`Slot`, `Slot.modulus`, `Slot.residue`, `PhysicalSlotFamily`, `PhysicalSlotFamily.slotOf`,
`PhysicalSlotFamily.slotIndex`, `PhysicalSlotFamily.slotIndex_card`,
`PhysicalSlotFamily.slotIndex_fiber_card`, `PhysicalFixedResidueAPBound` (socket),
`familySign`, `abs_familySign`, `E_T`, `totLaneFixedResidueConditionalBound45`,
`totLaneFixedResidueConditionalBound45_factored`.

**Canonical split** — `Erdos287.September3CanonicalSplit`:
`exists_threshold_of_monotone`, `monotone_rpow`, `canonicalSplit_two_thresholds`,
`splitCoeff`, `canonicalSplitFourInterval`, `canonicalSplit_upward_closed`,
`crossing_at_half_exponent`.

**Status layer** — `Erdos287.September3SourceBankStatus`: `Status`, `Node`, `status`,
`socket_is_not_kernelProved`, `finiteCoverage_does_not_close_medium_branch`,
`conditionalCompiler_does_not_prove_erdos287`, `maynard_is_not_asserted`,
`eT_and_eL_remain_conditional`, and five `row_*_backed` theorems.

---

## 3. Exact source statements formalised

**(a) Finite extension.**  Semantically identical to the pre-existing finite-bank theorem
(`Erdos287.Gap2CE.no_of_M_le_4e9`, `Erdos287.no_Erdos287Counterexample_of_max_le_4e9`),
with the ceiling extended:

```
Gap2CE.no_of_M_le_extendedCeiling :
  ∀ (ce : Gap2CE), 3 ≤ ce.M → ce.M ≤ 67108856338751594 → False

no_Erdos287Counterexample_of_max_le_extendedCeiling :
  Erdos287Counterexample A → A.max' _ ≤ 67108856338751594 → False

arithmeticCoverage_exceeds_twoExp375 : 38643198608805673 < extendedCeiling
```

The same `Gap2CE` / `Erdos287Counterexample` predicates and the same interval blocker
`Gap2CE.blocker_window` are used; only the certificate data is new.  This is **not** a
different arithmetic statement with a similar endpoint.

**(b) 2-adic Möbius pairing.**  `μ(2a) = −μ(a)` for odd `a`; the canonical coefficients
`kappaEps w d = μ(d)·w(d)` and `sigmaEps w m = μ(m)·w(oddPart m)` satisfy the two explicit
pairing equations; and, with `Y` the supplied split datum for `n^γ`,

```
∑_{m ∣ n, m ≤ Y, 4 ∤ m} σ(m)
  = ∑_{d ∣ n, d odd} κ(d) · ( 1_{d ≤ Y} − 1_{2d ∣ n} · 1_{2d ≤ Y} )
```

with the indicators written as Lean `if _ then 1 else 0` inside Finset-filtered sums.  The
two pairing equations are **explicit hypotheses** of the theorem (and proved for the
canonical coefficient) — nothing load-bearing is hidden inside an unconstrained structure.

**(c) Split identity.**  `totSource = totSourceFamily0 − totSourceFamily2`, with
family 0 = `{d odd, d ∣ n, d ≤ Y n}` and family 2 = `{d odd, 2d ∣ n, 2d ≤ Y n}`, for
supplied physical weights; no absolute value occurs in the identity.  A separate algebraic
witness (`termwise_triangle_loses_pairing`) exhibits an instance where the paired sum is `0`
while the termwise absolute sum is `2`.

**(d) Fixed-residue arithmetic.**
`(2dr + s) ≡ s [ZMOD d]`; `(4du + s) ≡ s [ZMOD 4d]`; and, under `p` odd, `d` odd, `s = ±1`,
`p ≡ s [ZMOD d] → 2d ∣ p − s` (equivalently `∃ u, p = 2du + s`).  Parity hypotheses are not
weakened.

**(e) Conditional compiler.**
`PhysicalFixedResidueAPBound F → |E_T F w A| ≤ ∑_{slots} |w d| · err(slot)`, with slot index
`D ×ˢ {1,4} ×ˢ {−1,+1}` (`slotIndex_card = 4·|D|`, `slotIndex_fiber_card = 4`).

---

## 4. Finite-chain status

**24-WINDOW FINITE CHAIN: KERNEL-PROVED.**  24 contiguous windows
(`L_{i+1} = U_i + 1`, `L_0 = 4000000001`, `U_23 = 67108856338751594`) — no gaps; the
contiguity is what the chained `by_cases` of `no_of_M_le_extendedCeiling` checks.
Certificates replayed: **52 recursive Pratt certificates** + **72 leaf trial-division
primality proofs** = 124 primality certificates, all kernel-checked, none replaced by an
oracle.

| # | x | L | U | `pu` (`x = a·pu`) | `pv` (`x+1 = b·pv`) |
|---|---|---|---|---|---|
| 0 | 3999999722 | 4000000001 | 7999999444 | 1999999861 (a=2) | 1333333241 (b=3) |
| 1 | 7999999233 | 7999999445 | 15999998466 | 2666666411 (a=3) | 3999999617 (b=2) |
| 2 | 15999998396 | 15999998467 | 31999996792 | 3999999599 (a=4) | 5333332799 (b=3) |
| 3 | 31999996382 | 31999996793 | 63999992764 | 15999998191 (a=2) | 10666665461 (b=3) |
| 4 | 63999992764 | 63999992765 | 127999985528 | 15999998191 (a=4) | 12799998553 (b=5) |
| 5 | 127999985482 | 127999985529 | 255999970964 | 63999992741 (a=2) | 127999985483 (b=1) |
| 6 | 255999970893 | 255999970965 | 511999941786 | 85333323631 (a=3) | 127999985447 (b=2) |
| 7 | 511999941722 | 511999941787 | 1023999883444 | 255999970861 (a=2) | 170666647241 (b=3) |
| 8 | 1023999883441 | 1023999883445 | 2047999766882 | 1023999883441 (a=1) | 511999941721 (b=2) |
| 9 | 2047999766366 | 2047999766883 | 4095999532732 | 1023999883183 (a=2) | 682666588789 (b=3) |
| 10 | 4095999532732 | 4095999532733 | 8191999065464 | 1023999883183 (a=4) | 4095999532733 (b=1) |
| 11 | 8191999065043 | 8191999065465 | 16383998130086 | 8191999065043 (a=1) | 2047999766261 (b=4) |
| 12 | 16383998129937 | 16383998130087 | 32767996259874 | 5461332709979 (a=3) | 8191999064969 (b=2) |
| 13 | 32767996259553 | 32767996259875 | 65535992519106 | 10922665419851 (a=3) | 16383998129777 (b=2) |
| 14 | 65535992518466 | 65535992519107 | 131071985036932 | 32767996259233 (a=2) | 21845330839489 (b=3) |
| 15 | 131071985036913 | 131071985036933 | 262143970073826 | 43690661678971 (a=3) | 65535992518457 (b=2) |
| 16 | 262143970073653 | 262143970073827 | 524287940147306 | 262143970073653 (a=1) | 131071985036827 (b=2) |
| 17 | 524287940146868 | 524287940147307 | 1048575880293736 | 131071985036717 (a=4) | 174762646715623 (b=3) |
| 18 | 1048575880293313 | 1048575880293737 | 2097151760586626 | 1048575880293313 (a=1) | 524287940146657 (b=2) |
| 19 | 2097151760586097 | 2097151760586627 | 4194303521172194 | 2097151760586097 (a=1) | 1048575880293049 (b=2) |
| 20 | 4194303521172052 | 4194303521172195 | 8388607042344104 | 1048575880293013 (a=4) | 4194303521172053 (b=1) |
| 21 | 8388607042343977 | 8388607042344105 | 16777214084687954 | 8388607042343977 (a=1) | 4194303521171989 (b=2) |
| 22 | 16777214084687942 | 16777214084687955 | 33554428169375884 | 8388607042343971 (a=2) | 5592404694895981 (b=3) |
| 23 | 33554428169375797 | 33554428169375885 | **67108856338751594** | 33554428169375797 (a=1) | 16777214084687899 (b=2) |

No window or certificate failed; there is no first-failure to report for this subtask.

**Note on provenance.**  No pre-existing Lean draft or certificate file for this interval
was present in the repository (the only occurrences of `4000000001` were unrelated
threshold predicates).  The 24-window chain above was therefore reconstructed from scratch
by the greedy doubling search that the recorded endpoint `67108856338751594` implies, and
it reproduces that ceiling **exactly**.

---

## 5. Uninhabited analytic sockets

* `Erdos287.September3ConditionalCompiler.PhysicalFixedResidueAPBound` — the *only* analytic
  input of this layer.  Exposed fields: per-slot **prime discrepancy**, **numerical error
  function** `err`, the **bound** `|discrepancy| ≤ err` quantified over each finite physical
  interval, plus `err_nonneg`; the slot itself carries **residue** `s = ±1`, **modulus**
  `q1 · d` with `q1 ∈ {1,4}` and `d` odd, and the **interval endpoints** `lo`, `hi`; the
  **activation threshold** lives in `PhysicalSlotFamily`.  It stores **no** `E_T`
  conclusion and **no** endpoint-supremum field.  No inhabitant is constructed anywhere.
* Pre-existing sockets (complete Perron/nuclear ledger; hard-`U` shared-Ford adapter) are
  untouched and keep their earlier statuses.

Honesty note (also in the module docstring): the socket is deliberately weak — nothing
forces `err` to be small, so a vacuous inhabitant with huge `err` exists in principle.  The
compiler's conclusion is correspondingly symbolic in `err`, and no number is banked.

---

## 6. Firewalls

1. **FINITE-CERTIFICATE-COVERAGE** is an arithmetic finite result only; it does **not**
   assert that the medium analytic branch is closed
   (`finiteCoverage_does_not_close_medium_branch`).
2. **FIXED-RESIDUE-SOURCE ≠ ANALYTIC-PRIME-DISTRIBUTION-THEOREM** — §C is congruence
   algebra over `ℤ`; `p` is a name, not a primality assumption.
3. The conditional compiler does not assert Maynard or any analytic theorem
   (`maynard_is_not_asserted`).
4. The conditional compiler does not assert a numerical `E_T` bound
   (`maynardNumericalConstant = notBanked`).
5. The conditional compiler does not assert `E_T = o(B_X)` — that would have to be supplied
   separately (`eTDirectedMedium = conditionalOpen`).
6. The conditional compiler does not imply Erdős #287
   (`conditionalCompiler_does_not_prove_erdos287`; `erdos287 = open_`).
7. No endpoint-supremum field is banked (`endpointSupremumField = notBanked`).
8. Status rows are metadata, never proof claims; five rows are additionally backed by the
   theorems they label (`row_*_backed`).

---

## 7. `lake build` result

`lake build` (whole project, `RequestProject.Main` inclusive):
**PASS** — `Build completed successfully (8418 jobs)`.  The only diagnostics are
pre-existing informational `Try this` notes and `unusedVariables` warnings, including the
deliberately retained physical hypotheses (`hd`, `hs`, `hn`) of the two `_pm` theorems in
§C, which are documented in their docstrings.

---

## 8. `#print axioms` summary

Every principal new declaration audited in
`RequestProject/Status/AxiomAuditErdos287September3SourceBank.lean` reports one of

```
does not depend on any axioms
[propext]
[propext, Quot.sound]
[propext, Classical.choice, Quot.sound]
```

i.e. no stronger than the existing project baseline.  In particular

```
Erdos287.Pratt.prime_of_certificate                            [propext, Classical.choice, Quot.sound]
Erdos287.Certificates.prime_33554428169375797                  [propext, Classical.choice, Quot.sound]
Erdos287.Gap2CE.no_of_M_le_extendedCeiling                     [propext, Classical.choice, Quot.sound]
Erdos287.no_Erdos287Counterexample_of_max_le_extendedCeiling   [propext, Classical.choice, Quot.sound]
Erdos287.arithmeticCoverage_exceeds_twoExp375                  [propext, Classical.choice, Quot.sound]
```

`Classical.choice` enters through ordinary Mathlib lemmas, exactly as in the earlier layers.

---

## 9. First failure

None.  No window, no primality certificate, and no source-algebra statement failed.

---

## 10. No-overclaim status

* Erdős #287: **open**.  Nothing here proves it or claims to.
* The finite extension excludes counterexample maxima `≤ 67108856338751594` only.
* The `E_T` compiler is an **implication** whose antecedent is never supplied.
* No analytic theorem, numerical constant, or endpoint supremum is banked.
* `E_L`: conditional / open.  `E_M`: status retained from the earlier layer.
  Global effectivity: open.

---

# STRICT OUTPUT

```
24-WINDOW FINITE CHAIN:        KERNEL-PROVED
FINITE CEILING:                67108856338751594
COVERS ceil(2 exp(37.5)):      KERNEL-PROVED  (38643198608805673 < 67108856338751594)
2-ADIC MÖBIUS PAIR:            KERNEL-PROVED
ODD-DIVISOR TOT SOURCE:        KERNEL-PROVED
d FIXED-RESIDUE ARITHMETIC:    KERNEL-PROVED
4d FIXED-RESIDUE ARITHMETIC:   KERNEL-PROVED
TOT SOURCE SPLIT T0-T2:        KERNEL-PROVED
CANONICAL FOUR-INTERVAL:       KERNEL-PROVED
AP ANALYTIC SOCKET:            UNINHABITED
ENDPOINT-SUPREMUM ASSUMED:     NO
MAYNARD THEOREM ASSERTED:      NO
CONDITIONAL E_T COMPILER:      KERNEL-PROVED (implication only)
NUMERICAL E_T:                 NOT BANKED
E_L:                           OPEN / CONDITIONAL
GLOBAL EFFECTIVITY:            OPEN
ERDOS287:                      OPEN
LAKE BUILD:                    PASS
SORRY / SORRYAX:               NONE
NEW CUSTOM AXIOMS:             NONE
OVERCLAIM AUDIT:               PASS
```
