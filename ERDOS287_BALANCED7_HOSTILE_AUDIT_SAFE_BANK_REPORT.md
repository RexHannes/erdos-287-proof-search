# ERDŐS #287 — BALANCED7 HOSTILE-AUDIT SAFE BANK

**Source seal · general-modulus LS · full-`q` reassembly · effectivity socket**

Append-only continuation of the existing workspace.  No historical V15–V24 / SP-2 /
PostBalanced7Pro file, status row or report was modified or deleted; `ARISTOTLE_SUMMARY.md`
was not touched.  Namespace convention: `Erdos287.*` (`Erdos287.HostileAudit`,
`Erdos287.Balanced7HostileAuditStatus`).

---

## 0. Files added

All new Lean files live in `RequestProject/HostileAudit/` and `RequestProject/Status/`:

| § | file | content |
|---|------|---------|
| 2 | `HostileAudit/BalancedSevenSP2SourceAdapter.lean` | SP-2 → seven-box **source seal**; literal `H_*(P) = −20`; general unimodular-phase box law |
| 3 | `HostileAudit/GeneralModulusInducedCharacter.lean` | induced-character pointwise identity; Möbius expansion of `1_{gcd(n,j)=1}` (non-squarefree `j` included) |
| 4 | `HostileAudit/TotientComplementaryFactor.lean` | `φ(f)φ(j) ≤ φ(fj)`; exact gcd formula; `f > D, R ≤ fj < 2R ⇒ j < 2R/D`; `d ≠ j` firewall |
| 5 | `HostileAudit/GeneralModulusConductorSplitLargeSieve.lean` | uninhabited primitive weighted large sieve; conditional compiler to `polylog·(R + N/D)·‖c‖₂²` |
| 7 | `HostileAudit/SmallROwnerCapacity.lean` | `S_sr = M_sr_prin + D_sr`; owner uniqueness; `q ≥ X^{2/3}` capacity; `2/3 + 1/3 = 1` |
| 8 | `HostileAudit/ShortTResidueGeometry.lean` | exactly-one forbidden class mod `ℓ ∤ q`; constant class for `ℓ ∣ q`; `2/105 < 15/105`; sieve primes miss the `Y`-boxes |
| 9 | `HostileAudit/ShiuHypothesisCompiler.lean` | `5/7`, `3/4`, margin `1/28`; `gcd(±1, 2w') = 1`; conditional consumer |
| 10 | `HostileAudit/RawRawVarianceCompiler.lean` | raw-raw compiler to `(M·W₅²/Q)·log^{-5}`; **`log^{-10}` refuted**; Cauchy cross bound `log^{-15/2}` |
| 11 | `HostileAudit/HardAmplitudeExponentCompiler.lean` | `C_ext = 1`; `M·W₅ = X`; `−(2+5)/2 + 1 = −5/2`; dyadic `−3/2`; abstract `o(1)` interface |
| 12 | `HostileAudit/FullQExactReassembly.lean` | literal boundary ownership; region principal/defect; principals sum to `FullEulerPrincipal`; no double spending; even-`q` and non-unit routing |
| 13 | `HostileAudit/BalancedSevenHostileAuditCompiler.lean` | `BalancedSevenHostileAuditInputs → BalancedSevenAsymptoticConclusion` (conditional, uninhabited) |
| 15 | `HostileAudit/EffectiveLowConductorExceptionalPNT.lean` | effectivity socket with explicit constants, threshold, optional exceptional zero; conditional consumer |
| 14/6/16 | `Status/CurrentStatusErdos287Balanced7HostileAudit.lean` | new append-only ledger, retracted death certificates, downstream frontier |
| 17 | `Status/AxiomAuditErdos287Balanced7HostileAudit.lean` | `#print axioms` for every principal declaration of this pass |

`RequestProject/Main.lean` was modified **by import lines only**.

---

## 1. Existing bank verified first

`lake build` on the pre-existing repository succeeded (8213 jobs, 0 errors) before any new
file was added.  The modules named in the brief — `SevenBoxPrimeWeights`,
`PrimeTupleMultiplicity`, `ConductorSplitLargeSieve`, `LowConductorSiegelWalfisz`,
`SmallQ34LSCompiler`, `SmallPrimePrefix`, `PostRepairOwnerCompiler`,
`UniformFragmentationCompiler`, `CurrentStatusErdos287PostBalanced7Pro`,
`AxiomAuditErdos287PostBalanced7Pro`, together with the SP-2 / fixed-certificate sources —
are **reused, not duplicated**: the new layer imports them and re-exports their theorems
(`truncMobius`, `omegaBox`, `sSmallR`/`dSmallR`, `postRepairOwnerOf`, `IsSmallQ`/`IsSmallR`/
`IsHard`, `BalancedSevenShortTSieveInput`, `BalancedSevenShiuInput`,
`BalancedSevenLowConductorSiegelWalfiszInput`, `balancedCellWeight`, `sp2CextRepaired`).

---

## 2. Source seal (§2) — result: **SOURCE_OPEN**

Proved:

* `truncMobius_of_primeProduct` — the *literal* repository weight
  `H_*(n) = ∑_{d ∣ n, d ≤ T} μ(d)` at `n = p₁⋯p₇` equals the subset-lattice alternating sum,
  when the truncation cuts at divisor depth `r`;
* `truncMobius_sevenBox_eq_neg20` — `H_*(P) = 1 − 7 + 21 − 35 = −20` (depth `r = 3`), and
  `truncMobius_sevenBox_matches_counterguard` identifies it with the banked
  `balancedCellWeight 7 3`;
* `boxWeight` with an **arbitrary** phase, `norm_boxWeight_le_one` (`|phase| = 1`, `0 ≤ V ≤ 1`
  ⇒ `‖ω_i(p)‖ ≤ 1`), `boxWeight_support_is_primes`, and `boxWeight_eq_omegaBox` showing the
  repository's archimedean weight is the case `phase(p) = p^{it}`;
* `BalancedSevenSP2SourceSeal` with `seal_pointwise_law`, `seal_prime_support`,
  `seal_certificate_value_neg20` and `seal_rigidity` (the seal pins the packet uniquely — it
  is an identification, not a same-dimensions model).

Not proved: the identification of the *physical* analytic packet with the SP-2 packet needs
the fixed-certificate `cell_identity`, which this repository does not discharge.
`sp2SourceSeal_not_automatic` refutes the seal on explicit data.  Therefore the row is
`sourceOpen` and **Balanced7 is not recorded as source-sealed**.

---

## 3–5. General modulus

* `induced_character_pointwise` : `χ_r(n) = χ*(n)·1_{gcd(n,j)=1}` pointwise, **with no**
  squarefreeness of `r` and **no** `gcd(f,j) = 1`; `inducedSpec_holds_for_nonSquarefree_modulus`
  gives the instance `f = j = 2`, `r = 4`.
* `coprimeIndicator_moebius_expansion` : `1_{gcd(n,j)=1} = ∑_{d ∣ j, d ∣ n} μ(d)` for every
  `j ≠ 0`, non-squarefree included (`moebius_expansion_nonSquarefree_j_four`).
* `totient_mul_ge`, `totient_gcd_exact`, `complementary_factor_bound`
  (`f > D`, `fj < 2R` ⇒ `j < 2R/D`), `complementary_factor_saving_is_real`.
* `divisorVariable_ne_complementaryFactor` : the divisor-expansion variable `d` is **not** the
  complementary factor `j`; keeping only `d = j` makes the expansion false (explicit
  `j = 6`, `n = 1`).
* `general_modulus_conductorSplit_compiler` : from the uninhabited
  `PrimitiveWeightedLargeSieveInput` (literal weighted form `(R/j + N j/(R d))·E_d`), the
  conductor window data and the uninhabited `DivisorSumPolylogInput`, the target
  `L_gen ≤ (2·polylog)·(R + N/D)·‖c‖₂²`.  Both analytic children are refuted on explicit
  data.

---

## 6. Retracted death certificates (metadata)

```
SMALLQ-LS-DEATH-CERTIFICATE            : RETRACTED   (dropped f·k ∼ Q, hence k ≪ Q/D)
SMALLR-GENERAL-MODULUS-DEATH-CERTIFICATE : RETRACTED (induced-character identity valid for
                                          arbitrary r; D-saving from j ≪ R/D)
```

Recorded in the new ledger (`death_certificates_retracted`), together with the two Lean
theorems that force the retraction.  No historical file was erased.

---

## 7–12. The remaining sections

* **SmallR owner**: `smallR_source_eq_principal_add_defect`, `smallR_owner_assignment`
  (principal → `eulerPrincipal`, defect → `smallRDirect`, uniquely),
  `smallR_modulus_capacity` (`q ≥ X^{2/3}`), `smallR_exponent_ledger`.  The divisor asymptotic
  and `φ` lower bound stay in the uninhabited `SmallRPrincipalCapacityInput`.
* **Short-`t`**: `shortT_unique_forbidden_class` (∃!), `shortT_constant_class_of_dvd`,
  `shortT_scale_ledger`, `shortT_sieve_primes_disjoint_from_boxes`.  The Selberg estimate
  stays uninhabited.
* **Shiu**: `shiu_exponent_margin` (`3/4 − 5/7 = 1/28`),
  `shiu_modulus_within_admissible_range`, `shiu_shift_coprime`, conditional consumer
  `shiu_target_of_input`.  Shiu's theorem is neither proved nor axiomatised.
* **Raw-raw**: `rawRaw_variance_bound` gives `V_RR ≤ (M·W₅²/Q)·log^{-5}`;
  `rawRaw_saving_is_five_not_ten` **proves** that the `log^{-10}` version fails on admissible
  data; `cross_variance_bound` gives `V_RP ≤ √(A·B)·log^{-15/2}`.
* **Hard amplitude**: `C_ext = 1` reused; `hard_amplitude_product` (`X^{2/7}·X^{5/7} = X`);
  `hard_cell_log_budget` (`−5/2`); `hard_dyadic_summation` (`−3/2`); the `o(1)` is the
  uninhabited `HardAmplitudeAsymptoticInterface`.
* **Full-`q`**: literal boundary ownership (`q = U` → SmallQ, `r = U` with `q > U` → SmallR);
  `region_source_split`; `region_principals_sum_eq_full`;
  `no_region_owns_the_full_principal`; `fullQ_no_double_spending`;
  `even_q_is_impossible` and `q_coprime_twoP` (routing of even and non-unit moduli).

---

## 13/15. Compilers

`BalancedSevenHostileAuditInputs` contains exactly the eight audited ingredients (source
adapter, SmallQ low conductor, primitive large sieve, general-modulus compiler inputs,
SmallR direct, short-`t`, Shiu, Euler principal) plus the exact full-`q` reassembly and the
per-cell savings; `balancedSeven_hostileAudit_compiler` derives
`BalancedSevenAsymptoticConclusion`.  The structure is **not inhabited**
(`hostile_audit_is_not_a_lean_proof`).

`EffectiveLowConductorExceptionalPNTInput` is the new effectivity socket (explicit constants
and threshold, principal term, optional exceptional real character and secondary term, smooth
`Y`-scale weight, `f ≤ log^30 X`, Mellin range, induction to `q`, exact comparison), with the
conditional consumer `effective_smallQ_lowConductor_of_input` and the contrast theorem
`effective_socket_is_not_siegelWalfisz`.  Uninhabited.

---

## FINAL BLOCK

```
BALANCED7 SOURCE SEAL:
    SOURCE_OPEN.
    Finite content PROVED: H_*(p1...p7) = 1 - 7 + 21 - 35 = -20 for the literal
    repository weight; seven-box law with |phase| = 1, 0 <= V <= 1 gives |omega_i(p)| <= 1
    as a theorem; the seal is rigid.  The identification with the physical analytic packet
    needs the fixed-certificate cell identity, which is not discharged.
    BALANCED7 IS NOT RECORDED AS SOURCE-SEALED.

SMALLQ:
    HOSTILE-AUDITED EXTERNAL PASS / CONDITIONAL COMPILER.

SMALLR GENERAL MODULUS:
    HOSTILE-AUDITED EXTERNAL PASS / CONDITIONAL COMPILER.
    Definition-level algebra (induced character, Mobius expansion, j < 2R/D) PROVED.

SMALLR OWNER:
    PROVED ALGEBRAIC (exact subtraction, exact owner uniqueness, q >= X^{2/3} capacity).

SHORT-t:
    EXTERNALLY AUDITED.  Finite residue geometry and scale separation PROVED;
    Selberg upper sieve UNINHABITED.

SHIU:
    EXTERNALLY AUDITED.  Rational hypothesis map (5/7, 3/4, 1/28) and gcd(+-1, 2w') = 1
    PROVED; Shiu's theorem UNINHABITED, not an axiom.

RAW-RAW:
    EXTERNALLY AUDITED.  Compiler PROVED with saving log^-5 (log^-10 REFUTED);
    Cauchy cross bound log^-15/2 PROVED.

FULL-q OWNER:
    PROVED ALGEBRAIC (exact partition with literal boundaries, principal/defect split,
    principals sum to the full Euler principal, no double spending, even-q and
    non-unit routing).

BALANCED7:
    HOSTILE-AUDITED RESEARCH/PAPER PASS; NOT LEAN ANALYTIC THEOREM.

BALANCED7 EFFECTIVE:
    OPEN.

EFFECTIVITY NEXT SOCKET:
    287-EFFECTIVE-LOWCOND-EXCEPTIONAL-PNT45 (SOURCE/THEOREM DICTIONARY OPEN).

MAIN-LINE FIRST RESIDUAL:
    287-K0-SP2-THREE-SMALLPRIME-PREFIX-TYPEII45.

FCL:
    OPEN.

ERDOS287:
    OPEN.

BUILD:
    lake build SUCCEEDS - 8227 jobs, 0 errors.  The only warning in the repository is the
    pre-existing linter note in RequestProject/Erdos287/FixedCertificateSmoothParity.lean:60;
    zero warnings in the new files.

TRUST:
    Zero occurrences of sorry, admit, axiom, opaque, unsafe, native_decide or
    @[implemented_by] in all new files.  #print axioms on every principal new declaration
    reports only propext, Classical.choice, Quot.sound (several depend on fewer).
    Every analytic/source interface of this layer is UNINHABITED, each with an accompanying
    refutation theorem exhibiting explicit failing data.  No ledger row is `closed`.
```

### FINAL FIREWALL

Formalisation certifies the source algebra and the conditional dependency graph.  It does not
convert external sieve / PNT / Shiu / large-sieve mathematics into kernel theorems.
