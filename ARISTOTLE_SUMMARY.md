# Summary of changes for run 61962c4d-c5c0-4dd9-944e-43a4d968eba9
Added a new, self-contained Erdős #287 **effectivity kernel bank** to the project — thirteen Lean modules, all proved, all wired into the default build. Full `lake build` **PASSES** (8450 jobs); no `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, `implemented_by` or `opaque` occurs in any new file, and `#print axioms` on all fifty principal theorems reports only `propext, Classical.choice, Quot.sound` (or none). **Erdős #287 is not claimed**; the joined square function, `C_joint ≤ 0.09`, medium-k, the two-high gap, the signed floor and Maynard are untouched.

Files added (`RequestProject/Erdos287/`): `BsrcWeights`, `AllComplement`, `OddHalfDivisor`, `Reflection`, `MediumLedger`, `C1C2Splice`, `OddLineCancellation`, `RatioBoundary`, `EulerLocal`, `TwoVariableZ`, `PerronAlgebra`, `IncrementalDirectedLedger`, `CurrentStatusEffectivity`; plus the report `ERDOS287_EFFECTIVITY_KERNEL_BANK_REPORT.md`. `RequestProject/Main.lean` gained the thirteen imports.

STRICT OUTPUT — PHYSICAL B1 NORMALIZATION: KERNEL-PROVED (B0/β multiplicative, `B1·B(ab)=B(a)B(b)`, plus a firewall showing one-B1-per-prime is a different normalisation) · ALL-COMPLEMENT DISCRETE: KERNEL-PROVED (`B(d)·∑_{k|n,(k,d)=1}β(k)=B(dn)`, by finite prime-factor products only) · CONTINUOUS EULER IDENTITY: KERNEL-PROVED finite / CONDITIONAL infinite (convergence is a `Tendsto` hypothesis, never postulated) · ODD HALF-DIVISOR: KERNEL-PROVED (exact variable change `n>cd ↔ c d²<w`) · w=6 FIREWALL: KERNEL-PROVED (`H₁^odd(6)=1` vs unrestricted `0`) · FULL-vs-MEDIUM TYPING: KERNEL-PROVED · INCREMENTAL LEDGER TYPE: KERNEL-PROVED (no coercion inserts a full estimate without an explicit removal list) · HALF-DIVISOR REFLECTION: KERNEL-PROVED, both boundary forms, plus special cases A and B · c1/c2 DISCRETE SPLICE: KERNEL-PROVED (the `4d` endpoint is derived from `n↦2n`) · c1/c2 CONTINUOUS SPLICE: KERNEL-PROVED, both ½'s coming from the substitution, integrability an explicit hypothesis · FULL ODD DISCRETE CANCELLATION: KERNEL-PROVED · CONTINUOUS COEFFICIENT CONVOLUTION: KERNEL-PROVED (`μ1_odd/φ = mOdd ⋆ r`), downstream cancellation conditional on `∑ mOdd = 0` · RATIO-BOUNDARY: KERNEL-PROVED (conditional on the two cancellations) · G_p LOCAL FACTOR and FINITE `B1·G(u,0)=1`: KERNEL-PROVED · TWO-VARIABLE LOCAL EULER IDENTITY and FINITE `Z(s,s)=0`: KERNEL-PROVED · INFINITE `Z(s,s)=0`: BLOCKED BY ANALYTIC CONVERGENCE (only a formal-product congruence is recorded, clearly labelled) · G ABSOLUTE-CONVERGENCE REGION: PARTIAL (`|G_p(u,0)−1| = 1/(p(p−2)) ≤ 3/p²`; the two missing analytic inputs are isolated in the docstring) · PERRON VARIABLE CHANGE: KERNEL-PROVED (algebra/Jacobian/kernel compensation only, no contour theorem) · STRICT EQUALITY ALGEBRA: KERNEL-PROVED conditional, giving `2(Δ₁−Δ₂)` from the −4 outer factor · INCREMENTAL LEDGER ARITHMETIC: KERNEL-PROVED (`8.86065e-7 − 5.250043872e-7 = 3.610606128e-7`, capacity `> 3.610606128e-7`) · JOINED SQUAREFUNCTION / MEDIUM-k / TWO-HIGH GAP / SIGNED FLOOR: OPEN · MAYNARD: NOT ENTERED · ERDOS287: OPEN.

Two places where the specification was ambiguous are documented explicitly rather than guessed silently: the `c=2` lanes are defined as the `n↦2n`-substituted lanes (which is what makes the `4d` endpoint and the two ½'s derived, not assumed), and `Z_P(u,v)` is defined as the difference of the two finite prime products. One statement was also weakened in hypotheses rather than strengthened: the all-complement identity turned out not to need `d` odd, so it is proved for all `d ≠ 0` with the requested odd-`d` form as a corollary.

# Summary of changes for run ff3caa6e-75f3-41eb-90ea-f831247718b8
Delivered both requested pieces: the Erdős #287 effectivity certificate bank and the surgical P0 `B_src` normalisation repair. Full `lake build` passes (8437 targets, no errors); a detailed report is in `ERDOS287_CERTIFICATE_BANK_AND_P0_REPAIR_REPORT.md`.

LEAN FILES (new)
`RequestProject/Erdos287/{SourceWeights, GcdDescent, BernoulliKernel, MediumKSource, RepeatedCores, DirectedLedger, FloorInterface, Bank}.lean` and `RequestProject/Status/CurrentStatusErdos287CertificateBank.lean`.
Edited surgically: `RequestProject/CurrentProgramme/Erdos287September4BsrcLocalMobiusCollapse.lean`, `RequestProject/Status/AxiomAuditErdos287September4SignedFloorBank.lean`, `RequestProject/Main.lean`. No proved bank was deleted.

NO SORRY: YES. NO CUSTOM AXIOMS: YES (no `axiom`, `@[implemented_by]`, `native_decide`, `unsafe`, `opaque`). LAKE BUILD: PASS.

P0 BUG LOCATED — confirmed exactly as suspected. The September‑4 module models the source as a purely local product `Bsrc Bloc d = ∏_{p|d} Bloc p` with the hypothesis `bloc p − Bloc p = −S₂` at every prime; multiplying that over `primeFactors(q)` inserts the global `S₂` once per prime and necessarily yields `S₂^{ω(q)}·μ(q)`. The theorems are true but describe an artificially locally‑normalised model, not the physical source.
OLD FALSE PHYSICAL THEOREM: RETYPED (nothing deleted). A P0 notice was added, §4.4/§4.5 retitled as the abstract model, and the counterexample renamed `literal_S2_mu_form_fails → abstractLocalNormalisation_S2_mu_form_fails` (its witness uses artificial local values, so it refutes only the over‑general abstract form). Exactly one physical local‑collapse theorem now exists.
CORRECT PHYSICAL DEFINITION: `B0(d)=∏(p−1)/(p−2)`, `B_src(d)=S₂·B0(d)`, `β(d)=∏1/(p−2)`, `λ(b)=∏(p−1)/(p−2)²`, with the typed relation `S₂·B_src(ab)=B_src(a)B_src(b)`.
CORRECT LOCAL COLLAPSE: KERNEL-PROVED — `β(p)−B0(p) = −1` for odd primes (and `= 0` at p=2, which is why oddness is required), hence `∑_{d|q} μ(d)B_src(d)β(q/d) = S₂·μ(q)` for odd squarefree q (`physicalBsrcMobiusCollapse45`).
q=15 REGRESSION: KERNEL-PROVED (`β(15) − B0(3)β(5) − B0(5)β(3) + B0(15) = 1`; divisor sum `= S₂`).
AFFECTED DECLARATIONS: only the four abstract `S₂^{ω(q)}` statements, referenced solely by the axiom-audit `#print axioms`; no physical compiler depended on them, so nothing had to be downgraded. UNAFFECTED BANK REBUILT: PASS.

CORE (all KERNEL-PROVED): coprime Möbius indicator; β/B0/λ multiplicativity and the typed `B_src` relation; λ local factor; exact local coefficient identity `μ(b)μ(bv)B_src(bv)β(bq) = λ(b)μ(v)B_src(v)β(q)`; the central `squarefree_gcd_descent` (stated over an arbitrary coefficient ring hom, with ℚ and ℝ instances), plus `gcd(b,q·v)=1` (with `gcd(q,v)` deliberately unconstrained) and a one-prime cancellation sanity check; phase / W-argument / derivative descent; hyperbola support descent (`0.9` always as exact `9/10`); medium-k exact source normal form (conditional on the finite truncation, no analytic bound claimed); `jointKernel_noLattice` — PROVED, by exact integration by parts, no Euler-summation lemma introduced; repeated-core ledger disjointness and exhaustiveness (no double counting), with the r=1/p²/p³ classification carried abstractly. The strict-endpoint sawtooth convention `ψ(n) = −1/2` is preserved, and the API firewall (only `jointKernel` is a k-consumer) is recorded.

CERTIFICATE — no compact machine certificate was attached, so the five analytic bounds are recorded as EXTERNAL-CERT inputs transcribed as exact rationals; only the arithmetic on them is kernel-checked, and nothing became an axiom.
CERTIFIED SUBTOTAL: 52188738751/10^17 = 5.2188738751e-7.
PRINTED 5.218873872e-7 CONSISTENT: NO — it is strictly smaller than the exact outward sum, short by exactly 3.1e-16, so it is not a valid outward subtotal.
REMAINING CAPACITY: 36417761249/10^17 = 3.6417761249e-7.
PRINTED 3.641776128e-7 CONSISTENT: NO — it overstates capacity by 3.1e-16. Use the corrected value.
The q=3 row (2.17e-8) is recorded as a sub-item of the k ≤ 31 total and proved not to be double-counted.
LARGE-SIEVE CONSTANTS: `∑λ(b)/√b < 7/2` and `∑β(q)² < 241/100` are NOT AVAILABLE (recorded, not kernel-checked); the sawtooth L² mass IS kernel-checked: `(1/q)∑_{a<q}(a/q−1/2)² = (q²+2)/(12q²)` and `≤ 11/108` for q ≥ 3.
q=3 CERTIFICATE: format/checker interface formalised only; the 4.5e9 search is not replayed and the claim is not asserted.
CONDITIONAL BUDGET THEOREM: KERNEL-PROVED, both abstractly and with the audited ledger numbers substituted.

OPEN: medium-k joint Bernoulli — OPEN; two-high a ≤ 180 — OPEN; signed B_src floor — OPEN (all three exist only as predicates); Maynard — NOT ENTERED (no predicate at all); Erdős #287 — OPEN, nothing here claims it.
FIRST EXACT REMAINING NODE: ERDOS287-TOT-BSRC-SQFREE-LATTICEBEARING-MEDIUMK-GCDDESCENT-JOINT-BERNOULLI-DIRECTED45.

`RequestProject/Erdos287/Bank.lean` runs `#print axioms` on every major theorem; each reports exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` and no custom axiom.

# Summary of changes for run caa78c95-832f-4710-8a9b-9cba8bd17ac4
Append-only September-4 signed `B_src` floor bank added. Nothing existing was deleted, edited or downgraded; **Erdős #287 is not claimed**, no Maynard theorem, no numerical Mertens statement and no analytic estimate is asserted. Full report: `ERDOS287_SEPTEMBER4_SIGNED_FLOOR_SAFE_BANK_REPORT.md`.

**Files added** (all under `RequestProject/`): `CurrentProgramme/Erdos287September4PhysicalW.lean`, `…CanonicalStateSign.lean`, `…T0T2DeepEvenCancellation.lean`, `…BsrcLocalMobiusCollapse.lean`, `…BoundaryDivisorLattice.lean`, `…SignedBsrcCompiler.lean`, `…BoundaryCertificateChecker.lean`, `…LargeLTailCompiler.lean`, plus `Status/CurrentStatusErdos287September4SignedFloorBank.lean` and `Status/AxiomAuditErdos287September4SignedFloorBank.lean`; `Main.lean` gained the ten imports.

**Kernel-proved.** Physical W: exact definition with rational break points 7/10, 4/5, 9/10; support ⊆ [7/10,9/10]; W(7/10)=W(9/10)=0, W(4/5)=1; 0 ≤ W ≤ 1; strictly increasing on [7/10,4/5], strictly decreasing on [4/5,9/10]; sup norm `IsGreatest (range W) 1`; **Var(W)=2** in Mathlib's own `eVariationOn` (no bespoke variation notion was invented); hence **C_W = 2‖W‖_∞ + Var(W) = 4** with every term proved; plus the derivative W′ = −20uv²e^{1−v} inside the support. Canonical-state sign invariance κ_ε = μ(d_low)·g_j = (−1)^{ω(d)} = μ(d) with all hypotheses explicit binders (not structure fields), and the one-prime threshold-crossing invariance. The exact T⁰−T² decomposition into the odd family plus the even collar 1_{d ≤ Y(dr) < 2d}, the r = 2u reindexing facts (same n, same κ, same weight, B_src(2m)=B_src(m)), and deep-even cancellation `t0t2DeepEvenCancellation45`, with a firewall theorem witnessing that this is *not* a complete signed-floor closure. Interior divisor-lattice Möbius collapse `interiorLocalMobiusCollapse45` via the local prime-factor identity and multiplicativity over `q.primeFactors` (finite; no infinite Euler product). The exact signed source `R_signed = −4 Σ_{d odd}(E_d[V0,d] − E_d[V2,d])` with −4 *derived* from the two affine sign families times the T⁰−T² comparison sign. Exact rational budget 14164610/10¹⁵ + 985835/10¹² < 10⁻⁶ (sharper pole value kept, slack preserved) and the ordered-field budget compiler. The boundary certificate checker: coverage soundness over 42.9 ≤ L ≤ 62.5, per-box budget check, and the aggregate bound. Tail envelope 9360L(1+L)e^{−L/2} strictly decreasing on [4,∞) and the endpoint decimal envelope(62.5) < 10⁻⁶ proved *inside the kernel* from 7889/6144 ≤ exp(1/4) and 37147500·10⁶ < (7889/6144)¹²⁵ — so both MONOTONICITY and ENDPOINT DECIMAL are kernel-proved, with no numerical socket needed.

**Repair found (§4).** The literally requested identity Σ_{d∣q} μ(d)B_src(d)β(q/d) = S₂·μ(q) is **false** once ω(q) ≥ 2: kernel-proved counterexample q = 15, S₂ = 2, B_loc ≡ 0, β_loc ≡ −2 gives 4, not 2. The correct global form S₂^{ω(q)}·μ(q) is proved, and the requested shape holds exactly under the explicit hypothesis S₂^{ω(q)} = S₂ (in particular on a one-prime fibre). Both forms are stated; nothing was silently reinterpreted.

**Partial / external, as declared.** Boundary datatype BUILT (7 source-native causes, record reconstructing the omitted fibre) and the interior-or-boundary dichotomy kernel-proved, with a firewall counterexample showing the collapse fails on a truncated fibre; physical exhaustiveness of the cause list is PARTIAL and isolated as a stated (unproved) obligation. Secondary pole: analytic residue EXTERNAL / NOT FORMALIZED, only the downstream shoulder implication proved; the socket contains mathematical fields only and no floor conclusion. Compact slab 42.9–62.5 is CONDITIONAL; **no actual numerical certificate exists** (`bankedCertificates = []`), and the domination socket is never inhabited — a single clearly-labelled structural demo with an empty class list only shows the checker is non-vacuous. Mertens interface uninhabited; Maynard socket untouched and uninhabited; numerical E_T not banked; E_T, E_L, global effectivity and Erdős #287 remain open.

**Audit.** `lake build` PASSES (all 8428 jobs, `RequestProject.Main` included). `#print axioms` is run on all 92 principal new declarations: every one reports no axioms or a subset of `propext, Classical.choice, Quot.sound`. No `sorry`/`sorryAx`, no custom `axiom`, no `unsafe`, `native_decide`, `implemented_by`, `opaque` or `skipKernelTC` in any new file; no lint warnings in the new files. The status ledger, its firewalls and its row-backing theorems are machine-checked. First exact remaining node: the boundary numerical certificate (no event-box data for 42.9 ≤ L ≤ 62.5, and no inhabitant of the domination input). All work committed and pushed.

# Summary of changes for run eccaa4cc-2cfa-4ca3-b6aa-a412e582fb3d
All requested September-3 work is complete, append-only, and building. Nothing existing was deleted, rewritten, or weakened; Erdős #287 is **not** claimed and stays open.

**Priority A — 24-window finite extension: KERNEL-PROVED.**
No pre-existing Lean draft or certificate data for the interval `4000000001 … 67108856338751594` was in the repository, so the chain was reconstructed and is now replayed entirely in the kernel:
- `RequestProject/CurrentProgramme/Erdos287September3PrattEngine.lean` — a recursive (Pratt/Lucas) primality-certificate engine: a fuel-driven binary modular exponentiation `powMod` with a **proved** correctness theorem, and `Erdos287.Pratt.prime_of_certificate`. This was necessary because trial division cannot reach the ~10^16 primes the new windows need.
- `…Erdos287September3PrattCertificateBank.lean` — 72 leaf primes (`norm_num`, all `< 10^9`) plus **52 recursive Pratt certificates**, bottom-up, up to `33554428169375797`. No oracle, no `native_decide`.
- `…Erdos287September3FiniteExtension24Window.lean` — the **24 contiguous windows** (`L_{i+1} = U_i + 1`, no gaps) and `Erdos287.Gap2CE.no_of_M_le_extendedCeiling`, `Erdos287.no_Erdos287Counterexample_of_max_le_extendedCeiling` — the *same* predicates and interval blocker as the existing 4·10^9 bank, with the ceiling extended to exactly **67108856338751594**; plus `arithmeticCoverage_exceeds_twoExp375 : 38643198608805673 < extendedCeiling`. Firewall recorded: this is finite arithmetic only and does not close the medium analytic branch.

**Priority B — 2-adic Möbius pairing: KERNEL-PROVED.** `…Erdos287September3TotTwoAdicMobiusPairing.lean`: `μ(2a) = −μ(a)` for odd `a`, the canonical coefficients `kappaEps`/`sigmaEps`, the exact odd-divisor source identity `oddDivisorTotSourceIdentity` (stated before any triangle inequality, with the two pairing equations as explicit hypotheses, discharged for the canonical coefficient), the split `totLaneSourceSplit : T = T⁰ − T²` for supplied weights, and an algebraic witness that a termwise triangle bound destroys the `μ(a)/μ(2a)` cancellation.

**§3 fixed-residue arithmetic: KERNEL-PROVED.** `…Erdos287September3TotFixedResidueArithmetic.lean`: `p = 2dr+s ⇒ p ≡ s (mod d)`, `p = 4du+s ⇒ p ≡ s (mod 4d)`, and the converse integrality `p ≡ s (mod d), p odd, d odd, s = ±1 ⇒ 2d ∣ p − s` (parity hypotheses not weakened). Firewall: fixed-residue source ≠ analytic prime-distribution theorem.

**§5–§6 conditional compiler.** `…Erdos287September3TotFixedResidueConditionalCompiler.lean`: an **uninhabited** external AP socket exposing residue, modulus (`q1·d`, `q1 ∈ {1,4}`), finite interval endpoints, prime discrepancy, numerical error function/bound and activation threshold — with no endpoint-supremum field and no stored `E_T` conclusion — and the implication-only `totLaneFixedResidueConditionalBound45`, with the slot index `D ×ˢ {1,4} ×ˢ {−1,+1}` (four slots per modulus: two signs once, two families once).

**Priority C (optional): KERNEL-PROVED.** `…Erdos287September3CanonicalSplitFourInterval.lean`: abstract monotone crossing lemma, two thresholds per window, coefficient = signed sum of ≤ 4 interval indicators, with the numerical exponent content isolated and computed exactly (`d ≤ n^(1/2) ↔ d² ≤ n`).

**Status/audit/report.** Added `RequestProject/Status/CurrentStatusErdos287September3SourceBank.lean` (append-only ledger with the requested rows, firewall theorems and five rows backed by the theorems they label) and `…/AxiomAuditErdos287September3SourceBank.lean`; `RequestProject/Main.lean` gained the nine imports; full details in `ERDOS287_SEPTEMBER3_FINITE_AND_2ADIC_SAFE_BANK_REPORT.md` (window table, certificate counts, firewalls, axiom summary). The generator scripts are in `scripts/` and are untrusted — every statement they produce is re-proved by the kernel.

STRICT OUTPUT — 24-WINDOW FINITE CHAIN: KERNEL-PROVED · FINITE CEILING: 67108856338751594 · COVERS ceil(2 exp(37.5)): KERNEL-PROVED · 2-ADIC MÖBIUS PAIR: KERNEL-PROVED · ODD-DIVISOR TOT SOURCE: KERNEL-PROVED · d FIXED-RESIDUE: KERNEL-PROVED · 4d FIXED-RESIDUE: KERNEL-PROVED · TOT SOURCE SPLIT T0-T2: KERNEL-PROVED · CANONICAL FOUR-INTERVAL: KERNEL-PROVED · AP ANALYTIC SOCKET: UNINHABITED · ENDPOINT-SUPREMUM ASSUMED: NO · MAYNARD THEOREM ASSERTED: NO · CONDITIONAL E_T COMPILER: KERNEL-PROVED (implication only) · NUMERICAL E_T: NOT BANKED · E_L: OPEN/CONDITIONAL · GLOBAL EFFECTIVITY: OPEN · ERDOS287: OPEN · LAKE BUILD: PASS (8418 jobs) · SORRY/SORRYAX: NONE · NEW CUSTOM AXIOMS: NONE (all new declarations use only propext / Classical.choice / Quot.sound or fewer) · OVERCLAIM AUDIT: PASS.

# Summary of changes for run f7a1242f-400f-4a54-b51d-ff89318e9bd0
## What was added (append-only; nothing existing was deleted or rewritten)

**New Lean modules**

- `RequestProject/CurrentProgramme/Erdos287September2TaggedTwoLaneSource.lean` — the tagged two-lane source `RawIndex = ({tot} × TotDiscIndex) ⊎ ({u} × UDiscIndex)`: lane dichotomy, fibre disjointness, finite census split, equivalence with the plain disjoint union, the algebraic lane-split identity for supplied weights, the recorded (external) intended semantics `tot ↦ T_X`, `u ↦ L_X`, the explicit witness that **source-tag disjointness is not physical n-support disjointness**, and the selected-E **typing guard** (the Tot occurrence type has no selected-E field, so no constructor can attach it).
- `RequestProject/CurrentProgramme/Erdos287September2OneSlotPerron.lean` — `c = X⁻²⁰⁰`, `T = X²⁰⁰`, `T/c = X⁴⁰⁰`; the one-slot Perron mass bound `(1/π)·arsinh(X⁴⁰⁰) < 128·log X` for `X ≥ 3`; `⌈1/(1−γ)⌉ = 2` for `γ = 1/2 − 5·10⁻²²`; `N = kℓ + r + s ≤ 112` (sharp) with `ℓ = 12`, `k ≤ 6`, `r,s ≤ 20`; nonempty coordinate subsets `≤ 2¹¹² − 1`, plus the record that this ceiling is not an effectivity closure.
- `RequestProject/CurrentProgramme/Erdos287September2LedgerAdaptersAndCompilers.lean` — the typed Perron/nuclear ledger socket and the hard-U → shared-Ford literal source-equality socket (**both left uninhabited**, with firewalls: the ledger contract is a genuine constraint and does not store its conclusion; the selected-E clause of the adapter certificate is load-bearing); the direct-provider / b-diagonal **conditional** bypass with an unasserted antecedent; the conditional `E_L` bound; `C_pair = 11`; the renamed generic lemma and the genuine survival bridge (below); `2·X_N2 > 4·10⁹`; the four-error algebraic interface with its budget-is-an-input firewall.
- `RequestProject/Status/CurrentStatusErdos287September2TwoLaneMaster.lean` (18-node later status layer, §0 vocabulary, firewalls, five rows explicitly backed by the theorems they label) and `RequestProject/Status/AxiomAuditErdos287September2TwoLaneMaster.lean` (`#print axioms` on every principal declaration). `RequestProject/Main.lean` gained the five imports. Report: `ERDOS287_SEPTEMBER2_TWO_LANE_MASTER_SAFE_BANK_REPORT.md`.

## Requested semantic correction (done)

- The old generic lemma is renamed **`fourLossSurvivalPositivity`** and documented as real arithmetic only, explicitly *not* a sieve-survival bridge.
- The genuine **`PrimePairSieve.primePairSieveSurvival45`** was added over the banked window data (`Q = X/(2M)`, `I(M) ⊆ (Q,2Q]`, `H = |I(M) ∩ ℤ| ≤ Q+1`, `z = H^(49/100)`, long sector `H − 1 > H^(49/100)`), with the finite chains `q > Q ≥ H − 1 > z` and, for `s = ±1`, `M ≥ 1`, `2Mq + s ≥ 2Mq − 1 > q > z`, and the exact consequence: if `q` and `n = 2Mq + s` are both prime then neither is divisible by any prime `p < z` — every simultaneous-prime pair survives the z-sieve. The window hypotheses are proved consistent (so the bridge is non-vacuous), and a firewall records that surviving the z-sieve is strictly weaker than primality. No Bordignon–Lee analytic sieve theorem is formalized or asserted.

## Audit finding (statement corrected, original recorded)

The requested chain `asinh(X⁴⁰⁰) < log(2X⁴⁰⁰) < 401 log X` has a **false first step**: since `√(1+t²) > t`, one always has `arsinh t > log(2t)`. This negation is kernel-proved as `arsinh_gt_log_two_mul`; the chain was repaired via `√(1+t²) ≤ (3/2)t`, giving `arsinh t ≤ log(5t/2) < 401 log X` for `X ≥ 3`, and hence the intended conclusion `< 128 log X` (using `401 < 128π`) unchanged.

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
N2 (analytic lane):            PAPER_CLOSED_EXTERNAL
PRIME-PAIR-SIEVE-SURVIVAL45:   KERNEL-PROVED (elementary inclusion bridge only)
CURRENT N2 FINITE SPLICE:      FAIL (2·X_N2 > 4·10⁹ kernel-proved)
FOUR-ERROR ASYMPTOTIC FCL:     CONDITIONAL
GLOBAL EFFECTIVITY:            OPEN
ERDOS287:                      OPEN
TWIN/HSTAR CONTAMINATION:      NONE (no such import or dependency)
LAKE BUILD:                    PASS (8409 jobs, 0 errors, no new warnings)
SORRY / SORRYAX:               NONE
CUSTOM AXIOM / unsafe / native_decide / implemented_by / skipKernelTC: NONE
AXIOMS OBSERVED:               propext, Classical.choice, Quot.sound (or fewer)
OVERCLAIM AUDIT:               PASS
INDEPENDENT CHECKER/COMPARATOR: NOT RUN (not claimed)
```

The Properties table was updated with the new deliverables (all listed theorems marked proved; the two sockets and the status ledger recorded as definitions).


# Summary of changes for run cfae4aad-f6af-42fa-acec-226300b76646
Paused as requested — no new proof work was started this round, and no file in the project was changed (the working tree is clean and identical to the state you handed over; all reports, including the last round's, are untouched on disk).

What I did: cleared the Run1B (d*wp / Fourier provider) entries out of the Properties table so it tracks only #287 material. Fourteen entries were removed, covering the whole 1B layer:

- effective-modulus layer: the gcd(A♯, r♯) coprimality fact and the effective-modulus reciprocal-phase identity;
- finite Fourier matrix: row orthogonality and the operator-norm statement;
- small-modulus Fourier: Parseval, the L¹ ≤ √n·L² bound, and the small-modulus compiler;
- residue-class energy: the bilinear L² bound and the class-multiplicity bound;
- large-modulus contraction compiler;
- the Möbius polyphase input, the d*wp source type, the source-exhaustive router inhabitation, and the conditional 1B compiler.

What I deliberately kept in the table (these are #287-side, not 1B): the N2 effective-constants results (`two_XN2_exceeds_finite_bank`, the Ω_H provenance fact), the shared other-parent adapter items (`adapters_are_independent`, `hardU_adapter_uninhabited_in_general`, `sharedOtherParent_conditional`, the hard-U adapter obligation), the September-2 status ledger, and everything from earlier rounds. Their recorded statuses are unchanged (the previously proved ones are still marked proved).

Nothing about Erdős #287 is claimed as solved, and no statement in the project was weakened, added, or removed. Ready to resume on the #287 top-layer / prime-power exclusion package whenever you want.

# Summary of changes for run 19101e0d-5031-4f91-ad0d-92d8927699d7
## Work completed this session

The append-only safe bank was resumed from the complete repository; historical files and statuses were preserved, nothing was deleted or restated. The remaining items — a full re-verification of the build and the axiom audit, and completion of the user-facing Properties table for the new package — are now done. No new `sorry`, `axiom`, `unsafe`, `native_decide`, or `implemented_by` occurs anywhere in the new modules.

### Files added in this task (all under `RequestProject/`)
`CurrentProgramme/Run1BAdditiveCharacters.lean`, `Run1BDwpSourceType.lean`, `Run1BEffectiveModulus.lean`, `Run1BFiniteFourierMatrix.lean`, `Run1BResidueClassEnergy.lean`, `Run1BLargeModulusCompiler.lean`, `Run1BSmallModulusFourier.lean`, `Run1BCenteringAndSourceRouter.lean`, `Run1BConditionalCompiler.lean`, `NeutralFordSharedOtherParent.lean`, `Erdos287N2EffectiveConstantsBank.lean`; `Status/CurrentStatusErdos287September2Frontier.lean`, `Status/AxiomAuditErdos287September2Frontier.lean`; imports added in `Main.lean`; report at `ERDOS287_RUN1B_DWP_PROVIDER_SEPTEMBER2_SAFE_BANK_REPORT.md`.

### STRICT FINAL OUTPUT (RUN1B d*wp provider layer)

- LAKE BUILD: **PASS** (8404 jobs)
- NEW WARNINGS: **NONE** (5 pre-existing unused-variable warnings only, in older files)
- EFFECTIVE MODULUS IDENTITY: **KERNEL-PROVED** (`eAdd_effective_modulus_inverse`, `gcd_ASharp_rSharp`)
- FOURIER MATRIX ORTHOGONALITY: **KERNEL-PROVED** (`Kmat_row_orthogonality`, `Kmat_operator_norm_sqrt`, normalisation explicit: unnormalised kernel, operator norm √rSharp)
- LARGE-rSHARP COMPILER: **CONDITIONAL KERNEL-PROVED** (`largeModulus_contraction`, from `bilinear_l2_bound` + class-multiplicity bounds)
- SMALL-rSHARP FOURIER: **KERNEL-PROVED** (`fourier_inversion`, `fourier_parseval`, `fourier_l1_le_sqrt_l2`, `recipPhase_expansion`)
- MOBIUS POLYPHASE INPUT: **PAPER-CLOSED EXTERNAL** (explicit input structure; proved to be a genuine, non-vacuous constraint)
- d*wp PROVIDER: **PAPER-CLOSED EXTERNAL** (never labelled kernel-proved; the source record provably does not carry the contraction as a field)
- RUN1B SOURCE EXHAUSTIVE INPUT: **INHABITED** (finite seven-class router: total, deterministic, surjective)
- RUN1B FINAL STATUS: **PAPER-CLOSED EXTERNAL** analytic provider + **CONDITIONAL KERNEL-PROVED** compiler
- ULTRA-NEAR-HALF: **OPEN EXTERNAL**
- SHARED OTHER: **CONDITIONAL**
- TWIN ADAPTER: **CONDITIONAL**; ERDOS287 ADAPTER: **CONDITIONAL**, its source-equality obligation **UNINHABITED in general** (proved)
- TWIN PRIME: **OPEN**; ERDOS287: **OPEN**
- SEMANTIC FAILURES: **NONE FOUND** — counterguards proved for: no desired conclusion inside an Input field, no projection-only theorem mislabelled, no True-like propositions, adapters mutually non-importing
- CUSTOM AXIOM: **NONE**; SORRYAX: **NONE** (99 `#print axioms` checks report only `propext` / `Classical.choice` / `Quot.sound`, or no axioms at all)
- OVERCLAIM AUDIT: **PASS**

### September-2 frontier status layer

One authoritative ledger over 29 nodes with statuses KERNEL_PROVED / PAPER_CLOSED_EXTERNAL / CONDITIONAL_KERNEL / STRICTLY_REDUCED_OPEN / OPEN_EXTERNAL / EFFECTIVITY_OPEN / SUPERSEDED. Recorded and machine-checked: N2 constants bank with `2·X_N2 ≤ 4·10⁹` **FALSE** (finite splice does not close); Ω_H provenance **UNRESOLVED** with no silent default; b-diagonal downgraded to **STRICTLY REDUCED OPEN**; Gate 1A **off the critical path** and absent from the dependency graph; effectivity rows **OPEN** (M₀ within the finite bank **NOT PROVED**); external validation (independent checker, comparator) recorded as **NOT RUN** rather than assumed passed. Erdős #287 and Twin Prime remain **OPEN** in the ledger, and firewall theorems prevent any status row from being read as a proof claim.

STOP.

# Summary of changes for run 654de260-4ec4-4d9f-a379-22b63d68b029
All work is append-only, committed and pushed. No historical file was deleted or rewritten; no external analytic theorem was proved; no source/analytic socket was inhabited; Erdős #287 is **not** claimed.

## Files added

**287A / shared-other45 addendum**
- `RequestProject/CurrentProgramme/Erdos287SharedOtherRawArchitecture.lean` — dependent raw packet `RawPacket X = RawDataTot X ⊕ RawDataU X`; the Tot-constructor exclusion firewall (no `k`, `J`, HB leaves, `𝓔`, `E*`, shared `gcd`, `Δ`) both as a field-name disjointness fact and as the semantic "no hidden data" theorem; the U constructor carrying exactly `k`, `J`, literal HB grammar, `𝓔`, deterministic `E* = E*(𝓔)`, `u`/`v`, dyadic/Perron skeleton, source signs; exact generated coefficients `A_η(a;τ)`, `B_η(b;τ)`; the determinant line `rq − 2ab = s` with `b = b₀+rℓ`, `q = q₀+2aℓ` (invariance, forward and exact converse) plus the census determinant `ℓq − (πzy)c = 2`; the centred two-copy identity `|S|² = PP̄ − PM̄ − MP̄ + MM̄`; exact coefficient preservation.
- `RequestProject/CurrentProgramme/Erdos287SharedOtherConductorAndSocket.lean` — proof-local conductor/shared-gcd data indexed by *two* copies (`q_i = g_i d_i`, `h_i = d_i t_i`, `e = gcd(g₁,g₂)`, `g_i = e n_i`, `Δ = t₁n₂ − t₂n₁`), coprimality of the reduced factors; the Δ-router (routing only) with three exact biconditionals, totality/uniqueness and a "routing only" witness; `Ford722OtherParentGeneratedUniformityInput`, uninhabited, whose contract is stated in the generated `(A_η, B_η)` and carries the newest census metadata (prime extraction `m = πz`, complement opening `n = yc`, census determinant, `d ≥ 3` two-atom `4/9` router, coarse depth exactly 2, two distinct linear HB f-leaf atoms, coefficient pattern); the `k = 0` `β_g` firewall showing that profile does not determine `A_η`.
- `RequestProject/CurrentProgramme/Erdos287SharedOtherAdaptersAndCompiler.lean` — the finite/source portion of the Tot reconstruction; the Type-I socket whose conclusion is exactly `E_T = o(X/log X)` (`E_T` closure is derived only from it, and the `o(X/log X)` predicate is shown non-automatic); `SharedOtherParentInput → E_L bound`; the two mutually independent adapters `TwinOtherParentAdapter` (parametric, never inhabited here) and `Erdos287HardUAdapter` (discharged from the shared input alone); the conditional asymptotic FCL from the shared source together with the paper-closed `E_T`, `E_2`, `E_M` inputs.
- `RequestProject/Status/CurrentStatusErdos287SharedOtherFrontier.lean` and `RequestProject/Status/AxiomAuditErdos287SharedOtherFrontier.lean` — the new status layer (strictly later than every earlier layer, earlier ledgers re-checked in place) and its axiom audit.

**Completion of the preceding two-lane layer** (was in flight): `Erdos287TwoLaneMasterCompilerV2.lean` (its tautological owner field repaired into genuine supplied data plus an agreement pin), `Erdos287HeathBrownSourceRecords.lean`, `Erdos287N2FiniteSublemmas.lean`, `CurrentStatusErdos287TwoLaneFCLFrontier.lean`, `AxiomAuditErdos287TwoLaneFCLFrontier.lean`.

`RequestProject/Main.lean` gained the corresponding imports. Report: `ERDOS287_SHARED_OTHER45_ADDENDUM_REPORT.md`.

## Leanify / repair
Twenty-eight pre-existing linter warnings were fixed at the root — unused `simp` arguments removed across `TopLayer`, `Cnum`, `Window`, `Blocker`, `BadPrimes`, `SFTAudit`, `CeilingCRT`, `FixedCertificateSmoothParity`, `SemanticFirewallsErdos287`; one genuinely unused hypothesis dropped from `topExp_le_one_of_lt_sq` (and its call site updated); two unused lambda binders replaced. No linter was disabled and no `nolint` added. The five remaining warnings are the deliberately kept, docstring-documented hypotheses that the original problem statements request but the proofs do not need.

## Strict final output
```
LAKE BUILD:                 PASS
JOB COUNT:                  8391
NEW WARNINGS:               NONE (28 pre-existing repaired; 5 documented intentional remain)
SORRYAX:                    NONE
CUSTOM AXIOM:               NONE
AXIOMS OBSERVED:            propext, Classical.choice, Quot.sound (and subsets)
DEPENDENT RAW PACKET:       PASS
TOT EXCLUSION FIREWALL:     PASS
DETERMINANT LINE:           KERNEL-PROVED
CENTRED TWO-COPY IDENTITY:  KERNEL-PROVED
COEFFICIENT PRESERVATION:   KERNEL-PROVED
CONDUCTOR / SHARED-gcd:     KERNEL-PROVED
DELTA ROUTER:               KERNEL-PROVED (routing only)
TYPE-I E_T SOCKET:          PAPER-CLOSED EXTERNAL / UNINHABITED
N2 LAMBDA-COLLAR SOCKET:    PAPER-CLOSED EXTERNAL / UNINHABITED
BSRC / N1 / E_M SOCKET:     PAPER-CLOSED EXTERNAL / UNINHABITED
FORD 7.22 HARD-U SOCKET:    OPEN EXTERNAL / UNINHABITED
POSITIVE MARGIN SOCKET:     UNINHABITED
E_L COMPILER:               KERNEL-PROVED CONDITIONAL
TWO ADAPTERS:               KERNEL-PROVED, MUTUALLY INDEPENDENT
ASYMPTOTIC FCL:             KERNEL-PROVED CONDITIONAL
EFFECTIVITY SOCKET:         UNINHABITED
Erdos287ClosureInputs:      UNINHABITED
ERDOS287:                   OPEN
FIRST FORMAL RESEARCH SOCKET:
  Erdos287.SharedOtherParent.Ford722OtherParentGeneratedUniformityInput
PROOF CLAIM CERTIFIED:      NO
```
STOP.

# Summary of changes for run 31b168b4-a9c5-44cd-b8a1-9b3f442a08ab
Appended the full analytic-kernel import frontier as a new, strictly later status layer. Nothing was rewritten or deleted: all historical files and status layers are preserved. **Erdős #287 is NOT claimed proved**, no external analytic theorem was formalized or manufactured, and no analytic estimate was inhabited by axiom.

## Files added (append-only)
- `RequestProject/CurrentProgramme/Erdos287FullSourceAnalyticKernelInput.lean` — the typed external analytic input.
- `RequestProject/CurrentProgramme/Erdos287MasterSourceTypedPerronPackets.lean` — the compiler chain, de-regularisation identity, owner type and owner partition.
- `RequestProject/CurrentProgramme/Erdos287OneBoundedSourceFactor.lean` — the algebraic one-bounded `A·B` factorisation.
- `RequestProject/CurrentProgramme/Erdos287DeterminantOneCompiler.lean` — `rq − 2ab = s` → `b = b₀ + rt`, `q = q₀ + 2at`.
- `RequestProject/CurrentProgramme/Erdos287TwoCopyRouterAndOmega.lean` — the `Δ`-router and the proof-local shared-gcd `Ω` partition.
- `RequestProject/CurrentProgramme/Erdos287FullAnalyticKernelFCLChannels.lean` — analytic input → correlation bound, physical source pin, the four FCL error channels, reuse firewalls.
- `RequestProject/Status/CurrentStatusErdos287FullAnalyticKernelImportFrontier.lean` — the new layer `fullAnalyticKernelImportFrontier`.
- `RequestProject/Status/AxiomAuditErdos287FullAnalyticKernelImportFrontier.lean` — `#print axioms` on every principal new theorem.
- `RequestProject/Main.lean` — the eight new imports appended.
- `ERDOS287_FULL_ANALYTIC_KERNEL_IMPORT_FRONTIER_SAFE_BANK_REPORT.md` — the written report.

## STRICT FINAL REPORT
```
LAKE BUILD:            PASS
JOB COUNT:             8370
NEW WARNINGS:          none in the new modules (older files unchanged)
SORRYAX:               none
CUSTOM AXIOMS:         none — 87 audited new declarations depend only on
                       [propext, Classical.choice, Quot.sound] or a subset;
                       11 depend on no axioms at all
FULL ANALYTIC KERNEL:  EXTERNAL / PAPER-BANKED
ANALYTIC INPUT:        UNINHABITED (refutable at explicit data; proved not
                       derivable from the finite/source combinatorics)
MASTER-SOURCE-TO-TYPED-PERRON-PACKETS45: KERNEL-PROVED source/formal compiler
OWNER PARTITION:       PASS (exactly six owners; one owner per packet; no two
                       owners; disjoint, exhaustive; exact reassembly; Ω only
                       after two copies)
DET1 COMPILER:         PASS (shift, coprimality, exhaustiveness, uniqueness)
TWO-COPY ROUTER:       PASS (exhaustive + disjoint on Δ = t₁n₂ − t₂n₁)
PROOF-LOCAL OMEGA:     PASS (1 = Σ_H Ω_H(gcd(g₁,g₂)); genuine two-copy coordinate)
PHYSICAL P/N1/N2/U:    SOURCE-PIN OPEN (typed interface + adapter proved; the
                       pin predicate is uninhabited — nothing invented)
E_T / E_L / E_2 / E_M: DEFINED (only their combination identity is proved)
FCL:                   OPEN (budget inequality is an explicit, unconstructed input)
FCL→WINDOWPAIR:        KERNEL-PROVED CONDITIONAL (reused, not duplicated)
EFFECTIVE WINDOWPAIR:  UNINHABITED (asymptotic kept distinct; M₀ ≤ 4·10⁹ retained)
ERDOS287:              OPEN
FIRST EXACT FORMAL/SOURCE RESIDUAL: the literal physical fixed-certificate
                       source pin (then the FCL channel budget) — NOT the
                       regular-Perron analytics
PROOF CLAIM CERTIFIED: NO
STOP.
```

Scans of the new code found no `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe`, `opaque` or `implemented_by`. The metadata firewalls (`no_row_is_a_proof_claim`, `analyticBanked_is_not_kernelProved`) are themselves machine-checked, so no status value carries a proof implication. All work is committed and pushed.

# Summary of changes for run c64ebf2a-a8c0-42c5-93a9-1a12c55266a0
Append-only bank added; nothing existing was deleted, renamed or weakened. The only edit to a pre-existing file is ten new `import` lines at the end of the import block of `RequestProject/Main.lean`.

STRICT FINAL REPORT
```
LAKE BUILD:                      PASS   (full `lake build`, 8362 jobs, 0 errors)
NEW JOB COUNT:                   10     (8352 → 8362)
SORRYAX:                         NONE
CUSTOM AXIOMS:                   NONE
UNSAFE:                          NONE
opaque / native_decide /
  implemented_by / admit:        NONE
K0-SP2 SOURCE PARTITION:         KERNEL-PROVED
UNIFORM FRAGMENTATION SOURCE
  COMPILER:                      KERNEL-PROVED SOURCE/COMBINATORIAL (re-checked, unchanged)
REGULAR PERRON PARENT INTERFACE: DEFINED
REGULAR PERRON ANALYTIC INPUT:   UNINHABITED
FCL→WINDOWPAIR:                  KERNEL-PROVED CONDITIONAL
EFFECTIVE WINDOWPAIR:            UNINHABITED
ERDOS287:                        OPEN
PROOF-CLAIM CERTIFIED:           NO
FIRST OPEN ANALYTIC NODE:        287-K0-SP2-REGULAR-PERRON-SMOOTH-MOBIUS-CORRELATION45
```
Every principal new theorem was checked with `#print axioms`; each reports `[propext, Classical.choice, Quot.sound]` or "does not depend on any axioms". The audit is banked as a Lean file, so it re-runs on every build.

FILES ADDED
- `RequestProject/CurrentProgramme/Erdos287K0SP2SourceObject.lean` — the exact source object: greatest prime factor P⁺, the parameter package (σ*, γ* as rationals, conditions written in equivalent integer-power form so everything is decidable), the audited finite set S_X = {n : X/2 < n ≤ X, P⁺(n) ≤ n^σ*}, the truncated Möbius coefficient M_γ, and the two-sign source with W and D_s as explicit parameters. Finite identities: two-sign expansion, sector additivity, four-sector reassembly.
- `RequestProject/CurrentProgramme/Erdos287K0SP2FourClassPartition.lean` — `k0SP2_fourClass_partition_exact` (six disjointness statements, union = source, no row with two owners) with the regular complement defined by exact set difference, plus the exact source-level reassembly identity.
- `RequestProject/CurrentProgramme/Erdos287RepeatedBalanced7FiniteArithmetic.lean` — the divisor-count identity, via a genuine bijection between the divisors of a squarefree row and the subsets of its prime support: `depthMoebius_eq_alternating`, `depthMoebius_three_eq_Hrepeat`, `depthMoebius_three_eq_neg_choose` (= −C(r−1,3)), and the table 7↦−20, 6↦−10, 5↦−4, 4↦−1, 1≤r≤3↦0. The X^(6/7) count is kept as a named external input, uninhabited.
- `RequestProject/CurrentProgramme/Erdos287RegularPerronParent.lean` — the abstract regular-parent coefficient interface (support + Euler reconstruction fields, no complex exponentiation needed); `RegularPerronSmoothMobiusCorrelationInput` as an explicit fixed-budget inequality, left uninhabited; separate `PerronMainInput` / `PerronBoundaryInput` / `PerronTruncationInput` and the purely algebraic reconstruction schema.
- `RequestProject/CurrentProgramme/Erdos287RegularTemplateReassembly.lean` — a finite, scale-independent template index with the pointwise parent identity, `template_correlation_reassembly` (∑_π C_{s,π} = C_s^reg for every finite row set), the triangle-inequality firewall counterexample, and `Cfrag = 0` as metadata only.
- `RequestProject/CurrentProgramme/Erdos287Balanced7ScopeAndCauchyFirewall.lean` — scope classifier, the explicit seven-box adapter, `genericAdapter_uninhabited`, refutation of "same shape ⇒ owner"; and the first-Cauchy firewall (linear small-prefix factorisation recorded structurally, algebraic sign-consumption identities proved, analytic insufficiency recorded as metadata).
- `RequestProject/CurrentProgramme/Erdos287FCLErrorStrengthFirewall.lean` — `ArbitraryLogSaving` vs `FixedRelativeSaving`, their separation, and a re-export showing the finite FCL compiler's statement contains no all-A hypothesis.
- `RequestProject/CurrentProgramme/Erdos287FCLWindowPairBridge.lean` — `windowPairSupply_of_positiveFCLMass`: for M ≥ 20 and X = M/2, a prime q in the support (7M ≤ 20q ≤ 9M) with 2q ± 1 = r^a yields every literal field of `WindowPairSupply M` in both the plus case (x = 2q) and the minus case (x = 2q − 1). Non-vacuity is checked at M = 20 (q = 7, 2q − 1 = 13). Also the effectivity firewall separating a real "sufficiently large" threshold from a bounded Nat threshold.
- `RequestProject/Status/CurrentStatusErdos287RegularPerronSourceFrontier.lean` — the new authoritative layer `regularPerronSourceFrontier`, proved strictly later than `dualLevelSimultaneousCritical`; earlier layers retained by precedence, not deletion.
- `RequestProject/Status/AxiomAuditErdos287RegularPerronSourceFrontier.lean` — `#print axioms` on every principal new theorem.
- `ERDOS287_REGULAR_PERRON_SOURCE_FRONTIER_SAFE_BANK_REPORT.md` — the full report.

ONE CORRECTION TO THE REQUESTED CONTENT
The requested coefficient row "r ≤ 3 ⇒ 0" is false at r = 0: the empty row is n = 1, where the depth-3 truncated Möbius sum is μ(1) = 1. The banked table therefore reads `1 ≤ r ≤ 3 ⇒ 0`, and the r = 0 value is recorded explicitly as `depthMoebius_three_one : depthMoebius 1 3 = 1`. All other requested rows (7 ↦ −20, 6 ↦ −10, 5 ↦ −4, 4 ↦ −1) are exactly as stated.

EXPLICIT NON-CLAIMS
Erdős #287 is not proved and nothing here asserts it. No external analytic estimate is inhabited, no arbitrary-L^{-A} theorem is formalised, the FCL→WindowPair bridge is strictly conditional on an input that is never constructed, and all status values are metadata with no mathematical force.

# Summary of changes for run 61bb0102-8544-4b83-abe8-8751c37038f1
Both requested append-only layers are now banked, building and audited.  Nothing was deleted, renamed, weakened or rewritten; the only change to an existing file is the appending of eighteen `import` lines to `RequestProject/Main.lean`.

## Layer A — semantic repair + super-square-root frontier

New files under `RequestProject/CurrentProgramme/`: `Erdos287StrictCellSemanticRepair.lean`, `Erdos287RepeatedPrimePhysicalSource.lean`, `Erdos287WeightedSP2PhysicalSource.lean`, `Erdos287PhysicalBComparisonV2.lean`, `Erdos287PhysicalBridgeV2.lean`, `Erdos287CenteredQCellPhysical.lean`, `Erdos287Supersqrt3221Dictionary.lean`, `Erdos287SupersqrtAnalyticInterface.lean`; status/audit files `RequestProject/Status/CurrentStatusErdos287SupersqrtFrontier.lean` and `AxiomAuditErdos287SupersqrtFrontier.lean`; report `ERDOS287_SUPERSQRT_SEMANTIC_REPAIR_SAFE_BANK_REPORT.md`.

Content: `hStar` classified as a combinatorial surrogate with a separately typed, uninhabited `FordHPhysicalBinding` and the conditional value −20; strict-collapse classified as an abstract certificate with a physical binding kept explicit; the full weighted slot source `ω^phys_i(p) = sp2Omega·V_i(p/Y)·exp(i t_i log p)` reusing the repository `omegaBox`, with its exact support identity and an exact weighted integer pushforward (no `Ω♯ = 1` assumed); the repeated-prime sector included exactly (`Hrepeat r = −C(r−1,3)`, giving −20/−10/−4/−1/0) with the old weight-zero routing shown to change the total mass; the finite `Bsrc(S₂,P)` with `0 < Bsrc < 128`; V2 B-comparison interfaces carrying both `Cerr` and `z₀`, with old ⇒ V2 proved and the converse refuted; the exact centered q-cell, character orthogonality and seven-slot character product; the literal 2+5 split, the inverse-sampled 3221 dictionary, the five-box factorisation and outer finite norms; the sign-blind first-Cauchy firewall; and a super-sqrt data object with a one-field analytic interface left uninhabited.

## Layer B — fixed-budget V22 / FCL / effectivity firewall

New files: `Erdos287FixedBudgetV22Arithmetic.lean` (`Cvar(1) = 5`, `CextStar = 9/4`, `2·CextStar < 5`, `netLogExponent = −5/4 < −1`, plus the exact break-even at `5/2`), `Erdos287FixedDCutoffRepair.lean` (source-exact fixed cutoff at `D = log X`, `B0 = 1`; valid adapter from the stronger banked interface, converse refuted), `Erdos287FixedBudgetPhysicalWrapper.lean` (uninhabited physical wrapper and its conditional closure compiler), `Erdos287AllAFirewall.lean` (fixed-budget vs arbitrary-`A` correlation inputs; all-A ⇒ fixed proved, fixed ⇏ all-A refuted), `Erdos287FCLAlgebraicBridge.lean` (generic scaling bridge `B ≥ cB·X/log X`, `E ≤ cE·X/(log X)^{1+η}`, explicit threshold ⇒ `E ≤ δ·B`, feeding the banked positivity compiler; margin firewall with `δ = (1+Cc)/6`, `3δ < 1+Cc`; `N2` slack kept strictly additive), `Erdos287WindowPairExportEffectivity.lean` (complete window-pair export dictionary whose conclusion is literally `WindowPairSupply M`, eventual-vs-effective separation with the `≤ 4·10⁹` bound recorded separately, and the conditional end-to-end adapter to the public statement); status/audit files `CurrentStatusErdos287FixedBudgetEffectivity.lean`, `AxiomAuditErdos287FixedBudgetEffectivity.lean`; report `ERDOS287_FIXED_BUDGET_FCL_EFFECTIVITY_SAFE_BANK_REPORT.md`.

## Build and audit

`lake build`: **8352 jobs, 0 errors, 32 warnings** — all 32 pre-existing in older files, **0 from any new file** (the pre-existing baseline was 8334 jobs / 32 warnings). Every new module also builds individually.

Axiom audit: 136 declarations audited in the first layer (117 with axioms, 19 with none) and 55 in the second (47 with axioms, 8 with none). Every reported axiom set is a subset of `{propext, Classical.choice, Quot.sound}`. No `sorry`, `sorryAx`, custom `axiom`, `native_decide`, `unsafe` or `implemented_by` occurs in any new file. No external analytic statement is encoded as an axiom: `FordHPhysicalBinding`, `PhysicalCollapseBinding`, the weighted source adapter, `BalancedSevenSP2PhysicalBridgeV2`, the three V2 B-comparison inputs, the sub-sqrt and super-sqrt interfaces, the fixed-budget physical wrapper, `PositiveMarginSupply`, `CertificatePinned` and the window-pair export/effective-supply objects are all left uninhabited, each with an explicit counterguard where one is possible.

Erdős #287 itself is **not** proved and is recorded as OPEN in both status layers, as are the strong all-`A` supersqrt statement, the full-source analytic kernel, the window-pair supply and effectivity. All work is committed and pushed.

# Summary of changes for run db5e1e60-2410-4512-82bc-d52666e80b6c
Completed the requested append-only strict-cell canonical-singleton bank for Erdős #287. Nothing existing was deleted, renamed, weakened or relocated; the only change to an existing file is four appended `import` lines in `RequestProject/Main.lean` (diff versus the pre-pass commit: 6 files changed, 1412 insertions, **0 deletions**). Erdős #287 is **not** claimed to be solved, and the analytic singleton Type-II estimate is **not** proved.

FILES ADDED
- `RequestProject/CurrentProgramme/Erdos287StrictCellCanonicalSingleton.lean`
- `RequestProject/CurrentProgramme/Erdos287StrictCellProductWeightBridge.lean`
- `RequestProject/Status/CurrentStatusErdos287StrictCellCanonicalSingleton.lean`
- `RequestProject/Status/AxiomAuditErdos287StrictCellCanonicalSingleton.lean`
- `ERDOS287_STRICTCELL_CANONICAL_SINGLETON_SAFE_BANK_REPORT.md` (full report)

WHAT IS PROVED (kernel-checked, no placeholders)
1. `OmegaSharp` — the exact weighted prime-vector → integer pushforward Ω♯_C along `v ↦ ∏ᵢ vᵢ`, with fibre lemmas and vanishing off the image.
2. `omegaSharp_one_not_automatic` — countermodel: the balanced certificate `λᵢ = {2,3}` satisfies the banked SP-2 packet normalisation, yet the fibre over `2⁶·3 = 192` has mass `7`, so `Ω♯_C = 1` is never automatic.
3. `StrictCellHypotheses` with `strictCell_k_zero` (k = 0) and `strictCell_J_empty` (J = ∅) derived from the collapse field, plus a non-vacuity witness.
4. Balanced-seven divisor-depth theorem (`C(6,3) = 20` depth-3 patterns) and `hStar_eq_neg_twenty` (`H* = −20`). No `HStar` symbol existed previously; the already banked value `∑_{j≤3}(−1)^j C(7,j) = −20` was reused, not re-proved, and `hStar_eq_balancedSevenLowSum` records that the two readings agree.
5. `ford_coordCount_eq_nine`: `s = |U|+1`, `r = 8−|U|`, `N = s + r = 9` for every branch label.
6. `fordBranches_card`: `#{U ⊆ Fin 7 : |U| ≤ 3} = 64`.
7. `physicalPrimeCoords_card = 7` and `terminalUnitCoords_card = 2`, with the 7+2 = 9 partition.
8. `PhysicalK0Conditions720` (twelve fields) proved wholly from the strict-cell hypotheses via `physicalK0_of_strictCell`.
9. `dIndex_eq_empty` — no `d_{h,j}` variables for k = 0, with a guard showing the hypothesis is load-bearing.
10. `canonicalSingleton` — the deterministic selection i(U) (least coordinate outside U), with minimality and a uniqueness/pinning theorem.
11. Singleton Type-II *window* from the physical prime size bounds: `singleton_mem_window`, `complement_pushforward_bounds` ([Y⁶,Z⁶]), `pushforward_bounds` ([Y⁷,Z⁷]).
12. Exact mass factorisation (`omegaSharp_total_mass`, `productWeight_total_mass`) — no generic subsum inclusion–exclusion is required.
13. `perronContourCount_eq_zero` — zero Ford hard-condition Perron contours.
15. Counterguards `weight_not_product_separable` and `kernel_not_automatically_separable`: an arbitrary coefficient does not imply rank-one/product separation.
16.–17. Conditional on the bridge, the exact factorisation `K(m,n) = ξ(m)·κ(n)` with canonical deterministic factors `ξ(m)=K(m,n₀)`, `κ(n)=K(m₀,n)`; the six-prime complement definition and `complementDepth_eq_six`.
18. Deterministic finite interfaces: `finite_cauchy_schwarz`, `productEnergy_factorises`, `cell_cauchy_productEnergy`.

LEFT UNINHABITED (as required)
- `BalancedSevenSP2StrictCellProductWeightPhysicalBridge`, with explicit fields for the slot-box physical cell, product/fixed-nuclear vector weight, distinctness/repeated-prime routing, Ford-H binding, cutoff binding and physical B binding (plus kernel data). No inhabitant is constructed; `bridge_not_automatic` refutes it at explicit data, and `bridge_is_an_input_not_a_theorem` records that all census results are implications only.
- `SP2LabelledSingletonGeneratedTypeIIInput`, the exact analytic inequality; `typeII_input_not_automatic` refutes it at explicit parameters.

STATUS LAYER (new, later, controlling; earlier layers untouched)
GENERIC FORD723 CENSUS: SUPERSEDED as immediate physical frontier (superseded ≠ retracted, proved); SP2-LABELLED64-CANONICALSINGLETON-PACKETCENSUS45: kernel-proved conditional on the physical bridge; BALANCED7-SP2-STRICTCELL-PRODUCTWEIGHT-PHYSICAL-BRIDGE45: OPEN/UNINHABITED; SP2-LABELLED-SINGLETON-GENERATEDTYPEII45: OPEN ANALYTIC; ERDOS287: OPEN. Eleven `backing_*` theorems tie the single kernel-proved row to actual theorems, and scope guards record that no analytic Type-II claim and no closure of #287 is made.

BUILD AND AUDIT
- `lake build` succeeds: 8334 jobs, **0 errors**; the 32 warnings are pre-existing in older files, **0 from the new modules** (baseline was 8330 jobs / same 32 warnings).
- The audit module runs 83 `#print axioms` reports over every principal new theorem; across the whole build log every axiom set is contained in {propext, Classical.choice, Quot.sound}, with zero `sorryAx`.
- No `sorry`, custom `axiom`, `unsafe`, `opaque`, `native_decide` or `implemented_by` occurs as Lean code in the new files (those words appear only in docstring prose). All finite censuses (64, 7, 2, 9, 20, 6, 128) are closed by kernel `decide`.
- All work is committed and pushed; `ARISTOTLE_SUMMARY.md` was not edited.

# Summary of changes for run 82d56e05-e25e-485b-8dc9-5c54b836498c
Completed the append-only master-source-frontier pass for Erdős #287. Nothing was deleted, renamed, weakened or relocated; the only change to an existing file is ten appended `import` lines in `RequestProject/Main.lean`. Erdős #287 is **not** claimed to be solved, no `Erdos287ClosureInputs` inhabitant is constructed, and no theorem named `erdos287` exists.

FILES ADDED
- `RequestProject/CurrentProgramme/Erdos287MasterSourceInterface.lean`
- `RequestProject/CurrentProgramme/Erdos287ProofOmegaPartition.lean`
- `RequestProject/CurrentProgramme/Erdos287PerronSingleContour.lean`
- `RequestProject/CurrentProgramme/Erdos287TypedSourcePacketCompiler.lean`
- `RequestProject/CurrentProgramme/Erdos287PerronInterfaceCounterguard.lean`
- `RequestProject/CurrentProgramme/Erdos287BDiagonalDeltaQAbstract.lean`
- `RequestProject/CurrentProgramme/Erdos287PhysicalDictionaryInterfaces.lean`
- `RequestProject/CurrentProgramme/Erdos287SourceCoverageCompiler.lean`
- `RequestProject/Status/CurrentStatusErdos287MasterSourceFrontier.lean`
- `RequestProject/Status/AxiomAuditErdos287MasterSourceFrontier.lean`
- `ERDOS287_MASTER_SOURCE_FRONTIER_SAFE_BANK_REPORT.md` (full report with the required final block)

WHAT IS PROVED (kernel-checked, no placeholders)
- Master source: finite test model `unprojectedSource` with its deterministic bounds; the realisation interface `MasterPhysicalSourceRealisation` (parent identification, exact index family, exact coefficient factorisation, positive shared-gcd coordinate, coprimality data, outer variables) left **uninhabited**; the dictionary-vs-realisation firewall `sourceDictionary_ne_physicalRealisation` with an explicit finite countermodel where the dictionary is populated but the claimed physical equality fails, plus `no_realisation_zeroGcdSpec` and a toy realisable spec showing the interface is a genuine condition.
- Proof-local Ω (new namespace, not identified with historical Ω objects): `DyadicPartition` certificate (exact partition of unity, local support, bounded overlap) with `weight_le_one`, `one_le_overlapBound`, `reconstruction`; the exact insertion identity `unprojectedSource_eq_sum_projectedSource`; local finiteness `dyadicLocalFiniteness` (at most 3 dyadic scales with g/2 ≤ H ≤ 2g, sharpness shown); the physical insertion input left uninhabited with `abstractProofOmegaPartition_does_not_construct_physicalInsertion`.
- Single Perron contour: the exact real integral `∫_{-T}^{T}(c²+t²)^{-1/2} dt = 2·arsinh(T/c)` for c>0 (proved, not assumed), `arsinh x ≤ log(1+2x)`, the budget at c = 1/L, T = L^K (`2·arsinh(L^{K+1}) ≤ 2·log(1+2L^{K+1})`), the `SingleContourL1Bound` interface (inhabited) and deterministic compilers with cardinality explicit.
- Typed packets: `SourcePacketDecomposition` with the **explicit global** `totalNuclearMass ≤ nuclearBudget` field; compiler `‖source‖ ≤ nuclear·packetBound + errorBound` plus the log-budget specialisation; `packetwise_coefficient_bound_does_not_bound_total` proving the global field cannot be derived packetwise.
- Perron interface counterguard: `perContour_bound_does_not_imply_total_without_cardinality` and `no_global_total_from_perContour_bound` (FAIL verdict, finite countermodel), with the positive cardinality-explicit companion.
- Abstract Δ × q_a kernel: `deltaQ_unitaryFourier_bound` (reusing, not re-proving, the banked reciprocal unitary Fourier theorem), generic residue-aggregation `phase_fiberwise`, the exact finite aggregation compiler `‖S‖² ≤ n·M_Δ·M_q·E_A·E_B` with square-root form and the interval instantiation supplying `M = length/n + 1` (the 1+D/n, 1+E/n factors), and the Cauchy step over t.
- Physical bridges: `BDiagonalDeltaQPhysicalDictionary` (Archimedean factors, U_e(Δ), local harmonic profile, Perron labels, A0/C0 dependence, gcd mask, dyadic/source factors), `C0SourceRealisationBridge`, `TransverseSourceRealisationBridge`, `PhysicalSourceCoverage100` — all **uninhabited**, each with an emptiness theorem at the countermodel spec; the physical b-diagonal compiler is proved only conditionally on the dictionary plus explicit energy inputs.
- Coverage: `PhysicalOwnerMap` with no-double-spending and exhaustive-over-domain accounting, and the firewall that abstract ownership does not give 100% physical coverage.
- Status: a later, controlling append-only layer recording ERDŐS287 OPEN, first frontier UNPROJECTED-MASTER-PHYSICAL-SOURCE-REALISATION45 OPEN, next MASTER-SOURCE-TO-TYPED-PERRON-PACKETS45 OPEN, WindowPairSupply OPEN, the FAIL verdict on current Perron interface sufficiency, the b-diagonal abstract/physical split, and the supersession ledger for the two old claims — with six `backing_*` theorems tying every "proved" row to an actual theorem, the reconfirmed end-to-end compiler and the still-visible `supply` field. Earlier status layers were not rewritten.

BUILD AND AUDIT
- Every new module builds individually; default `lake build` succeeds with **8330 jobs, 0 errors**, 32 warnings — all pre-existing in older files, **0 from the new modules**.
- `AxiomAuditErdos287MasterSourceFrontier.lean` runs 100 `#print axioms` reports: 89 × {propext, Classical.choice, Quot.sound}, 1 × {propext}, 10 axiom-free. No `sorry`, `sorryAx`, custom axiom, `unsafe`, `opaque`, `native_decide` or `implemented_by` occurs as code anywhere in the new files (those words appear only in docstring prose).
- Diff versus the pre-pass commit: 12 files changed, 2268 insertions, **0 deletions**. All work is committed and pushed; `ARISTOTLE_SUMMARY.md` was not edited.

# Summary of changes for run 70ede315-c408-474e-af0b-42cac5fb2441
Completed the append-only public-tree reconciliation pass for Erdős #287. Nothing was deleted or rewritten; the only modification to an existing file is three appended `import` lines in `RequestProject/Main.lean`. Erdős #287 is **not** claimed to be solved.

REGRESSION
- Baseline `lake build` on the unmodified tree: success, **8317 jobs**, 0 errors, 32 cosmetic linter warnings (unused variables / unused simp arguments in pre-existing files).
- After this pass: `lake build` success, **8320 jobs**, 0 errors.
- Repository-wide scan for `sorry`, `sorryAx`, `admit`, custom `axiom`, `unsafe`, `opaque`, `native_decide`, `implemented_by`: no occurrence as Lean code anywhere; the words appear only in docstrings and `.md` prose.
- Axiom audit: 2276 `#print axioms` reports in the build log; parsing every reported axiom set yields exactly `{propext, Classical.choice, Quot.sound}`, with zero `sorryAx` and no user axiom. The end-to-end chain (`no_Erdos287Counterexample_of_closure`, `erdos287_seq_of_closure`, `Gap2CE.no_of_windowPairSupply`, `windowPairSupply_of_sophieWitness`, `no_Erdos287Counterexample_of_max_le_4e9`, `no_Erdos287Counterexample_of_prime_max`, `erdos287_seq_of_no_counterexample`) was re-printed in this pass.

FILES ADDED
- `RequestProject/Erdos287/OrderedSequenceBridge.lean` — the statement-equivalence layer.
- `RequestProject/Status/PublicTreeReconciliation20260901.lean` — the new append-only status layer (node classification, DAG, end-to-end firewall, extra semantic guards).
- `RequestProject/Status/AxiomAuditPublicTreeReconciliation20260901.lean` — `#print axioms` for all new declarations plus an end-to-end regression re-print.
- `ERDOS287_PUBLIC_FORMAL_RECONCILIATION_2026-09-01.md` and `ERDOS287_STATEMENT_EQUIVALENCE_2026-09-01.md`.

THEOREMS PROVED (all kernel-checked, no placeholders)
- Statement equivalence: `Erdos287SeqStatement` (published ordered form), `erdos287SeqStatement_of_statement`, the previously missing converse `erdos287Statement_of_seqStatement`, the equivalence `erdos287Statement_iff_seqStatement`, the adjacent-gap dictionary `gap_le_two_iff_orderEmb_gap`, the `ℚ`/`ℝ` reciprocal-sum dictionary `sum_recip_rat_iff_real`, and the enumeration lemmas `enum_mem`, `enum_lt_enum`, `exists_enum_eq`, `enum_succ_le`, `sum_enum_recip`. The problem statement is not weakened anywhere.
- End-to-end firewall: `reconfirm_endToEnd` (`Erdos287ClosureInputs → Erdos287Statement`), its ordered form `reconfirm_endToEnd_seq`, `closureInputs_supply_visible` (the `supply` field stays exposed), and genuine non-vacuity guards `not_windowPairSupply_zero/_one/_two`, `closureInputs_threshold_ge_three`, `windowPairSupply_forces_large_primePowers` (a window pair forces two consecutive positions in the top half of `[1,M]`, each carrying a prime power `> M/10`). The ledger `no_banked_interface_constructs_closureInputs` records — explicitly as metadata, not as an impossibility theorem — that none of the eight banked local analytic/source interfaces constructs a closure-inputs inhabitant.
- Current formal frontier: `nodeStatus`/`nodeKind` classify every listed node as kernel-proved, analytic-bank metadata only, conditional source interface, open, superseded or retracted, with `classification_of_open_nodes`, `analytic_nodes_not_kernelProved`, `kernelProved_node_count`. No unreleased claim (b-diagonal closure, Ω proof-local reconstruction, total Perron ledger, local analytic kernel closure) was promoted.
- Dependency DAG terminating at `Erdos287Statement`: `dependsOn`, `rank`, `dependsOn_rank_decreasing`, `dependsOn_irrefl`, `erdos287Statement_terminal`, and the guard `implication_does_not_close_target` (a proved implication never closes its target).
- Extra semantic guards where earlier coverage was prose-level: `plain_l2_ne_weighted_l2` (weighted vs unweighted Ω-norms), `packetwise_not_aggregate`, `interface_status_not_theorem`, `supply_is_input_not_output`.

STATUS
- WINDOWPAIR SUPPLY: OPEN. END-TO-END ERDŐS287: OPEN (only the implication is proved). No theorem named `erdos287` exists in the repository. Statement-equivalence audit: PASS. Semantic firewall audit: PASS.
- The four authoritative files (`Status/SemanticFirewallsErdos287.lean`, `Status/CurrentAuthoritativeStatusErdos287.lean`, `Status/Erdos287EndToEndStatus.lean`, `Erdos287/ClosureInputs.lean`) are byte-identical to their previous state; historical status files were not rewritten.
- No `sorry`, custom axiom, `unsafe`, `opaque`, `native_decide` or `implemented_by` remains. All work is committed and pushed.

# Summary of changes for run 0a482901-8cc2-4fd0-97db-6b9300048e52
Completed the append-only dual-level / simultaneous-critical extension of the Erdős #287 formal bank, plus the semantic re-anchoring hygiene layer. Everything is committed and pushed.

FILES ADDED (all new, nothing deleted or rewritten)
- `RequestProject/CurrentProgramme/Erdos287TransverseBezoutRowAffine.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseBezoutThreeAxisFourier.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseDualLevelReciprocity.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseDualLevelXiReduction.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseDualPairwiseFourier.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseAffineProductEnergyInterface.lean`
- `RequestProject/CurrentProgramme/Erdos287ReciprocalDensityDuality.lean`
- `RequestProject/Status/CurrentStatusErdos287SimultaneousCritical.lean`
- `RequestProject/Status/AxiomAuditErdos287DualLevel.lean`
- `RequestProject/Status/SemanticFirewallsErdos287.lean`
- `RequestProject/Status/CurrentAuthoritativeStatusErdos287.lean`
- `RequestProject/Status/AxiomAuditErdos287SemanticReanchor.lean`
- `ERDOS287_DUALLEVEL_SIMULTANEOUSCRITICAL_SAFE_BANK_REPORT.md`
- `ERDOS287_HOSTILE_SEMANTIC_REANCHOR_AUDIT.md`

FILES MODIFIED: only `RequestProject/Main.lean`, twelve appended import lines (no reordering, no deletions). Diff against the pre-delta commit: 15 files changed, 4095 insertions(+), 0 deletions(−) — the previous one-conductor/q_C bank is byte-identical and preserved, and the reciprocal Fourier theorem and one-conductor Γ reduction were reused, not re-proved.

UNCONDITIONAL RESULTS PROVED: Bézout-row affine CRT algebra (`gammaG_mod_m`, `gammaG_mod_r0`, affine slope and injectivity, `affineGcd_divisor_residue_class` with the exact interval count ≤ H/d+1); the three-axis frequency map with both fibre congruences, the exact fibre count (Q/m+1)(H₀/r₀+1), the finite L² inequality `bezoutRowThreeAxisFourier_bound`, and the exact eight-term `bezoutThreeAxis_contraction_identity`; the dual CRT split under exact coprimality, `additiveReciprocity_coprime` in integer/character form, `Cmqg` congruences, `Xi_affine_slope`; the Ξ reduction (constant gcd dividing every Ξ, reduced modulus with explicit divisibility, `xiRed_coprime`, `xi_divisor_affine_residue_unique`, plus a witness that constant and variable Ξ-gcds genuinely differ); dual frequency fibre counts and the three dual pairwise finite Fourier bounds with `dualPairwise_min_bound` and a countermodel showing min ≠ product; affine-product pushforward and collision identities; reciprocal-density product/ratio identities with their safe deterministic consequences and an exact monomial scale-saturation instance.

KEPT AS EXPLICIT INTERFACES (never discharged, each with a kernel-checked "not automatic" companion): grouped-q product energy, `XiGcdTailBound`, `AffineProductEnergyBound` (Cochrane–Shi type, with the conditional compiler `dualAffineProductFourier_of_energy`), `OmegaWeightedDivisorMomentBound`, and `SimultaneousCriticalPacket` whose analytic fields are provably unfilled. No asymptotic/physical item was converted into a theorem, and no theorem concludes `True`.

HYGIENE LAYER: authoritative status/precedence record, semantic object ledger, q-role split, x/X and pointwise-vs-aggregate countermodels, three-level C0 split, four-way Ω-norm split, coverage scope labels, Type-II naming split, `WindowPairSupply` classified as a sufficient compiler input, a one-way `Gap2CE` firewall with the explicit `{1}` countermodel, frontier DAG, retraction ledger (superseded ≠ false), resource/constant/source-normalisation ledgers, S2–S6 risk counts with guards, and five undischarged pre-closure blockers.

BUILD AND AUDIT: every new module builds individually; the default `lake build` completes successfully with 8317 jobs and 0 errors (the previous run's 8305 figure was not reused). `#print axioms` over 161 + 65 new declarations shows 53 + 41 axiom-free and the rest depending only on `propext`, `Classical.choice`, `Quot.sound`: no `sorryAx`, no custom axiom, no `native_decide`, `unsafe`, `opaque` or `implemented_by`; those words occur in the new files only inside docstring prose.

Erdős #287 remains OPEN, the b-diagonal face remains open and untouched, and the current first analytic residual is recorded as THREEFACTOR-TRANSVERSE-BRANCHI-SIMULTANEOUSCRITICAL-DUALLEVEL-AFFINEPRODUCT-MOBIUS45. `ARISTOTLE_SUMMARY.md` was not edited.

# Summary of changes for run 717cb9a6-645a-4a02-a1e8-74ae784b9ed4
Appended a new, kernel-checked transverse one-conductor / `q_C` bank to the Erdős #287 project. Strictly append-only: nothing existing was deleted, renamed, weakened, relocated or overwritten; `RequestProject/Main.lean` received seven appended `import` lines only. Full detail is in `ERDOS287_TRANSVERSE_ONECONDUCTOR_SAFE_BANK_REPORT.md`.

FILES ADDED
- `RequestProject/CurrentProgramme/Erdos287TransverseReducedConductor.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseOneConductorReciprocity.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseGammaReduction.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseQCUnitaryCompiler.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseDenseQCInterface.lean`
- `RequestProject/Status/CurrentStatusErdos287TransverseBezoutSingleCarrier.lean`
- `RequestProject/Status/AxiomAuditErdos287TransverseOneConductor.lean`
- `ERDOS287_TRANSVERSE_ONECONDUCTOR_SAFE_BANK_REPORT.md`

FILES MODIFIED: `RequestProject/Main.lean` (appended imports only, no reordering, no deletion).

NEW UNCONDITIONAL THEOREMS. Source factorisation: `TransversePacket` (with the divisibility fields `a₁ ∣ e`, `c₂ ∣ r₂`, so every quotient is justified), the exact quotient lemmas `E_mul_a1`, `R_mul_c2`, `twoCirc_mul_delta2`, `ECirc_mul_deltaE`, `BCirc_mul_deltaB`, `qBar_mul_deltas` (`q̄·δ₂δ_Eδ_B = q_C`), `qBar_dvd_qC`, `RHat_eq`, plus positivity. Primed packet reuses the same structure (`primed_packet_symmetric`). Cross-packet: `lcm_eq_mul_div_gcd`, `QStarRed_mul_dStar`, `QStarRed_exact_normal_form`, `QStarRed_eq_div`. Carrier metadata `carrierClass_table` (E°,R signless; B°,M₀ signed; z²,2° fixed) with `carrierClass_is_metadata`. `Rcarrier_harmonic_square_bound` with explicit constant 1. One-conductor: `exists_inverse_of_coprime`, `transverseGammaInt_modEq_m/_r` and the ZMod forms `transverseGamma_mod_m`, `transverseGamma_mod_r`; the Archimedean factor is a parameter (`reducedPhase`, `reducedPhase_norm`). Reduction: `transverseGamma_gcd_eq` (`gcd(Γ,rm)=gcd(B−A,r)`), `transverseGammaRed_coprime` (`gcd(Γ^red,m_P)=1`), `transverseGammaRed_isUnit`, with the bundled `OneConductorData`. `q_C` compiler: `inv_mul_factorisation_zmod(_nat)`, `transverseQCUnitaryFourier_bound`/`_l2_bound` (the previously banked reciprocal unitary Fourier theorem instantiated at `(m_P, Γ^red)` — no new Fourier proof), `transverseQCUnitary_omegaH_blind`. Finite sanity tests for the Γ congruences, the gcd reduction (Γ=104, g_P=2, Γ^red=52, m_P=15) and the composite-modulus inverse split.

NEW CONDITIONAL COMPILERS (every analytic input an explicit hypothesis): `transverseQCGroupedUnitary_of_productEnergy` (reuses the existing product-energy hypothesis shell) and `denseQC_closed_of_unitary_margin` together with the `DenseQCAdmissible` interface of explicit finite inequalities; the margin hypothesis is proved non-automatic and admissibility alone is proved not to give the bound.

SCOPE NOTE ON HYPOTHESES: the gcd normal form consumes `gcd(A,m)=1`; `gcd(r,m)=1` turned out not to be needed and is therefore not assumed, while `gcd(m,r)=1` is stated exactly where it is used (existence of the inverse `t`).

STATUS / FIREWALLS: C0 recorded only as ANALYTICALLY CLOSED CONDITIONAL ON FORMAL NORMALISATION; Ω_H and Perron/nuclear normalisation, source-length bounds and product-energy comparisons remain explicit interfaces; the naive full-CRT signless-pair DFT is recorded as retracted (no universal non-equality theorem asserted); the pair-existence label is preserved and marked superseded as first frontier, with `THREEFACTOR-TRANSVERSE-CRITICAL-BEZOUTNUMERATOR-SINGLECARRIER45` open as the current frontier; the b-diagonal row stays separate and open; Erdős #287 stays OPEN.

BUILD AND AUDIT: each new module builds individually (PASS); default `lake build` PASS with 8305 jobs and 0 errors. `#print axioms` is run for all 134 new declarations: every one depends only on a subset of `propext`, `Classical.choice`, `Quot.sound` (58 depend on no axioms). No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `implemented_by` occurs as code in any new file.

FINAL FORMAL VERDICT: SAFE APPEND-ONLY BANK UPDATED.

# Summary of changes for run 5fff01ff-dc20-488e-994e-09d148f8e653
Appended a new, kernel-checked C0 unitary-Fourier / transverse-carrier bank to the Erdős #287 project. Nothing existing was deleted, renamed, weakened or relocated; `RequestProject/Main.lean` received appended `import` lines only. Full detail is in `ERDOS287_C0_UNITARYFOURIER_SAFE_BANK_REPORT.md`.

FILES ADDED
- `RequestProject/CurrentProgramme/Erdos287ReciprocalUnitaryFourier.lean`
- `RequestProject/CurrentProgramme/Erdos287BalancedBUnitaryFourierCompiler.lean`
- `RequestProject/CurrentProgramme/Erdos287AffineBilinearReciprocalNumerator.lean`
- `RequestProject/CurrentProgramme/Erdos287C0PhysicalNormalisationInterface.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseCarrierInterface.lean`
- `RequestProject/Status/CurrentStatusErdos287C0UnitaryFourier.lean`
- `RequestProject/Status/CurrentStatusErdos287TransverseCarrier.lean`
- `RequestProject/Status/AxiomAuditErdos287C0UnitaryFourier.lean`
- `ERDOS287_C0_UNITARYFOURIER_SAFE_BANK_REPORT.md`
(Paths follow the repository's existing `CurrentProgramme/` + `Status/` layout rather than a new top-level directory.)

FILES MODIFIED: `RequestProject/Main.lean` (eight appended imports).

NEW UNCONDITIONAL THEOREMS (all proved, no placeholders)
- Full Fourier Gram `unitaryFourier_mulConj_sum` (`F_C F_C* = x·I`) and the exact column energy `unitaryFourier_column_energy`, for an arbitrary unit `C` and an arbitrary positive modulus — no squarefree or primality hypothesis; a composite-modulus instance is certified at `x = 12`, `C = 5`.
- `unitaryFourier_bilinear_bound`, `unitaryFourier_finset_bilinear_bound` (zero-extension / support-restricted form), the inversion permutation of the units (`isUnit_zmod_inv`, `zmod_inv_inv_of_isUnit`, `zmod_inv_bijOn_units`) and the principal new theorem `reciprocalUnitaryFourier_bilinear_bound`, with the alias `transverseTwoCarrierUnitaryFourier` (reused, not re-proved).
- Residue aggregation: `residueAggregate_l2_le_maxFiber`, the interval fibre count `interval_residue_fibre_card_le` (`≤ N/x + 1`, integer form) and `intervalResidueAggregate_l2_bound`; the regrouping `reciprocalPhase_fiberwise` and the compiler `balancedReciprocalFourier_compiler`.
- The exact four-term contraction identity `balancedFourier_contraction_identity`.
- Coprimality firewall `coprime_product_left/_middle/_right/_all`.
- Affine and bilinear moving-numerator algebra `affineBilinearNumerator_reciprocal_decomposition` and its character factorisation / rank-one reduction.

CONDITIONAL COMPILERS (every analytic input an explicit hypothesis)
`threeCarrierReciprocalFourier_of_productEnergy`, `c0_balanced_branch_bound_of`, `perronNuclear_total_of_normalisation`, `omegaHL2_of_pointwise_normalisation`, `transverseTwoCarrier_bound_of_unitSupport`, `transverseTwoCarrier_bound_with_fibre_weights`. Their conclusions are explicit finite inequalities; no conclusion is `True` and none asserts C0 closure. Each hypothesis shell (product-convolution energy, Perron/nuclear, Ω_H ℓ²) is proved both non-automatic and satisfiable, so nothing can be silently discharged. The existing Ω_H pointwise shell is reused rather than duplicated.

INTERFACES / METADATA
`TransverseCarrierPacket` with unfilled `Prop` fields, `UsableTwoCarrierPair`, the bare trichotomy datatype (no exhaustiveness claimed), a `ResearchStatus` datatype with the requested status values, the `x` vs `X` firewall (`inv_sqrt_comparison_not_automatic`), the acyclic constant-selection order, and preservation theorems for the earlier ledgers. C0 is recorded only as "ANALYTICALLY CLOSED CONDITIONAL ON FORMAL NORMALISATION"; the b-diagonal row stays open and separate (`no_double_spending`); Erdős #287 stays open.

BUILD AND AUDIT
Each new module builds individually: PASS. Default `lake build`: PASS (8298 jobs, 0 errors). `#print axioms` for every new declaration reports only subsets of `propext`, `Classical.choice`, `Quot.sound`; several depend on no axioms. No `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by` or `native_decide` occurs as code in any new file. Not proved and not encoded: the carrier factorisation of `Q_*^red`, the `B_*^red` dependence, two-long-carrier existence, and any single-carrier residual classification.

# Summary of changes for run dd15ae7d-1759-4b7b-8bc7-0f355114010b
Appended the requested C0 source-lift / reduced-projective bank as new files only; no existing module was edited or weakened, and no statement claims C0 closed or Erdős #287 proved.

FILES CREATED
- `RequestProject/CurrentProgramme/Erdos287A0C0SourceLift.lean`
- `RequestProject/CurrentProgramme/Erdos287ReducedProjectivePair.lean`
- `RequestProject/CurrentProgramme/Erdos287BPrimeH0Energy.lean`
- `RequestProject/CurrentProgramme/Erdos287ConditionedInverseConvInterface.lean`
- `RequestProject/Status/CurrentStatusErdos287C0SourceLift.lean`
- `RequestProject/Status/AxiomAuditErdos287C0SourceLift.lean` (placed in `Status/` to match the existing `AxiomAudit*` convention)
- `ERDOS287_C0_SOURCELIFT_SAFE_BANK_REPORT.md`

FILES MODIFIED
- `RequestProject/Main.lean` — six appended `import` lines only.

UNCONDITIONAL THEOREMS (all kernel-checked)
- Source data: `Erdos287.SourceLift.SourceRow` (signed `s, s', Δ₀, Δ₀' : ℤ`; remaining slots `ℕ` with positivity fields) and `u, u', Γ₁, Γ₂, β₂, A0row, C0`.
- Primitive forms: `erdos287_gamma1_primitive`, `erdos287_gamma2_primitive`, `erdos287_A0row_primitive`, `erdos287_C0_primitive`, plus `erdos287_u_pos`, `erdos287_u'_pos`, `erdos287_b_pos`.
- Row representative: `erdos287_Q2_dvd` (`x ∣ d₁' v x`), `erdos287_A0pre_sub_A0row`, `erdos287_A0pre_dvd_sub`, `erdos287_A0pre_congr_A0row` (`A0pre ≡ A0row [ZMOD x]`), `erdos287_A0pre_congr_A0row_row`.
- Raw→reduced: `erdos287_F_pos`, `erdos287_F_ne_zero`, `erdos287_Praw_factor`, `erdos287_Rraw_factor`, `projective_collision_iff_of_row_factor`, `erdos287_raw_projective_collision_iff_reduced`, `projective_collision_invariant_under_row_scaling`, `row_factors_may_differ`.
- Depth record: `erdos287_Pnat_slot_product`, `erdos287_Rnat_slot_product`, `erdos287_numerator_depth`, `erdos287_denominator_depth` (both 8), `erdos287_fixed_depth_exponent` ((8+8)²−2 = 254).
- Finite energy: `product_fibre_l2_bound_of_fibre_card`, `productFibre_card_le_of_second_mem`, `product_fibre_l2_bound_of_second_cardinality`, `bprime_h0_global_energy`, `product_fibre_l2_bound_of_filtered`, `bprime_h0_global_energy_congruence_filter`.
- Firewall witnesses: `conditionedInverseConv_hypothesis_not_automatic`, `conditionedInverseConv_hypothesis_satisfiable`, `omegaH_normalization_not_automatic`; ledger theorems `banked_children_are_unconditional`, `open_owners`, `global_rows_not_closed`, `no_analytic_row_is_banked`, `depth_bound_not_formalised`, `sourcelift_pass_does_not_imply_c0_closure`, `commonX_ledger_still_preserved`.

CONDITIONAL THEOREMS (explicit named hypotheses only)
`energy_transfer_of_depth_bound` and `bprime_h0_global_energy_with_depth_bound` (hypothesis `d₁' ≤ Lparam^K`), `erdos287_C0_after_conditioned_transfer` (hypothesis `ConditionedInverseConvHypothesis`), `omegaH_energy_of_normalization` (hypothesis `OmegaHNormalizationHypothesis`). `d₁' ≤ L^K`, the Ω_H normalisation and the conditioned transfer are never asserted; both shells are proved non-automatic.

BUILD AND AUDIT
`lake build` on the default target: PASS (8290 jobs, 0 errors). A token search over all new files finds no `sorry`, `axiom`, `unsafe`, `native_decide`, `opaque` or `implemented_by` as code (only in docstring prose in the audit file). `#print axioms` on every new declaration reports only subsets of `propext`, `Classical.choice`, `Quot.sound`; several depend on no axioms.

HOSTILE-AUDIT POINTS
Casts are explicit with no `Nat` subtraction; sign slots carry no positivity; `F = b u'` is only cancelled via the proved `F ≠ 0`; the collision equivalence is stated for two independent rows with independent factors (`row_factors_may_differ` witnesses `F₁ ≠ F₂`); the energy lemma bounds fibre cardinality (via injectivity of `p ↦ p.2` on fibres over `n ≠ 0`), not a pointwise divisor maximum.

STATUS FREEZE (recorded in the ledger and proved there): banked children A0C0-PRIMITIVE-SOURCEFORM45, A0C0-SOURCELIFT45, A0C0-BPRIME-ABSORPTION45, BPRIME-H0-GLOBALENERGY45, PROJECTIVE-RAW-TO-REDUCED45, fixed depth (8,8); OPEN analytic owner EXACTPRODUCT-CONDITIONED-INVERSECONV-LEVELLS45; OPEN source pin SHAREDGCD-OMEGAH-NORMALISATION-SOURCEPIN45; EXACT PRODUCT COLLISION / DOUBLE TYPE II / C0: PARTIAL; ERDOS287: OPEN.

# Summary of changes for run e3eda94c-ae28-4753-ad56-d37dec60d2c5
## COMMON-x / fractional-linear C0 bank — appended, kernel-checked, build green

The new bank is appended strictly after the existing HYBRID-2 / critical-rectangle bank. No previously banked module was edited, no previously proved theorem was altered or weakened, no historical status layer was replaced or deleted. Full detail is in `ERDOS287_COMMONX_FRACTIONALLINEAR_SAFE_BANK_REPORT.md`.

### FILES ADDED
- `RequestProject/CurrentProgramme/Erdos287CommonXArithmetic.lean`
- `RequestProject/CurrentProgramme/Erdos287FractionalLinearC0.lean`
- `RequestProject/CurrentProgramme/Erdos287CommonXCollisionFirewall.lean`
- `RequestProject/Status/CurrentStatusErdos287CommonXFrontier.lean`
- `RequestProject/Status/AxiomAuditErdos287CommonX.lean`
- `ERDOS287_COMMONX_FRACTIONALLINEAR_SAFE_BANK_REPORT.md`

### FILES MODIFIED
- `RequestProject/Main.lean` — five new `import` lines appended only. No import path of any existing module changed.

### UNCONDITIONAL THEOREMS (all kernel-checked, no analytic hypothesis)
`Erdos287.CommonX` — §2 common-x conductors: `commonX_gcd` (`gcd(a₁x,a₂x) = x·gcd(a₁,a₂)`), `commonX_mul`, `commonX_lcm`, `commonX_gcd_coprime`, `commonX_lcm_coprime`, `commonX_dvd_left`, `commonX_dvd_right`, `commonX_dvd_gcd`, `commonX_gcd_mul_lcm`. §3 centered-κ CRT: `kappa_crt_exists`, `kappa_mod_small`, `kappa_mod_long`, `kappa_unit_long`, `kappa_sub_one_coprime_long`, `kappa_sub_one_gcd_long_eq_one`, `gcd_kappa_sub_one_fullConductor`, `gcd_kappa_sub_one_fullConductor_of_crt`. §4 graph-diagonal firewall: `graph_diagonal_forces_full_gcd`, `gcd_eq_natAbs_of_dvd`, `graph_literal_diagonal_impossible`, `graph_diagonal_impossible_of_centered`. §7–§8: `commonDivisor_residue_compatible`, `commonDivisor_residue_cancel_unit`, `commonDivisor_residue_iff_unit`, `centered_kappa_satisfiable`, `xRowDiagonal_not_excluded`.

`Erdos287.FractionalLinear` — §5–§6: `fractionalLinear_to_linear`, `oppositeRow_linearized`, `oppositeRow_unique_residue`, `oppositeRow_unique_residue_of_source`, `oppositeRow_unique_residue_zmod`, `kappa_fractionalLinear_of_source`, `kappa_fractionalLinear_of_source_zmod`, `denominator_ne_zero_of_unit`. §11 local change of variables: `affine_leftInverse`, `affine_rightInverse`, `affine_bijective`, `affine_pole_iff`, `sum_affine_reindex`, `sum_affine_reindex_nonzero`.

Conservatism points honoured: the full-conductor gcd equality carries its literal hypotheses (`κ−1 = d·s` with `s` coprime to `qLong`) rather than being overstated; cancellation by `b` exposes `IsUnit b` explicitly; congruences are written as literal divisibilities so no modular inverse is chosen implicitly.

### CONDITIONAL / STATUS-ONLY
`Erdos287.CommonXFrontierStatus`: ledger data (`CommonXNode`, `CommonXLabel`, `stage`, `commonXLedger`, `DiagonalKind`, `DiagonalStatus`, `diagonalLedger`) plus eighteen bookkeeping theorems, including the three demanded non-implications (`commonX_arithmetic_pass_does_not_imply_c0_closure`, `fractionalLinear_pass_does_not_imply_kloosterman_estimate`, `local_kloosterman_arithmetic_does_not_imply_spectral_closure`), `no_false_promotions`, `status_does_not_encode_xRow_exclusion` (the graph/x-row separation, backed by the witness theorem, not by fiat), `transverse_status_rows`, `bdiagonal_status_rows`, and `hybrid2_ledger_still_preserved` / `caseB_ledger_still_preserved`. The Type-I / Type-II rows carry labels deliberately distinct from `provedUnconditional`, so they are records of the research status and cannot read as proofs of an analytic estimate.

### NOT FORMALISED
Double-Type-II Kloosterman saving; level-averaged Kuznetsov / spectral closure; Weil bound; transverse analytic closure; b-diagonal analytic closure (numerical vertex dictionary absent); Ω_H source normalization. None is admitted or assumed.

### AUDITS AND BUILD
- Axiom audit: all 58 new principal declarations depend only on a subset of `propext`, `Classical.choice`, `Quot.sound`; several depend on no axioms at all. No new custom axiom.
- Token audit: no `sorry`, `axiom`, `unsafe`, `native_decide`, `opaque` or `implemented_by` as a code construct in any new file (only the docstring sentence listing the forbidden tokens). Decidable ledger facts use `decide +kernel`.
- `lake build` on the default target: **PASS**, 8284 jobs, 0 errors.

FORMAL FIRST RESIDUAL: `SharedGcdOmegaHNormalizationSourcePin`
RESEARCH FIRST ANALYTIC RESIDUAL: `CommonXFractionalLinearDoubleTypeIIKloosterman45`
C0 / TRANSVERSE / b-DIAGONAL: researchStrictlyReducedOpen
ERDOS287: OPEN

# Summary of changes for run dcdd0861-ffe6-4fe2-afa9-fb4fd3080e2b
The HYBRID-2 / critical-rectangle bank is appended, kernel-checked, and the full repository builds. Full detail is in `ERDOS287_HYBRID2_CRITICALRECT_SAFE_BANK_REPORT.md`.

FILES ADDED:
- `RequestProject/CurrentProgramme/Erdos287Hybrid2Arithmetic.lean`
- `RequestProject/CurrentProgramme/Erdos287Hybrid2AnalyticCompiler.lean`
- `RequestProject/CurrentProgramme/Erdos287Hybrid2CriticalRectangle.lean`
- `RequestProject/CurrentProgramme/Erdos287Hybrid2ShortEdgeFirewall.lean`
- `RequestProject/CurrentProgramme/Erdos287BDiagonalProductMod.lean`
- `RequestProject/Status/CurrentStatusErdos287Hybrid2Frontier.lean`
- `RequestProject/Status/AxiomAuditErdos287Hybrid2.lean`
- `ERDOS287_HYBRID2_CRITICALRECT_SAFE_BANK_REPORT.md`

EXISTING FILES MODIFIED:
- `RequestProject/Main.lean` — seven new `import` lines appended only. No prior mathematical module edited; no previously proved theorem altered; no source firewall replaced.

UNCONDITIONAL THEOREMS:
`Erdos287.Hybrid2`: `mobius_opening_of_squarefree`, `mobius_opening_needs_squarefree`, `coprime_left_of_mul_coprime`, `coprime_right_of_mul_coprime`, `coprime_both_of_mul_coprime`, `isCoprime_both_of_mul_isCoprime`, `isCoprime_of_isInverseMod`, `reciprocal_cancel_common_factor`, `isCoprime_ell_of_inverse`, `baseConductor_gcd`, `fullConductor_gcd`, `fullConductor_needs_coprime`, `pairwise_factors_dvd`, `lcm_dvd_e`, `mul_eq_gcd_mul_lcm`, `g0_mul_g0prime_dvd_e_mul_difference`, `g0_mul_g0prime_does_not_divide_difference`, `sum_inv_Icc_le_one_add_log`, `ell_sum_harmonic`, `ell_sum_harmonic_two_min`, `eta_sq_expand`, `eta1_nonneg`, `rectangle_side1`, `rectangle_side2`, `rectangle_product`, `rectangle_intersection`, `topShell_e_lower_bound`, `noncontraction_shortEdge_or_rectangle`, `hybrid2_survivor_union`, `rectangle_alone_does_not_capture_all_survivors`, `shortD_is_not_automatic`.
`Erdos287.BDiagonal`: `isCoprime_of_dvd_mul_sub_one`, `bdiag_crt_inverse_congr`, `bdiag_phase_product_modulus`, `bdiag_moebius_mul`, `bdiag_moebius_levelPair`, `bdiag_squarefree_split`, `bdiag_reduced_conductor`, `bdiag_reduced_unit`, `bdiag_survivor_union`.
Ledger (`Erdos287.Hybrid2FrontierStatus`): `caseB_strictly_before_hybrid2_frontier`, `primitiveFractionCritical_not_frontier`, `omegaNormalization_is_formal_first_residual`, `hybrid2_analytic_descendants_all_open`, `hybrid2_longEdge_passedThrough_only_if_appropriate`, `erdos287_open`, `only_arithmetic_rows_are_unconditional`, `hybrid2_survivor_union`, `hybrid2_longEdge_pass_does_not_capture_survivors`, `caseB_ledger_still_preserved`, `primitiveFraction_ledger_still_preserved`.

CONDITIONAL THEOREMS:
`Erdos287.Hybrid2.fixedEll_bound`; `Erdos287.Hybrid2.hybrid2_bound`; `Erdos287.BDiagonal.bdiag_delta_contraction_conditional`.

EXPLICIT ANALYTIC HYPOTHESES:
- `fixedEll_bound`: `hArch : Bell ≤ Carch * sqrt Sell`; `hPacket : Pell ≤ L1^2/(ell*M1)`; `hLS : Sell ≤ (D/ell + Q)*(1 + M1/(ell*Q))*Pell`.
- `hybrid2_bound`: `hArch : Btot^2 ≤ Carch^2*Etot`; `hPacket : Etot ≤ Lell^2*Wsep`; `hLS : Wsep ≤ 1/D + 1/M1 + 1/Q + Q/(D*M1)`.
- `bdiag_delta_contraction_conditional`: `hArchB`, `hPacketB`, `hLSB` (same shapes).
- Source gcd identities of §5 exposed as hypotheses `h1`, `h2` (option B). No equivalent literal separated-frequency large sieve exists in the repository, so `hLS` is passed rather than instantiated. None of these is an axiom.

SHORT-D: FORMALISED OPEN
SHORT-M: FORMALISED OPEN
SHORT-Q: FORMALISED OPEN
(exact pigeonhole with explicit constants `C_short = C_rect = 4`; no closure proof was available, none invented)

LONG-EDGE RECTANGLE: FORMALISED PASS (algebraic compiler `rectangle_side1/2`, `rectangle_product`, `rectangle_intersection`); ledger node stays `conditionalOpen`.

g0g0' DIVISIBILITY: FORMALISED PASS. The stronger `g0*g0' | (b2-b1)` was not formalised — it is false and is explicitly refuted.

b-DIAGONAL ALGEBRA: FORMALISED PARTIAL (exact CRT phase collapse, Möbius product, gcd reduction all PASS; the Δ-large-sieve contraction is conditional only).

AXIOM AUDIT: every one of the 63 new declarations depends only on `propext`, `Classical.choice`, `Quot.sound`; several depend on no axioms at all. No new custom axiom.

UNSAFE-TOKEN AUDIT: no `sorry`, `axiom`, `unsafe`, `native_decide`, `opaque` or `implemented_by` in any new file (only prose mentions inside docstrings). Decidable facts use `decide +kernel`.

FULL BUILD: PASS — `lake build` on the default target completes with 8279 jobs and 0 errors.

OMEGA_H: SOURCE PIN (unchanged; B and G polynomial margins also unchanged)

ERDOS287: OPEN

FIRST EXACT FORMAL RESIDUAL: `SharedGcdOmegaHNormalizationSourcePin` (Ω_H normalisation source pin), with the conditional analytic frontier being the union `Hybrid2ShortD ∪ Hybrid2ShortM ∪ Hybrid2ShortQ ∪ Hybrid2LongEdgeTwoSidedRectangle ∪ BDiagonalDeltaProductModRectangle`.

§12 note: the top-shell comparability lower bound on `e` is formalised (`topShell_e_lower_bound`); the exponent-level consequence for `kappa` is recorded as NOT YET FORMALISED, since the source-exact dictionary it needs is not present in the repository.

STOP.

# Summary of changes for run 207d670f-9cdd-4c86-b15d-ef7ea07a5160
## What I did

I re-verified the CASE-B primitive-fraction bank you sent and then added the statements from it that were **not** yet available as literal Lean theorems. The work is append-only: no previously banked module was edited, and the only change to an existing file is three new `import` lines in `RequestProject/Main.lean`.

### Files added
* `RequestProject/CurrentProgramme/CaseBPrimitiveFractionReproof.lean` — the new mathematics
* `RequestProject/Status/CurrentStatusErdos287CaseBFrontier.lean` — reproof rows + frontier ledger
* `RequestProject/Status/AxiomAuditErdos287CaseBReproof.lean` — `#print axioms` for every new declaration
* `ERDOS287_CASEB_PRIMITIVEFRACTION_REPROOF_BANK_REPORT.md` — the delta report

### New theorems proved (all kernel-checked)
* `Erdos287.CaseBReproof.separation_of_distinct_pairs` — spacing in the form a large sieve actually uses: the hypothesis is that the two standard representatives `(m,t)` are *distinct* (injectivity, which needs only `(t,m)=1`, supplies the nonzero numerator), conclusion `≥ d/(4G²)`, `G = dM`. Unconditional.
* `Erdos287.CaseBReproof.caseB_pipeline_QH_bound` — the end-to-end composition energy → fixed `d` → `S1`/`S2` → global `Q_H`, giving `|Q_H| ≤ B(1+B/G)L·(A c₁(1+log⌊X/H⌋) + 8c₁G²/H)` with the coefficient-energy bound inserted verbatim instead of an abstract hypothesis. The analytic inputs (`hLS`, the `E_g` bound, the Ω_H support/mass normalisation) remain explicit hypotheses, and the extra comparability `G ≤ M` is stated openly.
* `Erdos287.CaseBReproof.normalised_ratio_le_of_comparable` — the `AB ≍ X` source firewall: from `c₀X ≤ AB` the four-term decomposition survives, with the comparability constant appearing on the `G²/(HX)` term only.
* `Erdos287.CaseBReproof.kappa_le_of_critical_range` (with `rpow_max_eq`, `loglog_div_log_tendsto_zero`, `kappa_le_eventually`, `kappa_le_max_zero`) — the exponential critical range in exact form, `κ ≤ max(2θ−1, θ−α) + K·loglog X/log X`, plus the `o(1)` version `κ ≤ max(0, 2θ−1, θ−α) + ε`.
* `Erdos287.CaseBReproof.projector_S1_at_two_G` — the audited `X = 2G` truncation, `S1 ≤ c₁(1 + log(2G/H))`.
* Frontier ledger (`CaseBFrontierStatus`): `frontier_no_closed_rows`, `frontier_unique`, `primitiveFractionCritical_strictly_before_frontier`, `primitiveFractionCritical_not_frontier`, `chain_is_strictly_increasing`, `frontier_erdos287_open`, `caseB_ledger_preserved`. These are bookkeeping statements about the ledger only — `passedThrough` records that a strictly later reduction exists, not that any node is closed — and they assert no mathematical content about the descendant nodes.

### Verification
* Full build of the default target: **PASS** (`Build completed successfully`, 8272 jobs), which also re-checks every previously banked CASE-B module.
* No `sorry`, `axiom`, `unsafe`, `native_decide`, `opaque` or `implemented_by` in the new material.
* Axiom audit: every new declaration depends only on `propext`, `Classical.choice`, `Quot.sound`; several ledger rows depend on no axioms at all.
* Every hypothesis of the pipeline theorem was checked to be load-bearing.

### Unchanged status
The Ω_H normalisation and the `B`/`G` polynomial margins remain **source pins** — nothing was promoted, `SMALL-B` and `SMALL-G` stay open, and Erdős #287 remains **OPEN**. Nothing in this delta claims otherwise.


# Summary of changes for run 22bf2afd-9633-4f07-b525-d9b7294d5167
## CASE-B one-level primitive-fraction large sieve — audit banked

I did not assume any of the incoming statuses: Sections 2–10 were re-derived from scratch in Lean, and each row is backed by a kernel-checked statement. The build succeeds and there is no `sorry`, `axiom`, `unsafe`, `native_decide` or other placeholder in the new material; every new declaration depends only on `propext`, `Classical.choice`, `Quot.sound`.

### Files added
Exact mathematics (`RequestProject/CurrentProgramme/`): `OneLevelPrimitiveFractionSpacing.lean` (§2), `OneLevelCoefficientEnergy.lean` (§4), `OneLevelProjectorS1S2.lean` (§6), `OneLevelWeightedLargeSieve.lean` (§§3, 5), `OneLevelPrimitiveFractionGlobal.lean` (§§7–10).
Status/audit (`RequestProject/Status/`): `CurrentStatusErdos287PrimitiveFractionCaseB.lean`, `AxiomAuditErdos287PrimitiveFractionCaseB.lean`.
Report: `ERDOS287_CASEB_ONELEVEL_PRIMITIVEFRACTION_SAFE_BANK_REPORT.md`.
Only change to a pre-existing file: seven new `import` lines in `RequestProject/Main.lean`. Historical ledgers are imported and re-checked, not edited (`historical_status_preserved`).

### STRICT OUTPUT

```
SPACING: PASS (unconditional)
  primitiveFraction_inj, spacing_lower_bound, spacing_uniform,
  primitiveFraction_separation.  Standard representatives 0 ≤ t < dm force the
  integer shift to 0; only (t,m)=1 is needed, not (t,dm)=1.
  separation ≥ 1/(d m1 m2) ≥ d/(4G²), G = dM.

WEIGHTED LARGE SIEVE: PASS (reduction; analytic input carried as a hypothesis)
  0 ≤ ρ ≤ ‖V‖_∞ with no friability estimate; ∑ρ|S|² ≤ ‖ρ‖_∞ ∑|S|².
  exact factor = A + 4G²/d, from δ = d/(4G²);  no extra log, no X^ε.
  The classical separated-frequency inequality itself is NOT formalised here;
  it appears only as the explicit hypothesis hLS.

COEFFICIENT ENERGY: PASS
  exact bound = ∑_{M≤m<2M} E_{dm}/m² ≤ dB(1+B/G)L^{C_E}, implied constant 1,
  from ∑1/m ≤ 1 and ∑1/m² ≤ 1/M.  No hidden log.  E_g ≤ (gB+B²)L^{C_E} is an input.

FIXED-d (§5): PASS.  (A + 4G²/d)(dK) = (Ad + 4G²)K exactly; all powers of d verified.

S1: PASS
  exact bound = ∑_{d≤X}|λ_H(d)|/d ≤ c₁(1 + log⌊X/H⌋) ≤ c₁(1 + log(X/H)),
  i.e. c₁(1 + log(2G/H)) for X = 2G.  The inner Möbius sum is genuinely truncated
  at ⌊X/H⌋; no d ~ H assumption is used anywhere.

S2: PASS
  exact bound = ∑_{d≤X}|λ_H(d)|/d² ≤ 2c₁/H.

OMEGA_H SOURCE NORMALISATION: SOURCE PIN
  supp Ω_H ⊆ {e~H}, |Ω_H| ≪ 1, ∑|Ω_H|/e ≪ 1, ∑|Ω_H|/e² ≪ 1/H are not theorems
  anywhere in this repository (λ_H is defined for arbitrary Ω).  Carried as the
  hypotheses hsupp, hmass.  Only the lower support and the e⁻¹ mass were needed.

GLOBAL Q_H: PASS
  exact bound = |Q_H| ≤ B(1+B/G)L^{C_E}·( A c₁(1 + log⌊X/H⌋) + 8c₁G²/H )
  envelope    = |Q_H| ≤ 8c₁·B(1+B/G)(A + G²/H)·L^{C_E+1}

NORMALISED RATIO: PASS (exact identity, X = AB)
  |Q_H|/(AB²) = L₁/B + L₁/G + L₀G²/(HX) + L₀G/(HA); four terms independent.

B POLYNOMIAL: SOURCE PIN
G POLYNOMIAL: SOURCE PIN
  No statement A ≥ X^{η_A}, B ≥ X^{η_B}, G > X^{1/2−η₀} occurs in the repository;
  none was manufactured.

1/B: OPEN   1/G: OPEN
  The mechanism is proved unconditionally ((log X)^K/X^η → 0, hence L^K/B ≤ ε
  eventually whenever B ≥ X^η), but its input is an unresolved pin, so
  SMALL-B and SMALL-G obstructions are NOT banked as closed.

H-CRITICAL RANGE:
  H ≤ L^{C_E+K_*}·max(G²/X, G/A),  K_* = 6 + 2η + C_route;
  exponentially κ ≤ max(0, 2θ−1, θ−α) + o(1).

PROMOTED THEOREMS:
  DET1-ONELEVEL-PRIMITIVEFRACTION-SPACING45  : PASS (exact, unconditional)
  DET1-ONELEVEL-dRESTRICTED-LS45             : PASS (conditional reduction)
  DET1-ONELEVEL-COEFFENERGY45                : PASS (conditional on E_g input)
  DET1-ONELEVEL-PROJECTOR-S1S2-45            : PASS (conditional on Ω_H pin)
  DET1-ONELEVEL-PRIMITIVEFRACTION-GLOBAL45   : PASS (conditional on the above)
  ERDOS287 CLOSED                            : NOT BANKED

ERDOS287: OPEN

FIRST EXACT RESIDUAL:
  287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-PRIMITIVEFRACTION-CRITICAL45
  range: H ≤ L^{C_E+K_*} max(G²/X, G/A)
  retains: μ(m); primitive t mod dm; reciprocal-b source; friable a;
           exact signed λ_H(d)/d² projector.
```

Two audit notes on the source statements as given: the sieve factor carries the explicit absolute constant 4 (`A + 4G²/d`) coming from `δ⁻¹ = 4G²/d`, and the S1 factorisation only yields `1 + log(2G/H)` if the inner Möbius sum is kept truncated at `⌊X/H⌋` — both are reflected in the banked statements. No work was done beyond this audit.


# Summary of changes for run 5c7ec803-72e5-4b06-9236-9c455af6a33f
Banked the requested **ONE-LEVEL MÖBIUS append-only delta** for Erdős #287 (§§0–16). The delta is strictly additive: no protected module was rebuilt or edited, and the only change to a pre-existing file is nine new `import` lines in `RequestProject/Main.lean`.

## Files added

**Exact algebra** (`RequestProject/CurrentProgramme/`):
- `LevelPairProductModulus.lean` — §§1–3, §5
- `LevelPairFixedDRigidity.lean` — §4
- `LevelPairReciprocalNormalForm.lean` — §6
- `LevelPairPrimeAssignment.lean` — §§7–8
- `SharedGcdGramSquare.lean` — §§9–10
- `PrimitiveTRamanujanFirewall.lean` — §12
- `SharedGcdOneLevelMobiusSocket.lean` — §§11, 13

**Status / audit** (`RequestProject/Status/`):
- `CurrentStatusErdos287OneLevelMobius.lean` — §14
- `AxiomAuditErdos287OneLevelMobius.lean` — §15

**Report**: `ERDOS287_ONELEVEL_MOBIUS_SAFE_BANK_REPORT.md` — §16.

## Principal theorems proved

- **Product-modulus compression**: `moebius_levelPair_compress`, `moebius_levelPair_eq_moebius_n` (μ(g1)μ(g2)=μ(n)), `lcm_levelPair_eq` (lcm(g1,g2)=g0·n), `levelPair_norm_eq` (1/(g1g2)=1/(g0²n)).
- **`gcd_D_n_eq_one`** — proved *directly* from primitivity, with the older `gcd(D,Λ) ∣ g0` recorded separately.
- **Divisor split / reindexing**: `unitary_split_coprime/_dvd`, `levelPair_divisorSplit`, `levelPair_reindex_fixed_n`, `levelPair_reindex`. No asymptotic dyadic ranges formalised.
- **Fixed-D rigidity**: `t1_congr_mod_r1`, `t2_congr_mod_r2`, `fixedD_solution_iff` (exact iff for `t1=xD+r1u`, `t2=yD+r2u`), `fixedD_u_period_g0` (`u mod g0`), `fixedD_primitive_reduces_to_g0_side`.
- **Farey kernel**: `fareyDifference_eq_D_div_g0n` (`t1/g1 − t2/g2 = D/(g0n)`) and `fareyDifference_split_invariant` — independence of the split `r|n`. No analytic property of Φ_A formalised.
- **CRT reciprocal normal form**: `exists_crtBeta`, `gcd_two_g0_beta_eq_one`, explicit numerator `crtNumerator` (Ξ_r), `reciprocal_phase_normalForm`, `reciprocal_normalForm_of_inverse`.
- **Fixed-n prime assignment**: `fixed_n_two_state_product` — banked as a fixed-`n` factorisation only; **no** multiplicativity in `n` asserted.
- **Non-multiplicativity firewall**: `localFactorK_not_multiplicative` — one explicit finite counterexample, K(15)=4 ≠ 1 = K(3)K(5). No universal negation.
- **Shared-gcd Gram-as-square** (highest-priority bank): `sum_lambdaH_divisors` (Möbius inversion of Ω_H), `sharedGcd_gram_square`, and the one-level form `sharedGcd_oneLevel_gram`; plus `abs_lambdaH_le`, `lambdaH_harmonic_mass_le`, `omega_support_mass_le`. Only the exact convolution inequality is banked; the asymptotic `≤ C/H` is left as research metadata.
- **Primitive-t Ramanujan firewall**: `ramanujan_prime_not_dvd` (c_p = −1), `ramanujan_prime_dvd` (c_p = p−1), `moebius_mul_ramanujan_prime`, and the re-exported divisor normal form. The ζ(1+w)/ζ(2+2w) Euler-product claim is **not** formalised.
- **Status ledger** (§14, all rows as specified): `no_closed_rows`, `erdos287_open`, `uniform_k0_open_fcl_not_reached`, `amplitude_exponents` (near-density 1/2, final amplitude 1/4), `cauchyConfiguration_superseded_not_closed`, `largeSharedG0_retracted_and_nearFreq_open`, `energy_subpolytope_provisional_not_closed`, `oneLevelMobiusGram_is_first_exact_residual` (uniqueness of rank 1), `signed_levelPair_gram_strictly_reduced`, `exact_rows_are_theorems`, `gram_square_and_one_level_are_theorems`, `nonmultiplicativity_firewall_is_explicit`, `historical_sharedG0_status_preserved`.

## Analytic firewall

Both new analytic interfaces are left **UNINHABITED** by design, each with an explicit refutation showing the hypothesis is genuine and not automatic:
- `SharedGcdOneLevelEnergyInput` (§11) — the subpolytope is **not** marked closed; only the satisfiability of the constraint set (`exists_valid_energyLedger`) is formal.
- `SharedGcdOneLevelMobiusGramInput` (§13) — retains primitive `t`, the reciprocal `b` source, the friable `a` source and the harmonic/Perron parameters; primitive `t` is **not** completed inside the socket.

All pre-existing analytic sockets remain uninhabited.

## Build and axiom audit

- Targeted builds of both new Status modules: success.
- Full `lake build`: **Build completed successfully (8262 jobs), 0 errors.** No new warnings; the warnings present are pre-existing in historical modules, deliberately left untouched.
- The audit module runs `#print axioms` over **90** audited declarations. Every one depends only on `propext`, `Classical.choice`, `Quot.sound` (several on strictly fewer; one on none). A filtered scan for any axiom outside the allowed list returns nothing.
- Source scan of all ten new files for `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `implemented_by`: **no occurrences** (only prose hits inside comments).

## Commits

Seven commits, all pushed to `origin`; working tree clean.

**FINAL: ERDOS287 OPEN. CURRENT FIRST EXACT MAIN-LINE RESIDUAL: 287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-MOBIUS-GRAM45.**

# Summary of changes for run b63c35a5-f054-4172-b072-f088bae33c4c
Completed the append-only SHARED-g₀ / reduced-denominator / Cauchy-repair formal delta for Erdős #287. Nothing historical was rebuilt or superseded; the only change to an existing file is ten added `import` lines in `RequestProject/Main.lean`. `ARISTOTLE_SUMMARY.md` and `CurrentStatusErdos287PrimitiveLocalProfile.lean` were not edited, and both `ShortLiftEulerAnalyticInput` and `PrimitiveLocalProfileGramInput` remain uninhabited.

**New files (all `sorry`-free and building):**

- `RequestProject/CurrentProgramme/LocalProfileHarmonicTwists.lean` (§1) — the exact finite harmonic-twist identity `mProfile_harmonic_twist_expansion`: m_{g,b}(Δ) = Σ_{ℓ | rad(2bg)} (1/ℓ)·twistInner ℓ, over the repository's own `mProfile`, via `moebius_coprime_twist_sum`. The asymptotic L¹-cost claim is deliberately not formalised.
- `RequestProject/CurrentProgramme/SharedG0PrimitiveUParam.lean` (§2) — `sharedG0_u_param_iff`, `sharedG0_u_period`, the primitive exclusions `primitive_not_dvd_t1/_t2`, `excludedU_eq_iff_dvd_D` (the two forbidden residues coincide iff p | D), and `card_excludedU` = ν_p(D).
- `RequestProject/CurrentProgramme/SharedG0PrimitiveURouter.lean` (§3) — `primitiveUSum_eq_complete_sub_excluded` (exact local factor), the two elementary bounds `norm_primitiveUSum_le_modulus` (|U_p| ≤ p) and `norm_primitiveUSum_le_two` (|U_p| ≤ 2 when p ∤ C), the deduction `abs_prod_local_le` (|∏_p U_p| ≤ 2^ω(g₀)·gcd(g₀,C)), and the CRT factorisation `primitiveUSum_crt_split` in exact two-factor form U_{mn}(C) = U_m(Ca)·U_n(Cb).
- `RequestProject/CurrentProgramme/SharedG0UnitSectorGcd.lean` (§4) — `sharedGcd_reciprocalDiff_eq_originalDiff`: gcd(g₀, (2b₁)⁻¹−(2b₂)⁻¹) = gcd(g₀, b₁−b₂), plus the unit-twisted version. The coprimality side condition is derived rather than assumed.
- `RequestProject/CurrentProgramme/SharedG0BPairAveraged.lean` (§5) — `gcd_eq_sum_totient_divisors`, the exact-floor interval count `pairCountCongruentModulo_le`, and the finite precursor `bpair_gcd_sum_le_divisorCount`: Σ gcd(g₀,b₁−b₂) ≤ B²τ(g₀) + B·g₀.
- `RequestProject/CurrentProgramme/PrimitiveReducedDenominator.lean` (§6) — `lcm_sharedG0_eq`, `gcd_D_lambda_dvd_g0` (proved via coprimality with r₁ and r₂ separately, so valuation-safe with no squarefree hypothesis), `reducedDenominator_eq` and `reducedDenominator_ge` (den(D/Λ) ≥ r₁r₂ = g₁g₂/g₀²).
- `RequestProject/CurrentProgramme/PrimitiveNearFreqCount.lean` (§7) — reuses the banked Farey machinery: `nearFreqSet_eq`, `nearFreq_D_mem_Icc`, and the exact count `nearFreqSet_card_le`: N_near ≤ g₀ + 2g₀⌊g₀r₁r₂H/A⌋. No analytic saving is claimed.
- `RequestProject/CurrentProgramme/SharedG0CauchyConfigurationSocket.lean` (§9) — the uninhabited `SharedG0CauchyConfigurationInput` over a `CauchyLedger` carrying the five ledger quantities, with audit item A (averaged router, θ_U < 1) and audit item B (root consistency, the 1/4-vs-1/2 dichotomy) formalised, a trivial conditional consumer, and `sharedG0CauchyConfiguration_not_automatic` refuting it with explicit data.
- `RequestProject/Status/CurrentStatusErdos287SharedG0Repair.lean` (§11–12) — the new ledger with kernel-checked integrity theorems: no closed row, ERDOS287 open, UNIFORM k=0 open, FCL not reached, both analytic children `repairPending`, the hard-denominator child `pendingChild` (conditional, rank 0, not inhabited), LOCALPROFILE-GRAM45 `strictlyReducedBlocked`, the Cauchy configuration the unique first exact residual, every exact row backed by the actual quoted statement of §§1–7, and the historical LOCALPROFILE/BLOCK20 ledgers re-checked as unmodified. The short-lift Euler row carries `nancVerifiedPassUninhabited` — a research-metadata label only; no analytic statement is proved in Lean.
- `RequestProject/Status/AxiomAuditErdos287SharedG0Repair.lean` (§13) — `#print axioms` for all 64 new principal declarations.
- `ERDOS287_SHAREDG0_CAUCHY_REPAIR_SAFE_BANK_REPORT.md` (§14) — the full report.

**Build:** each new module builds cleanly (no errors, no warnings), and the full `lake build` completes successfully (8253 jobs).

**Placeholders:** none. No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, or `implemented_by` in any new file; the only textual match in the repository is the prose of the audit file's own docstring.

**Axioms:** every audited declaration depends on a subset of `propext`, `Classical.choice`, `Quot.sound`; three of the ledger theorems depend on no axioms at all.

All work is committed and pushed. ERDOS287 remains OPEN; the current first exact research residual is 287-K0-SP2-DET1-SHAREDG0-CAUCHY-CONFIGURATION45.

# Summary of changes for run 73505396-e329-44ca-9d1a-3ad8016591e6
Delivered the PRIMITIVE-CONDUCTOR / SHORT-LIFT → PRIMITIVE-LOCALPROFILE delta as an append-only layer. Everything is exact algebra / finite combinatorics; no analytic number theory is claimed, and Erdős #287 is **not** claimed solved.

**Files added** (no historical file modified; `RequestProject/Main.lean` received import lines only):
- `RequestProject/CurrentProgramme/PrimitiveRamanujanAlgebra.lean` (§A)
- `RequestProject/CurrentProgramme/PrimitiveRamanujanReassembly.lean` (§B)
- `RequestProject/CurrentProgramme/ShortLiftLocalProfile.lean` (§C)
- `RequestProject/CurrentProgramme/PrimitiveDMultiplicity.lean` (§D)
- `RequestProject/CurrentProgramme/PrimitiveFareyNearCollision.lean` (§E)
- `RequestProject/CurrentProgramme/PrimitiveLocalProfileGramSocket.lean` (§F)
- `RequestProject/Status/CurrentStatusErdos287PrimitiveLocalProfile.lean` (§G)
- `RequestProject/Status/AxiomAuditErdos287PrimitiveLocalProfile.lean` (§H)
- `ERDOS287_PRIMITIVE_LOCALPROFILE_SAFE_BANK_REPORT.md`

**FORMALLY PROVED.** The Ramanujan sum is built from the repository's own additive phase e(x)=exp(2πix): c_g(N)=∑_{t<g, gcd(t,g)=1} e(tN/g). From that definition: the complete additive sum ∑_{t<g}e(tN/g)=g·1_{g∣N}; `ramanujan_eq_divisor_sum` (DET1-PRIMITIVE-RAMANUJAN-DIVISOR-NORMALFORM45) c_g(N)=∑_{r∣gcd(g,N)} r·μ(g/r); `ramanujan_unit_shift` (DET1-PRIMITIVE-T-RAMANUJAN45) c_g(a+s·w)=c_g(2ab+s) for 2b·w≡1 (mod g); `moebius_mul_moebius_div` (μ(g)μ(g/r)=μ(r) for squarefree g=rk, gcd(r,k)=1) and `ramanujan_moebius_normalForm` (DET1-RAMANUJAN-MOBIUS-SIMPLIFICATION45) μ(g)/g·c_g(N)=∑_{rk=g, r∣N} μ(r)/k. §B: the branch identity ∑_{kd=n} μ(d)1_{gcd(2b,k)=1}1_{gcd(b,d)=1}=[n=1] on the coprime sector (the r>1 cancellation), ∑_{d∣n,d<n}μ(d)=−μ(n) for n>1, and `primitive_ramanujan_reassembly` (DET1-PRIMITIVE-RAMANUJAN-REASSEMBLY45): reassembly returns exactly raw progression − additive zero mode — a representation loop, verified, not an estimate. §C: the finite/dyadic profile mProfile(g,b,D) with Ψ, plus the finite Euler product ∑_{d∣n,gcd(d,H)=1}μ(d)/d = ∏_{p∣n,p∤H}(1−1/p) = (∏_{p∣n}(1−1/p))·∏_{p∣n,p∣H}(1−1/p)⁻¹ (the finite-prime-product avatar of H_H/ζ). §D: the solution line t₁=t₁⁰+r₁u, t₂=t₂⁰+r₂u and DET1-PRIMITIVE-D-MULTIPLICITY45 (≤ g₀+1 solutions in the box; the sharp g₀ is also banked). §E: lcm(g₀r₁,g₀r₂)=g₀r₁r₂, the exact rational implication |t₁/g₁−t₂/g₂|≤1/A ⟹ |D|≤lcm(g₁,g₂)/A, and the exact finite count ≤ (2⌊lcm/A⌋+1)·g₀ with explicit integer floors.

**ANALYTIC / UNINHABITED.** `ShortLiftEulerAnalyticInput` (Dirichlet-series ∑_{gcd(d,H)=1}μ(d)d^{-s}=H_H(s)/ζ(s)) and `PrimitiveLocalProfileGramInput` (|Gram| ≤ C·X·log^{−3−η}X over valid primitive-conductor configurations retaining π, s, τ, g, primitive t, friable a, Möbius b, mProfile(g,b,Q/g), μ(g), smooth weights) are stated and never inhabited; each has only a trivial conditional consumer, plus explicit refuting data and a nonempty valid-configuration witness, so neither is vacuous or automatic. Nothing of the shape exp(−c√(log D)) is formalised. The asymptotic wrapper gcd(g₁,g₂)+g₁g₂/A is left unformalised; only the exact finite precursor is banked.

**STATUS LAYER (append-only).** New ledger: PRIMITIVE-CONDUCTOR-SHORTLIFT-GRAM45 = superseded-but-not-false (never closed, never false); PRIMITIVE-LOCALPROFILE-GRAM45 = analytic open / uninhabited / first exact main-line residual; UNIFORM k=0 = open; FCL = not reached; ERDOS287 = open; no closed row. The imported BLOCK20 ledger is unchanged and re-checked.

**BUILD / AXIOM AUDIT.** `lake build` succeeds (8243 jobs, 0 errors); each new module also builds individually and is warning-free (the only repository warning is the pre-existing note in a historical file). No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `@[implemented_by]` in any new file. `#print axioms` over every principal new declaration yields only subsets of {propext, Classical.choice, Quot.sound} (two status rows use none). All work is committed and pushed.

ERDOS287 OPEN. FIRST EXACT MAIN-LINE RESIDUAL: 287-K0-SP2-DET1-PRIMITIVE-LOCALPROFILE-GRAM45.

# Summary of changes for run a4b08109-0d68-4e6a-902d-e7011eadcb70
SOURCE-SEAL REPAIR:
Attempted literally in `RequestProject/CurrentProgramme/FixedCertificateBalancedSevenSourceSeal.lean`, starting from the repository's own fixed-certificate smooth-parity packet (no model object). Proved: the k=0 / J=∅ / P⁺(n) ≤ n^σ_* reduction to the truncated Möbius sum (`fixedCertificate_k0_Jempty_reduction`, `fixedCertificate_smoothCut_reduction`); the finite seven-box identity `H_*(P) = −20` through the repository definitions (`fixedCertificate_sevenBox_eq_neg20`); the weight dictionary with explicit exclusion of hidden Λ(p), log p, 1/log p (`omegaBox_dictionary`, `omegaBox_carries_no_vonMangoldt_factor`, `_no_log_factor`, `_no_inverse_log_factor`), keeping the affine log r from Λ = μ∗log separate (`vonMangoldt_sum_divisors_eq_log`); and `balancedSevenSeal_of_cellIdentity`, which derives the whole seal from one remaining hypothesis. The seal is NOT inhabited.

SOURCE-SEAL RESIDUAL:
`Erdos287.Block20.FixedCertificateSP2PacketMatchesCompilerPacket` — identification of the literal repository fixed-certificate SP-2 packet with the packet consumed by the Balanced7 compiler (the `cell_identity` field). Status remains SOURCE_OPEN, with `sourceSeal_residual_not_automatic` refuting automaticity.

BLOCK20 PACKING:
Procedural greedy rule formalised (`bigAtoms`/`smallAtoms`/`groupSmall`/`packSide`/`packBoth`) with exact conservation (`packSide_perm`: no atom lost or duplicated), deterministic singleton vs grouped provenance, no d/m straddling, non-final block mass ≥ σ_*/3, block mass ≤ σ_*, ≤ 2 leftovers. `Block20PackingValidity` is separate and inhabited constructively by `packBoth_validity`, with `block20Validity_not_automatic` showing it is not vacuous. Ledger: ν₀ = 16623/100000 exactly (never 1/6), σ_* = ν₀ − 2ε_*, `sigmaStar_ge : σ_* ≥ 0.1629054`, `nineteen_blocks_overflow : 19·(σ_*/3) > 1`, `eps_one_over_600_not_admissible`.

BLOCK20 COUNT:
≤ 20 (`nonfinal_block_count_le_18` plus at most two leftovers; `template_block_count_le_20`).

TRUNCATED MÖBIUS:
Exact finite divisor factorisation e = e_d·e_m proved (`truncMobius_coprime_split`, `truncMobius_gamma_split`); smooth/rough split at z₀ = X^(1/420) with `block20_gcd_smooth_rough` (gcd(d,m)=1) and `bigOmega_rough_le_420`.

BILINEAR SOURCE COMPILER:
`template_product_split` (∏ all = u·v), `template_predicate_split`, `template_mass_split`, `fixed_template_source_factorisation` (ξ_π(u)·κ_π(v) once external inputs are supplied), with the remaining joint predicate exposed as `joint_coprimality_predicate_not_factorisable`. ξ/κ are defined from the packed block grammar (`mobius_factor_occurs_once`, `ordered_block_convolution`), and the divisor-norm bounds are the uninhabited `GeneratedCoefficientNormInput`.

TYPE-II WINDOW:
Proved finite: ε_* ≤ selectedMass < ε_* + σ_* = ν₀ − ε_* (`typeII_window_from_first_crossing`, `typeII_window_endpoint`, `typeII_size_window`); E is template-fixed (`template_selection_not_recomputed`). The log-mass → literal X-power conversion is kept as an explicit input, not faked.

THREE-SMALL-PRIME STATUS:
SUPERSESSION CANDIDATE / SOURCE COVERAGE OPEN; explicitly NOT false (`threeSmallPrime_not_false`, `threeSmallPrime_class_is_nonempty`, conditional `threeSmallPrime_supersession_of_coverage`).

PERRON SOCKET:
`PerronConditionRemovalInput` — granular (source cutoff, truncated integral representation, kernel K(τ), vertical range, kernel L¹ budget, boundary-strip source and estimate, truncation error, exact reconstruction), uninhabited, with a proved conditional compiler to `SeparatedPrefixCoefficientFamily`; C_Perron = 1 recorded as external audit metadata only.

BOUNDARY ROUTER:
`PerronBoundaryRouterInput`, uninhabited, plus the firewall theorems `boundaryRouter_preserves_literal_source` and `smoothed_certificate_is_a_different_source` (no replacement of H_* by a smoothed certificate).

GENERATED TYPE-II SOCKET:
`Block20GeneratedTypeIIInput` quantifies only over actual Block20 templates, actual ξ_π/κ_π, the supported window, both signs, physical weights. Uninhabited. Conditional compiler `k0_uniform_fragmentation_compiler` to `K0UniformFragmentationConclusion`, which is not inhabited.

CURRENT MAIN-LINE ANALYTIC RESIDUAL:
287-K0-SP2-BLOCK20-GENERATED-TYPEII45

EFFECTIVITY RESIDUAL:
287-EXCEPTIONAL-MAINTERM-COMPARISON-ADAPTER45 (uninhabited adapter, all three routes left undecided, conditional compiler to `EffectiveSmallQLowConductorConclusion`).

FCL: OPEN
ERDOS287: OPEN

TARGETED BUILDS: all new modules built individually, 0 errors.

FULL BUILD: `lake build` — 8235 jobs, 0 errors. Only the pre-existing linter warning in the historical file `RequestProject/Erdos287/FixedCertificateSmoothParity.lean:60` remains; it was left untouched.

AXIOM AUDIT: `RequestProject/Status/AxiomAuditErdos287Block20.lean` prints axioms for every principal new declaration — all are subsets of {propext, Classical.choice, Quot.sound}. Trust scan of the new files: zero sorry, admit, axiom, opaque, unsafe, native_decide, @[implemented_by]. No analytic or source socket of this pass has an inhabitant anywhere in the repository.

FILES: added `RequestProject/CurrentProgramme/{FixedCertificateBalancedSevenSourceSeal, Block20PackingCompiler, Block20LargePrimePowerRouter, Block20GeneratedBilinearCompiler, PerronConditionRemovalCompiler, ExceptionalMainTermComparisonAdapter}.lean`, `RequestProject/Status/{CurrentStatusErdos287Block20, AxiomAuditErdos287Block20}.lean`, and `ERDOS287_BLOCK20_DELTA_SAFE_BANK_REPORT.md`. `RequestProject/Main.lean` received import lines only. No historical file was otherwise modified.

COMMITS: staged in phases (source seal; packing/bilinear compiler; Perron/generated Type-II/effectivity sockets; status + audit + Main imports + report).

PUSH: all commits pushed to origin.

FINAL FIREWALL: this formal layer certifies finite source algebra, deterministic Block20 packing, source dependency graphs and conditional compilers only. It does NOT prove 287-K0-SP2-BLOCK20-GENERATED-TYPEII45, Perron analytic error estimates, the exceptional comparison adapter, FCL, or Erdős #287.

ERDOS287 OPEN —
FIRST EXACT MAIN-LINE ANALYTIC RESIDUAL:
287-K0-SP2-BLOCK20-GENERATED-TYPEII45

# Summary of changes for run 2992f52e-6ca3-4d37-b918-35cb1438b1a0
The Balanced7 hostile-audit safe bank is complete, built, and pushed. All work was append-only: no historical V15–V24 / SP-2 / PostBalanced7Pro file and no summary file was modified.

**Files added**

`RequestProject/HostileAudit/`
- `BalancedSevenSP2SourceAdapter.lean` (§2) — `truncMobius_of_primeProduct`, `truncMobius_sevenBox_eq_neg20` (the literal finite identity `H_*(P) = 1−7+21−35 = −20`), `subsetAlternatingSum_eq_binomial`, `boxWeight` with `norm_boxWeight_le_one` / `boxWeight_eq_omegaBox` (|phase| = 1, 0 ≤ V ≤ 1), the seal structure `BalancedSevenSP2SourceSeal` (left **uninhabited**), `seal_rigidity`, `sp2SourceSeal_not_automatic`.
- `GeneralModulusInducedCharacter.lean` (§3) — `induced_character_pointwise` (χ_r(n) = χ*(n)·1_{gcd(n,j)=1}, no squarefreeness or gcd(f,j)=1 hypotheses), `inducedSpec_holds_for_nonSquarefree_modulus`, `coprimeIndicator_moebius_expansion`, `induced_character_moebius_form`.
- `TotientComplementaryFactor.lean` (§4) — `totient_mul_ge`, `totient_gcd_exact`, `complementary_factor_bound` (f > D ∧ R ≤ f·j < 2R ⇒ j < 2R/D), `divisorVariable_ne_complementaryFactor` firewall.
- `GeneralModulusConductorSplitLargeSieve.lean` (§5) — uninhabited `PrimitiveWeightedLargeSieveInput` and `DivisorSumPolylogInput`, plus the conditional `general_modulus_cell_bound` and `general_modulus_conductorSplit_compiler`.
- `SmallROwnerCapacity.lean` (§7) — `smallR_source_eq_principal_add_defect` and the exact defect identity, `smallR_owner_assignment` (principal → EulerPrincipal, defect → SmallRDirect), `smallR_modulus_capacity` (q ≥ X^{2/3}), uninhabited `SmallRPrincipalCapacityInput`.
- `ShortTResidueGeometry.lean` (§8) — `shortT_unique_forbidden_class` (∃! residue class when ℓ ∤ q), `shortT_constant_class_of_dvd`, the rational scale ledger 2/105 < 15/105, `smallPrime_not_dividing_YscaleProduct`; the Selberg estimate stays uninhabited as `BalancedSevenShortTSieveInput`.
- `ShiuHypothesisCompiler.lean` (§9) — exponent map 5/7, 3/4, margin 1/28; `shiu_shift_coprime` (gcd(±1, 2w′) = 1); uninhabited `BalancedSevenShiuInput` with a conditional consumer.
- `RawRawVarianceCompiler.lean` (§10) — `rawRaw_variance_bound` with the corrected `log^{-5}` saving, `rawRaw_saving_is_five_not_ten` (explicit refutation of `log^{-10}`), `cross_variance_bound` (`log^{-15/2}`) and the principal `log^{-10}` bound.
- `HardAmplitudeExponentCompiler.lean` (§11) — reuses `C_ext = 1`, `hard_amplitude_product` (M·W5 = X with M = X^{2/7}, W5 = X^{5/7}), `hard_cell_log_budget` (−5/2), `hard_dyadic_summation` (−3/2), uninhabited `HardAmplitudeAsymptoticInterface` for the o(1).
- `FullQExactReassembly.lean` (§12) — literal boundary ownership of the disjoint partition SmallQ / SmallR / Hard, `region_principals_sum_eq_full`, `no_region_owns_the_full_principal`, `fullQ_no_double_spending`, `even_q_is_impossible`, `q_coprime_twoP`.
- `EffectiveLowConductorExceptionalPNT.lean` (§15) — uninhabited `EffectiveLowConductorExceptionalPNTInput` (effective constants, exceptional-character secondary term, smooth Y-scale weight, f ≤ log^30 X, Mellin range, induction to q), the conditional consumer to `EffectiveSmallQLowConductorTarget`, and `effective_socket_is_not_siegelWalfisz`.
- `BalancedSevenHostileAuditCompiler.lean` (§13) — `BalancedSevenHostileAuditInputs` (exactly the eight audited fields), the conditional `balancedSeven_hostileAudit_compiler`, and `hostile_audit_is_not_a_lean_proof`.

`RequestProject/Status/`
- `CurrentStatusErdos287Balanced7HostileAudit.lean` (§14, §6, §16) — the new append-only ledger with the recommended rows, the two **RETRACTED** death certificates with their reasons, the downstream frontier rows, `ledger_is_honest`, `rawRaw_row_uses_the_corrected_exponent`; no `Status.closed` row, ERDOS287 and FCL remain `open_`.
- `AxiomAuditErdos287Balanced7HostileAudit.lean` (§17) — `#print axioms` over every principal new declaration.

`RequestProject/Main.lean` — import lines only. Report: `ERDOS287_BALANCED7_HOSTILE_AUDIT_SAFE_BANK_REPORT.md`, containing the mandated final block and final firewall.

**Build:** `lake build` succeeds — 8227 jobs, 0 errors. The only warning in the repository is the pre-existing linter note at `RequestProject/Erdos287/FixedCertificateSmoothParity.lean:60`, which was left untouched.

**Trust:** no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `@[implemented_by]` occurs in any new file (the only textual hits are prose in docstrings describing the scan). `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound` for the new principal declarations. Every analytic/source interface of this layer is uninhabited, each accompanied by a refutation theorem exhibiting explicit failing data.

**Verdicts.** BALANCED7 SOURCE SEAL: **SOURCE_OPEN** — the finite `H_*(P) = −20` identity and the smooth-box weight bounds are kernel-proved, but the literal identification of the compiler-consumed packet with the repository's fixed-certificate SP-2 packet could not be derived from the current definitions, so Balanced7 is **not** recorded as source-sealed. SMALLQ, SMALLR GENERAL MODULUS, SHORT-t, SHIU, RAW-RAW: hostile-audited external pass recorded as conditional compilers only. SMALLR OWNER and FULL-q OWNER: proved algebraically. BALANCED7: research/paper pass, not a Lean analytic theorem; Balanced7-effective open. FCL and ERDOS287 remain open, and nothing is claimed closed.

# Summary of changes for run 0b028c11-5b14-4718-88f5-d9d6ac7b179f
## Post-Balanced7 safe bank — completed (append-only)

The earlier BALANCED7 post-audit repair bank was already in place; this session completed the follow-on **conductor-split 34LS / SmallR owner / hard-δ / small-prime-prefix Type-II** pass. Everything is append-only: no historical V15–V24 / SP-2 bank, status row, report, or pass-1 module was modified.

### Files added (all under the requested `RequestProject/CurrentProgramme/` and `RequestProject/Status/`)

- `CurrentProgramme/SevenBoxPrimeWeights.lean`, `CurrentProgramme/PrimeTupleMultiplicity.lean` — prime-supported seven-box weights; exact labelled multiplicity `≤ k!`, giving `∑|a₃|² ≤ 6·∏E` and `∑|b₄|² ≤ 24·∏E` (repeated primes included, no injectivity assumed).
- `CurrentProgramme/ConductorSplitLargeSieve.lean` — character families supplied as data (no ambient character-API dependence), literal character sums, the **exact conductor split** (cover / disjoint / monotone / reassembly), and the Möbius expansion of the coprimality indicator.
- `CurrentProgramme/LowConductorSiegelWalfisz.lean` — internal cutoff `(log X)^30`, a proof that it is a *different function* from the physical cutoff `X^{1/3}`, an explicitly **ineffective** Siegel–Walfisz socket, and a finite aggregation consumer.
- `CurrentProgramme/SmallQ34LSCompiler.lean` — three-child `ε/3` bundle → SmallQ target bound, plus a proof that the outstanding obligation really is the normalisation child.
- `CurrentProgramme/SmallPrimePrefix.lean` — `z₀ = X^{1/420}`; smooth/rough factorisation with **existence and uniqueness**; the `Ω(d) ≥ 3` firewall; the truncated-Möbius **non-factorisation** obstruction (explicit counterexample `M₂(2)=0` vs `M₂(3)=1`); literal residual sum and its socket.
- `CurrentProgramme/PostRepairOwnerCompiler.lean` — refined owner map (6 owners / 9 cells, dedicated short-`t` and `Ω(d)≥3` owners), unique ownership, no double spending, conditional compiler.
- `CurrentProgramme/UniformFragmentationCompiler.lean` — K0 uniform fragmentation reassembly compiler, banked as REDUCED / CONDITIONAL and never activated.
- `Status/CurrentStatusErdos287PostBalanced7Pro.lean`, `Status/AxiomAuditErdos287PostBalanced7Pro.lean` — new append-only ledger with `no_closed_rows`, `erdos287_open`, `balanced7_open`, `k0_is_reduced_not_closed`, residual-ordering and honesty theorems; full `#print axioms` audit.
- `RequestProject/Main.lean` — import lines only, inserted inside the import block.
- `ERDOS287_POST_BALANCED7_PRO_SAFE_BANK_REPORT.md` — full report with the mandated final block and firewall.

### Verification

- **Build:** full `lake build` succeeds (8213 jobs, 0 errors). One pre-existing, unrelated linter warning in `RequestProject/Erdos287/FixedCertificateSmoothParity.lean:60` remains untouched.
- **Trust scan:** zero occurrences of `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `@[implemented_by]` in all new files.
- **Axioms:** every principal declaration of this pass depends only on `propext`, `Classical.choice`, `Quot.sound`.
- **Interfaces:** every analytic/source socket is uninhabited, each with an accompanying refutation theorem exhibiting explicit failing data.

### Status kept open

BALANCED7, FCL and Erdős #287 remain **open**; no `closed` row exists. The first exact residual is the SmallQ 3+4 coefficient/source normalisation; the first exact downstream residual is the `Ω(d) ≥ 3` small-prime-prefix Type-II input. The hard-θ `δ = 1/21` ledger is banked as rational/order arithmetic only.

Note on naming: the requested `TwinPrimeProject.*` namespace does not exist in this repository, so the established `Erdos287.*` convention was used (`Erdos287.PostBalanced7Pro`, `Erdos287.PostBalanced7ProStatus`); this is recorded in the report. The referenced research-ledger markdown file is not present in the repository, so Lean declarations were used as the sole authority for formal claims.


# Summary of changes for run 0c8f71d8-a099-4200-a479-de6e0f37f241
Continued the Erdős #287 repository in place, append-only. The comparison / aggregate-Euler safe bank (V23) was already banked and pushed; this session completed and banked the follow-on **V24 full-`q` Balanced7 provider-exhaustiveness layer**, chosen as the next consistent version identifier after V23. `ARISTOTLE_SUMMARY.md` was not modified, and the V20/V21/V22/SP-2/V23 layers are untouched.

**Files added** (all under `RequestProject/`):
- `Erdos287/PhysicalLogPrefactorRepair3221.lean` — repaired physical log prefactor `C_ext = 1`, machine-checked retraction of the old `C_ext = 0` normalization, `Q = X^{3/5}` numerology (net log exponent `−5/2`, signed margin `3`).
- `Erdos287/SP2LiteralPhysicalSource3221.lean` — literal one-sign SP-2 physical source, two-sign reassembly, and the non-circularity firewall that `2B(P)` is not recoverable from the principal q-cell.
- `Erdos287/EulerUniformityLayer3221.lean` — repaired Euler local factor with explicit bound `|f − 1| ≤ 6·p^{−7/4}` (real `w ≥ −1/4`), at most seven on-`P` corrections, `H_P(0) = 2B(P)`, plus an uninhabited analytic uniformity interface.
- `Erdos287/FullQStructuralPartition3221.lean` — cut `U = X^{1/3}`, exact SmallQ/SmallR/Hard cover, disjointness and reassembly, dyadic partition of unity with the proved firewall that smooth supports need not be disjoint, and provider ownership.
- `Erdos287/SmallQSmallRAdapters3221.lean` — literal sector sums with exact reassembly; uninhabited SmallQ and switched-SmallR Type-I adapter interfaces plus conditional consumers; proof that `q ↔ r` is not a symmetry of the sector decomposition.
- `Erdos287/HardDyadicProviders3221.lean` — `Q = X^{3/5}` cell metadata (with `Q·R = X`), hard dyadic census, and a *refuted* exhaustiveness interface.
- `Erdos287/BalancedSevenFullQCompiler3221.lean` — conditional full-`q` compiler and firewalls, including the proof that the antecedent bundle is currently satisfiable by no parameter set.
- `Status/Erdos287V24Status.lean`, `Status/AxiomAuditErdos287V24.lean`; `Main.lean` extended with import lines only; report `ERDOS287_FULLQ_BALANCED7_PROVIDER_SAFE_BANK_REPORT.md` with the mandated final block and final firewall.

**Build and trust:** `lake build` completes successfully — 8190 jobs, 0 errors; the only warnings are pre-existing linter notes in older files (zero warnings in the new files). A scan of every new file finds no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `@[implemented_by]`. `#print axioms` on all principal new declarations shows only `propext`, `Classical.choice`, `Quot.sound` (several depend on no axioms).

**Status recorded:** finite/structural layers PASS; aggregate-Euler uniformity, SmallQ and SmallR adapters remain external and uninhabited; provider exhaustiveness FAILS as a global claim (proved); `SP2-BALANCED7-FULL-Q45` OPEN (conditional compiler only); Balanced7 asymptotic and effective statuses kept separate, both open; post-Balanced7 census not activated; first exact residual `AFFINE287-SP2-SMALLQ-TYPEI-ADAPTER45`; **Erdős #287 remains OPEN**. All work is committed and pushed.

# Summary of changes for run ffa98343-83d2-4670-8663-8a6833eebf96
## What was done

Continued the Erdős #287 repository **in place, append-only**. Nothing earlier was deleted or rewritten, and `ARISTOTLE_SUMMARY.md` was not touched. Three layers are now banked: **V21** (two-high-projector / five-box sieve / source-normalization firewall), **V22** (source forensics + safe bad-character log re-ledger) and **SP-2** (direct Balanced7 source repair). Each has its own report with the mandated final block.

### V21 (completed)
Lean modules under `RequestProject/Erdos287/` — `TwoHighProjector3221`, `DoubleOrthogonalityFiveBox3221`, `BadCharacterCount3221`, `PrimeBoxNormalization3221`, `ShortShiftSieve3221`, `ShiuDivisorAverage3221`, `HighProjectorCutoff3221`, `PhysicalLogBudget3221`, `OuterTwoPrimeBlock3221`, `BalancedSevenV21Compiler`, plus `RequestProject/Status/Erdos287V21Status` and `AxiomAuditErdos287V21`. The missing deliverable, `ERDOS287_V21_TWO_PROJECTOR_SAFE_REPAIR_BANK_REPORT.md` (sections A–X + final block), has now been written.

Key proved content: the exact two-variable indicator identity giving `HH = AA − BA − AB + BB` with explicit no-omission / no-overlap / no-double-counting lemmas; the pre-projector variance reconstructed from the repository's own character source, with the ξ-form equivalence **proved** rather than assumed; five-box double orthogonality (`−2smW ≡ 1`, `−2smW′ ≡ 1`, `W ≡ W′ (mod q)`, `W − W′ = qt`, `q ∣ 2mW′+s`, `(q,W′)=1`, both signs); the safe finite bad-character count `#Bad ≤ D(D+1)/2 + 1 ≤ (D+1)²` (the `D·τ(q)` heuristic is **not** banked); the kernel-checked exponent ledger `39/35`, `31/35`, sum `2`; the symbolic four-channel log compilers with `BA/AB/BB` kept separate; the outer/inner seven-box partition and prime-density anti-double-spending firewall; the phase-alignment lemma repairing the circular provenance; and the conditional LOGVAR / Balanced7 compilers.

### V22 (new)
`BadCharacterLogLedger3221`, `Ford723BalancedSevenAdapter3221`, `PrimeBoxL1Normalization3221`, `TwoProjectorPhysicalClosure3221`, `Status/Erdos287V22Status`, `Status/AxiomAuditErdos287V22`, report `ERDOS287_V22_SOURCE_FORENSICS_SAFE_BANK_REPORT.md`. The safe `(D+1)²` count is pushed through the log arithmetic with abstract cutoff exponent: `Cvar(B0) = min(5, 15/2 − 2B0, 10 − 4B0)`, kernel samples `Cvar(1)=5`, `Cvar(2)=2`, `Cvar(3)=−2`. Closure criterion proved in exact form: `netLogExponent < −1 ⟺ Cvar > 2·Cext`, with the capacity table for `B0 = 1, 2, 3`.

### SP-2 (new)
`SP2DirectSourceAdapter3221`, `SP2PrimeBoxWeights3221`, `SP2ClosureCompiler3221`, `Status/Erdos287SP2Status`, `Status/AxiomAuditErdos287SP2`, report `ERDOS287_SP2_DIRECT_BALANCED7_SAFE_BANK_REPORT.md`. Source forensics found **no** `G_*`/`H_*` object; what exists is the fixed smooth-parity certificate (`truncMobius`, the `k=0, J=∅` packet), so the Ford-(7.23) adapter is recorded as `RETRACTED / NOT THE LITERAL SOURCE` (file preserved). Proved: the divisor-depth threshold pinning `r = 3`; `∑_{j≤3}(−1)^j C(7,j) = −20` and `64` of `128` subsets; and — the substantive repair — the pointwise law `|ω_i(p)| ≤ 1` for the literal weight `V_{i,λ}` as a **theorem**, not an interface field, with `L¹` mass equal to the cell cardinality. The closure compiler gives `−(2+5)/2 + 0 = −7/2 < −1` contingent on `Cext = 0`, with both `sp2_closure_margin` and `sp2_closure_fails_without_audit` making the contingency explicit.

## Required final block

```
FILES ADDED (V21): TwoHighProjector3221, DoubleOrthogonalityFiveBox3221,
BadCharacterCount3221, PrimeBoxNormalization3221, ShortShiftSieve3221,
ShiuDivisorAverage3221, HighProjectorCutoff3221, PhysicalLogBudget3221,
OuterTwoPrimeBlock3221, BalancedSevenV21Compiler, Status/Erdos287V21Status,
Status/AxiomAuditErdos287V21, ERDOS287_V21_TWO_PROJECTOR_SAFE_REPAIR_BANK_REPORT.md
FILES ADDED (V22): BadCharacterLogLedger3221, Ford723BalancedSevenAdapter3221,
PrimeBoxL1Normalization3221, TwoProjectorPhysicalClosure3221,
Status/Erdos287V22Status, Status/AxiomAuditErdos287V22,
ERDOS287_V22_SOURCE_FORENSICS_SAFE_BANK_REPORT.md
FILES ADDED (SP-2): SP2DirectSourceAdapter3221, SP2PrimeBoxWeights3221,
SP2ClosureCompiler3221, Status/Erdos287SP2Status, Status/AxiomAuditErdos287SP2,
ERDOS287_SP2_DIRECT_BALANCED7_SAFE_BANK_REPORT.md

FILES MODIFIED: RequestProject/Main.lean (import lines appended only)

V20 PRESERVED: YES
OLD HHH CLOSURE PROOF: RETRACTED (object and socket preserved)
TWO-HIGHPROJECTOR ALGEBRA: EXACT / ALGEBRAIC PASS
DOUBLE ORTHOGONALITY: EXACT PASS
BAD-CHARACTER SAFE COUNT: FINITE PASS, #Bad ≤ (D+1)^2
PRIMEBOX NORMALIZATION: pointwise law PROVED for V_{i,λ}; identification SOURCE_OPEN
CUTOFF COMPATIBILITY: SOURCE_OPEN / UNINHABITED
PHYSICAL LOG PREFACTOR: SOURCE_OPEN / UNINHABITED
SHIU INTERFACE: EXTERNAL / UNINHABITED (φ(2W)=φ(W) proved)
SHORT-t SIEVE INTERFACE: EXTERNAL / UNINHABITED (z = T^(1/20), dimension 1)
BA / AB / BB: SEPARATE CHANNELS, BOUNDS ARE HYPOTHESES, NOT THEOREMS
OUTER TWO-PRIME L2: ALGEBRA PROVED, DENSITY ANTECEDENT UNINHABITED
TWO-PROJECTOR CLOSURE: CONDITIONAL (compiler proved, no inhabitant)
3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45: OPEN / CONDITIONAL — NOT CLOSED
SIXTH MOMENT: OPEN STRONGER SUFFICIENT FALLBACK (not deleted, not marked false)
COMPARISON: SOURCE_OPEN
BALANCED7: OPEN
ERDOS287: OPEN
FIRST EXACT RESIDUAL: V21/V22 — BALANCED7-PRIMEBOX-L1-NORMALIZATION45;
  after SP-2 — COMPARISON-SMALLCOND-EXCEPTIONAL-SPLICE45
LAKE BUILD: SUCCESS — 8171 jobs, 0 errors; new modules emit 0 warnings
  (the warnings a from-source rebuild reports are pre-existing linter notes in older modules)
TRUST SCAN: ZERO occurrences of sorry / admit / axiom / opaque / unsafe /
  native_decide / @[implemented_by] in code across all new files (only prose mentions
  in docstrings); #print axioms on every principal new declaration returns only
  [propext, Classical.choice, Quot.sound]
PUBLIC-MAIN SYNC: Main.lean extended with imports only; full build clean
```

**Final firewall.** No source-open or external analytic interface was inhabited merely to make a compiler execute. Nothing in V21, V22 or SP-2 proves Erdős #287, and nothing proves Balanced7 unless the explicit analytic/source antecedents — the SP-2 source identification, the prime count, the sieve and Shiu inputs, the `Cext = 0` audit and the comparison splice — are separately supplied. Erdős #287 and Balanced7 both remain OPEN.


# Summary of changes for run 8a33d15a-18fa-43fa-b470-68e98c06199d
## Erdős #287 — V20 safe bank: completed and verified

The existing repository was continued **in place, append-only**. Nothing was deleted or rewritten; `ARISTOTLE_SUMMARY.md` was left untouched.

### Files added
- `RequestProject/Erdos287/HighConductorCharacterGram3221.lean`
- `RequestProject/Erdos287/FiveBoxCharacterFactorization3221.lean`
- `RequestProject/Erdos287/ConductorRouter3221.lean`
- `RequestProject/Erdos287/HighQuotientShiftedGram3221.lean`
- `RequestProject/Erdos287/HighConductorSixthMoment3221.lean`
- `RequestProject/Erdos287/BalancedSevenV20Compiler.lean`
- `RequestProject/Status/Erdos287V20Status.lean`
- `RequestProject/Status/AxiomAuditErdos287V20.lean`
- `ERDOS287_V20_HIGHQUOTIENT_HHH_SAFE_BANK_REPORT.md` (report sections A–V and the mandated final block)

### File modified
- `RequestProject/Main.lean` — import lines appended only.

### Principal results proved (all sorry-free)
- **Inverse-sampled character algebra:** `inverseSample_character_identity` (conj(χ(aₘ)) = χ(−2s)·χ(m), with `s²=1` and `2m` a unit stated explicitly), `affineSample_character_factor`, `cHigh_inverseSampled_expansion`.
- **Five-box factorisation:** `fiveBox_characterTransform_eq_prod_five`, `fiveBox_characterTransform_factor`, `pairBlockSum_eq_mul`, `sum_mul_sum5`.
- **Exact m-Gram (central V20 identity):** `inverseSampledVariance_eq_characterGram`, from `charSource_variance_eq_gram`; supporting `shortMGram`, `autocorr`, `autocorr_reindex`, `fixedModulus_samePrimitive_induced_unique`.
- **Diagonal / low-quotient children:** `characterGram_diag_split`, `autocorr_principal_highCoeff`, `lowConductor_card_le`, `lowQuotient_child_le`, plus the conditional compilers `highCondDiagonal_of_largeSieve`, `lowQuotient_child_of_diagonal_budget`.
- **Capacity firewalls:** `gram_parseval`, `autocorr_l2_sq_le`, `separateL2_compiler`, `separateGramL2_capacity_deficit` (12/35), `pointwiseBurgess_capacity_deficit` (51/112), `diagonal_power_room_rational`/`_rpow` (4/35).
- **Conductor-pair router:** `ConductorCell`, `RouterCondition`, `conductorCell_routed`, `router_case_A/B/C`, `router_threshold_identity` (5/14 + 31/80 = 417/560).
- **HHH frontier:** `SurvivingHHHConductorCell`, the exact object `hhhGram` (no analytic assumption in its definition, non-vacuity witnessed by `probeHHHData_gram`), the open socket `HighQuotientFiveBoxShiftedGram3221Input`, and the reassembly compiler `logVar_of_four_channels`.
- **Sixth-moment bridge:** `injOn_affineSample`, `sixthMoment_holder_at`, `sixthMoment_holder_over_q`, `sixthMoment_power_margin` (1/105).
- **Same-B0 comparison firewall and Balanced7 compiler:** `highConductorCutoff`, `MuLogComparisonAtCutoff`, `comparison_cutoff_must_match`, `balancedSeven_of_v20_package`, `v20_package_cutoff_consistent`.
- **Non-vacuity / anti-circularity:** `largeSieve_not_automatic`, `pointwiseBurgess_not_automatic`, `hhh_input_not_automatic_v20`, `sixthMoment_input_not_automatic_v20`, `comparison_not_automatic_v20`, `logVar_cannot_construct_hhh`, `balancedSeven_compiler_cannot_construct_comparison`.
- **Machine ledger:** `controlling_analytic_residual_unique`, `sixthMoment_not_controlling`, `logVar_reduced_not_proved`, `capacity_firewalls_are_not_proofs`, `children_are_conditional`, `comparison_source_open`, `terminal_nodes_open` (kernel `decide`).

### Build and trust
- `lake build`: **success — 8148 jobs, 0 errors, 0 warnings.**
- Placeholder scan of all new Lean files for `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `@[implemented_by]`: **zero occurrences.**
- `#print axioms` on every principal new declaration reports either `[propext, Classical.choice, Quot.sound]` or no axioms at all. No external analytic or source interface is inhabited anywhere.

### Status
Erdős #287 is **OPEN** and Balanced7 is **OPEN**; nothing here claims either. The first exact analytic residual is the high-quotient five-box shifted character Gram (`3221-HIGHQUOTIENT-FIVEBOX-SHIFTED-GRAM45`), with the sixth-moment route recorded only as a stronger sufficient open alternative, and comparison recorded as SOURCE_OPEN.


# Summary of changes for run 92ea5d66-6a71-4baf-b85e-90be38cdaccc
## Erdős #287 — V19 pre-Poisson / high-conductor safe bank (append-only)

**Erdős #287 remains OPEN. Balanced7 remains OPEN.** Nothing added proves either, no analytic or source interface is inhabited, and no `axiom` was introduced.

### A. Regression
Pre-edit `lake build`: success, 8135 jobs, 0 errors, tree clean. Every named prerequisite was located and reused unchanged (`FactorialEulerPolarization`, `FactorialEulerLocal`, `FactorialPolarizationLinearity`, `PascadiParameterLedger`, `NormalForm3221`, `MovingPhaseProvider3221`, `FactorialEndpoint3221Adapter`, `Erdos287V18Status`, and the whole V17 3221 finite/exponent bank). No existing theorem was restated, weakened, renamed or deleted; the seven-prime polarization was not redone (the V17 grouping and exponents are reused verbatim). Post-edit build: **success, 8140 jobs, 0 errors**.

**Files changed** — added `RequestProject/Erdos287/PrePoissonDensity3221.lean`, `RequestProject/Erdos287/HighConductorVariance3221.lean`, `RequestProject/Erdos287/CharacterGram3221.lean`, `RequestProject/Erdos287/BalancedSevenV19Compiler.lean`, `RequestProject/Status/Erdos287V19Status.lean`, `ERDOS287_V19_PREPOISSON_HIGHCOND_SAFE_BANK_REPORT.md`; edited `RequestProject/Main.lean` (five import lines only).

### B. Frontier reset
A new V19 metadata ledger (`Erdos287.V19Status.ledger`) records the V18 DI/small-`Z` route as *superseded as controlling frontier* — not false — plus `SOURCE_MISMATCH`, `CONDITIONAL PROVIDER METADATA` and `RETIRED AS CURRENT ROUTE` for the other three nodes. `controlling_analytic_node_unique` proves the inverse-sampled high-conductor log-variance node is the **unique** `OPEN_ANALYTIC` node. No theorem converts a label into a mathematical claim, so no analytic falsity is derived from metadata.

### C–H. New Lean-proved content (all sorry-free)
* **Affine divisor identity** — `affineResidue_iff_dvd_two_mul_add`: for odd `q`, `m·w ≡ a (mod q) ↔ q ∣ 2mw + s`; plus `balancedSeven_affine_divisor_condition`, `exists_affineResidue`.
* **First Cauchy / μ-sign** — `firstCauchy_sign_consumption`, `postCauchy_weight_sign_invariant`, and the firewall `firstCauchy_loses_sign_information` (the signed weight is provably not retained).
* **High-conductor residue source** — `residueSum`, `residueSum_sum_over_classes`. Dirichlet-character machinery *is* available, so the projection is literal, not a placeholder.
* **RR/RK/KK** — `normSq_sub_reassembly`, `highConductorEnergy_reassembles_crossTerms` (algebraic only; no claim that the physical comparison term is matched).
* **Divisor density** — `sampled_q_card_le_divisorCount(_affine)`; `τ(n)=X^{o(1)}` is *not* proved or assumed and is isolated as the uninhabited `DivisorGrowthInput`.
* **Second-copy density** — `secondCopy_shell_iff`, `congruence_interval_card_le` (`q·# ≤ (b−a)+q`), floor variant, `secondCopy_card_le_one_add_quotient`; exact ℤ arithmetic, no real intervals.
* **Combined compiler** — `sampledQuadBox_card_le`, with no `X`-exponent inside.
* **39/35 ledger** — `prePoisson_density_exponent = 39/35`, `cauchy_prefactor_exponent = 31/35`, `highCond_naturalScale_exponent = 39/35`, `naturalScale_matches_density` (`CAPACITY_ONLY`).
* **Retired-lane arithmetic** — `BC3221_capacity_deficit_arithmetic` (47/350 > 0), `DRZ3221_capacity_deficit_arithmetic` (11/84 > 0); metadata only, no external theorem formalised or assumed.
* **Variance socket** — `InverseSampledHighCond3221Data` (pure data, no free `Prop`), `Vhi`, and the load-bearing `samplePoint_iff_affineSampled` identifying `−s(2m)⁻¹` with `q ∣ 2mw+s`.
* **Character Gram** — `totient_mul_residueSum_eq_sum_char`, the proved projection `residueSum_eq_cLow_add_cHigh`, `gram_expansion`, `highResidue_energy_gram`, `inverseSampled_highResidue_gram`, `cHat_fiveBox_factorisation`, `cHat_twoBox_factorisation`. Identities only; no character-sum bounds.

### K/O/P. Socket, compiler, non-vacuity
`InverseSampledHighCondLogVar3221Input` (target `V_hi ≤ naturalScale / Lsave`, explicit positive saving) is **never inhabited**; it occurs only as a declaration and as a hypothesis. The compiler `cauchyPrefactor_of_firstCauchy → highCond_source_bound_of_logVar → factorialEndpoint_of_highCondLogVar → balancedSeven_of_highCondLogVar` keeps the budget explicit (`prefactor·(scale/Lsave) ≤ E²`) and the comparison channel independent (`E + err`). Non-automaticity proved: `highCondLogVar_not_automatic`, `cauchyPrefactor_not_automatic`, `balancedSeven_not_automatic`, `comparison_stays_independent` (reusing the V18 refutation).

### Q. Build / axiom audit
`lake build` succeeds (8140 jobs, 0 errors). The five new files contain **no** `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `@[implemented_by]` (the only textual hits are the words inside doc comments). `#print axioms` is run on all 45 principal new theorems; every one reports only `propext`/`Classical.choice`/`Quot.sound` or a subset, and two ledger theorems report no axioms at all. No `sorryAx`, no `Lean.ofReduceBool`.

### R–U
Final status table, first source open (`AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45`), first analytic open, and the next unique action are written in `ERDOS287_V19_PREPOISSON_HIGHCOND_SAFE_BANK_REPORT.md`.

```
GATE / BALANCED7: OPEN
FCL: OPEN
WINDOWPAIRSUPPLY: OPEN
ERDOS287: OPEN
```
```
FIRST ANALYTIC OPEN:
    3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45.
```

# Summary of changes for run afd7b265-8510-432f-8f62-3e3efb4cb741
## Erdős #287 — V18: fixed-degree-seven source / normal-form / small-`Z` compiler

**ERDŐS #287 REMAINS OPEN.** Nothing added here proves it, nor Balanced7, nor the factorial signed endpoint, nor the comparison match, nor any Kuznetsov/Deshouillers–Iwaniec/Pascadi estimate. No `axiom` was added and no analytic or source interface was inhabited.

### Regression guard
Baseline build 8131 jobs / 0 errors; final build **8135 jobs / 0 errors**. Every named prerequisite was located and reused unchanged (`FactorialEulerPolarization.lean`, `FactorialEulerLocal.lean`, `FactorialPolarizationLinearity.lean`, `PascadiParameterLedger.lean`, `Erdos287V16Status.lean`, plus the whole V17 3221 bank and `FactorialOmega7SignedEndpoint`, `MuLogComparisonLowCondMatch`, `BalancedSevenPacketInput`). Nothing was redefined, renamed, weakened or deleted; work is append-only apart from four import lines.

### Files changed
Added `RequestProject/Erdos287/NormalForm3221.lean`, `RequestProject/Erdos287/MovingPhaseProvider3221.lean`, `RequestProject/Erdos287/FactorialEndpoint3221Adapter.lean`, `RequestProject/Status/Erdos287V18Status.lean`, `ERDOS287_3221_SAFE_BANK_REPORT.md`. Edited `RequestProject/Main.lean` (imports only).

### Status repair (the moving-phase overclaim)
`PASCADI101-LEVELWISE-PHASE-LS45 PASS`, `PASCADI102-MOVINGPHASE45 PASS`, `PASCADI39-MOVINGPHASE-EXTENSION45 PASS` and `3221-SOURCE-MOVINGPHASE-DI45 CLOSED` are **retracted as controlling status** (provenance kept, nothing deleted): a repository-wide search finds no declaration mentioning a levelwise/moving phase and no phase provider is inhabited. They are replaced by a metadata-only four-regime dictionary (A, B published; C conditional provider; D open analytic), with the proved separations `largeRange_not_published`, `smallRange_is_conditional`. None of A–D is an axiom.

### New Lean-proved content (sorry-free)
* **Normal-form source pin** — `BalancedSeven3221NormalForm` records the schematic completed child as an exact equality on explicit finite data (coprime `q=rs`, phase, coefficients, Kloosterman leg literally equal to the banked `kloostermanLike` of modulus `s·c`, unit/gcd/zero-mode/low-conductor routing), with **no free `Prop` field and no inhabitant**. Search finding: a Kloosterman-shaped sum with its exact unit-change identity exists in the repository; **no** dispersion, Poisson/completion, additive character, gcd-extraction or low-conductor projection of the physical source exists. Status `SOURCE_BLOCKED`.
* **Phase algebra** — `phase_int_add`, `phase_fract`, `phase_congr`, `norm_phase`, and `phase_leg_congr` (mod-1 representative invariance on the pinned data); `kloostLeg_unit_change`, `modulus_above_cut`, `factorisation_is_data`. The ω-dependence classification is recorded, not forced, with counterguard `omega_product_strictly_stronger` (`1·6 = 2·3`). No literal ω formula and no value for `Z_3221` are claimed — `Z`, `R0,S0,M0,N0,C0`, `Qlevel` exist only as fields.
* **Small-`Z` range compiler** — `InSmallZRange`, `inSmallZRange_iff` (`N₀>0 ⇒ Z ≤ 1 ∨ Z N₀ ≤ Q`), dichotomy, disjointness, nonvacuity witness; unconditional levelwise algebra `levelValue`, `completedValue_eq_sum_levelValue`, `completedValue_norm_le`; and the compiler `diKuznetsov_of_perLevelSmallZ` from the **uninhabited** `PerLevelPhaseSmallZ3221Input` plus an explicit level-count budget to the existing analytic socket.
* **Large-range firewall** — `LevelwisePhaseLargeRange3221Input` (uninhabited, `OPEN_ANALYTIC`) kept strictly apart by the proved `smallZ_largeRange_firewall`: the two inputs can never both apply to the same source.
* **Endpoint adapter** — `FactorialEndpoint3221SourceAdapter` (`SOURCE_OPEN`, uninhabited) exposes the missing bridge; `factorialEndpoint_of_smallZ` and `balancedSeven_of_smallZ` are proved compilers that reuse the earlier balanced-seven implication unchanged and keep error channels separate (`E + err`).
* **Non-vacuity firewall** — `endpoint_not_automatic`, `comparison_not_automatic`, `perLevelSmallZ_not_automatic`: each open interface genuinely constrains its data, so no compiler can be made unconditional by parameter choice. The Hilbert–Schmidt/nuclear-rank firewall is preserved.

### Audit
`lake build` succeeds (8135 jobs, 0 errors). A repository-wide scan for `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `@[implemented_by]` finds **zero occurrences in Lean code** (all matches are documentation prose). `#print axioms` is emitted at build time for the 25 principal new theorems; each reports a subset of `[propext, Classical.choice, Quot.sound]` (one reports none). No user axiom.

### Final block
```
REGRESSION: PASS
BUILD: SUCCESS (8135 jobs, 0 errors)
SORRY: NONE
USER AXIOMS: NONE

FACTORIAL EULER: PROVED_ALGEBRAIC
EXPECTED-TERM LINEARITY: PROVED_ALGEBRAIC
3221 GROUPING: PROVED_FINITE
3221 EXPONENT LEDGER: PROVED_ALGEBRAIC / CAPACITY_ONLY
SOURCE-ASSISTED DIAGONAL: PROVED_FINITE / CAPACITY_ONLY
OFFDIAGONAL t: PROVED_FINITE / CAPACITY_ONLY
EH NO-WRAP: PROVED_FINITE
EH RATIO ENERGY: CONDITIONAL_FINITE
LITERAL 3221 NORMAL FORM: SOURCE_BLOCKED
omega FORMULA: SOURCE_OPEN
Z_3221: SOURCE_OPEN
SMALL-Z RANGE ADAPTER: CONDITIONAL_COMPILER
LEVELWISE LARGE-RANGE PHASE: OPEN_ANALYTIC
3221 ANALYTIC CHILD: OPEN_ANALYTIC
FACTORIAL ENDPOINT: OPEN_ANALYTIC
COMPARISON: SOURCE_OPEN
BALANCED7: OPEN
FCL: OPEN
WINDOWPAIRSUPPLY: OPEN
ERDOS287: OPEN
```
First source open: the dispersion/completion (Poisson) identity for the physical balanced-seven source. First analytic open: the per-level small-`Z` estimate for the pinned source (and, separately, the large-range input). Next unique action: derive a completed finite Fourier/Poisson identity for the `m`-box in terms of `levelValue`, `phase` and `kloostermanLike`, i.e. produce the first genuine inhabitant of the pinned normal form from repository definitions. Full details in `ERDOS287_3221_SAFE_BANK_REPORT.md`; all work is committed and pushed.

# Summary of changes for run 5d1858c9-721b-40a2-8db0-d6de33736eb4
## Erdős #287 — V17: 3221 source-assisted dispersion safe bank

**ERDŐS #287 REMAINS OPEN.** Nothing in this run proves it, nor Balanced7, nor the factorial signed endpoint, nor any Deshouillers–Iwaniec/Kuznetsov estimate. No axiom was added.

### Baseline / regression
Baseline `lake build`: 8123 jobs, zero errors. Final: **8131 jobs, zero errors**. No V15/V16 statement was edited; work is append-only apart from eight import lines in `RequestProject/Main.lean`.

**Search finding:** the named prerequisites `UnconditionalDivisorBound.lean`, `FixedDepthConvolution.lean` and `card_divisors_in_range_le_mul_rpow` **do not exist** in this repository, and there is no product-energy bank, no residue-class interval count, and no completed Fourier/Poisson identity. Nothing was assumed to exist: the finite divisor/energy facts were proved from scratch, the missing source objects were reported rather than fabricated.

### Files added
`RequestProject/Erdos287/Exponent3221Ledger.lean`, `BalancedSeven3221Grouping.lean`, `SourceAssistedDiagonal3221.lean`, `OffDiagonal3221.lean`, `EHNoWrap3221.lean`, `DIKuznetsov3221Interface.lean`, `BalancedSeven3221Compiler.lean`, `RequestProject/Status/Erdos287V17Status.lean`, `ERDOS287_3221_V17_SAFE_BANK_REPORT.md`. Edited: `RequestProject/Main.lean` (imports only).

### Main proved theorems
* **Regrouping** — `sevenfold_regrouping` (with `prod_apply_tuples`, the reusable exact expansion of an iterated Dirichlet convolution over ordered tuples): the ordered seven-prime sum of the V16 polarization equals `∑_{e·a·b·c=m} η α β γ` with exact convolution multiplicities. Numerically cross-checked at `m = 192` (both sides `1511208`). Multiplicity firewall discharged: `grouping_not_injective` (two distinct prime 7-tuples, same `(e,m,n,ℓ)`) and `alpha_not_one_bounded` (`α(6)=2`), with the correct majorant `alpha_norm_le_card_divisors` (`‖α(a)‖ ≤ τ(a)`).
* **Exponent/range ledger** — exact ℚ arithmetic: `E+M+N+L=1`, `W−Q=4/35`, `H=11/35`, `E+H=16/35<Q` with margin `1/7`, `Texp=4/35`, diagonal margin `2/35`, the defect `(N+L)−Q=−1/35`, and the transcribed margins `1/10, 2/21, 19/35, 4/35, 2/35`.
* **Diagonal** — `fiberwise_energy_le`, `productFibre_card_le` (`τ²`), `modulus_divisor_count_le` with the load-bearing zero guard `modulus_count_zero_case`, `diagonal_parent_bound`, `sourceAssisted_diagonal_finite`.
* **Off-diagonal** — `offdiag_existsUnique_t`, `offdiag_t_ne_zero`, `offdiag_abs_t_le` (`|t|·Q_min ≤ 2W_max`), all over ℤ.
* **No-wrap / hostile audit** — `ratio_eq_iff_cross` (unit sector), `nowrap_eq_of_dvd_of_abs_lt`, `ratioCollision_samePrime`, `ratioCollision_distinctPrimes_param` (`h₁=ce₁, h₂=ce₂`), `ratioCollision_card_bound` (`≤ #E·#H + (#E)²·#C`), `ehRatioEnergy_le_explicit`. Audit verdict: the claimed order `E·H` is reproduced **with no divisor factor and no `X^{o(1)}` loss**, so the claim is not retracted — but it is banked only as `CONDITIONAL_FINITE`, since every statement carries the literal no-wrap size hypothesis.
* **Dictionary / socket / compiler** — `BalancedSeven3221CompletedSource` (concrete data + conditions, no free `Prop` field, no physical inhabitant), `DIKuznetsov3221Input` (source-specific, never inhabited, not an axiom), counterguards `slot_dependence_counterguard`, `zeroMode_separation_guard`, `modulus_factorisation_not_unique`, and the compilers `factorialEndpoint_of_3221`, `balancedSeven_of_3221` (reusing the V16 theorem unchanged). The bridge the 3221 child cannot supply is made explicit as the SOURCE-OPEN `Endpoint3221Decomposition`, never inhabited.

### Comparison source audit
`SOURCE_BLOCKED`. Missing definitions named exactly: `B(n)`/`4B(n)`, `M_phys`, the principal local density, the small-conductor subtraction, the exceptional-character convention, physical unit/nonunit routing. Nothing invented; polarization not redone.

### Audit
No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `@[implemented_by]` in Lean code (all matches are documentation prose). `#print axioms` is emitted for the 68 principal new theorems; every report across the repository is a subset of `[propext, Classical.choice, Quot.sound]`. Full A–V report in `ERDOS287_3221_V17_SAFE_BANK_REPORT.md`. Everything committed and pushed.

```
REGRESSION: NONE
BUILD: SUCCESS (8131 jobs, 0 errors)
SORRY: NONE
USER AXIOMS: NONE

FACTORIAL EULER POLARIZATION: PROVED_ALGEBRAIC
3221 LABELLED GROUPING: PROVED_FINITE
3221 COEFFICIENT MULTIPLICITY: PROVED_FINITE
STANDARD Q<NL DEFECT: PROVED_ALGEBRAIC
SOURCE-ASSISTED DIAGONAL: PROVED_FINITE
OFFDIAGONAL t PARAMETER: PROVED_FINITE
t RANGE: PROVED_FINITE
EH<Q CAPACITY: CAPACITY_ONLY
EH NO-WRAP: PROVED_FINITE
EH RATIO ENERGY: CONDITIONAL_FINITE
COMPLETED SOURCE DICTIONARY: SOURCE_OPEN
DI/KUZNETSOV LITERAL SPLICE: OPEN_ANALYTIC
FACTORIAL ENDPOINT: OPEN_ANALYTIC
COMPARISON: SOURCE_BLOCKED
BALANCED7: OPEN
FCL: OPEN
WINDOWPAIRSUPPLY: OPEN
ERDOS287: OPEN
```

**First formal blocker:** the endpoint bridge, now explicit as `Endpoint3221Decomposition`. **First source blocker:** the completed post-Poisson identity (then the physical comparison objects; the `θ=7/32` inequality was supplied without a formula and was not transcribed). **First analytic blocker:** `3221-DI-KUZNETSOV-LITERAL-SPLICE45`. **Next exact action:** produce a completed finite Fourier/Poisson identity for the `m`-box in terms of the objects already defined here.

# Summary of changes for run 09089103-b26b-402b-8253-fef2b27ed0e8
## V16 formal update — resumed in place, `ERDŐS #287 REMAINS OPEN`

**Workspace guard: PASS.** Every V15 object named in the task was located before any edit (`coeff_balanced_eq_perm_sum`, `coeff_balanced_scaled`, `balancedMonomial`, `balancedSevenMonomial`, `labelledPolynomial`, `SquarefreeEncoding`, and both V15 interfaces `PolarizedOmega7SignedEoD`, `MuLogComparisonLowCondMatch`). No compiling V15 file was restarted, rewritten, weakened or renamed; work is append-only apart from five import lines in `RequestProject/Main.lean`. No axiom was added.

### Files changed
Added `RequestProject/Erdos287/FactorialEulerPolarization.lean`, `FactorialEulerLocal.lean`, `FactorialPolarizationLinearity.lean`, `PascadiParameterLedger.lean`, `RequestProject/Status/Erdos287V16Status.lean`, `ERDOS287_FACTORIAL_V16_REPORT.md`. Edited `RequestProject/Main.lean` (imports only).

### 1. Retirement
"Complete multiplicativity is required for the polarized seven-box encoding" is retired **as controlling** in the V16 status docstring; nothing proved under it is withdrawn or deleted.

### 2. New factorial Euler polarization — `PROVED_ALGEBRAIC`
Over an arbitrary characteristic-zero field (ℂ instantiated separately), never a bare semiring: `factorialEulerPolarization_seven` gives, for Ω(m)=7 and `F_z(p^e)=a_z(p)^e/e!` extended multiplicatively with `a_z(p)=(1/7)Σ z_i ω_i(p)`,
`7^7·[z_1⋯z_7] F_z(m) = Σ_{p_1⋯p_7=m, ordered} ∏_i ω_i(p_i)`,
**including repeated primes**. Supporting theorems: `mem_ordFact_iff` (the index set really is the ordered prime tuples), `count_eq_factorization`, `exists_perm_comp`, `image_perm_eq_ordFact`, `fiber_card_eq` (the factorials cancel exactly the permutations of equal prime occurrences — proved, not assumed), `factorialEulerPolarization_of_listing`, `exists_prime_listing`, plus the general N-slot version `factorialEulerPolarization`, the ℂ form, and non-vacuity at the extreme repeated case `128 = 2^7`. The identity was cross-checked numerically on `m = 12`, `N = 3` (both sides `227`).

### 3. Local Euler algebra — formal only
`localSeries_eq_rescale_exp` (`Σ_e F_z(p^e)T^e = exp(aT)` as formal power series), `derivative_localSeries` (`d/dT S = a·S`), and — so the Λ-data is a theorem, not a convention — `localSeries_ne_zero`, `localLambdaSeries_unique`, `lambda_coeffs_of_logDeriv`: any family satisfying the log-derivative equation is forced to be `a` at `e=1` and `0` for `e≥2`; with the `log p` normalisation, `localLambda_one`, `localLambda_of_two_le`, `localLambdaSeries_eq_C`. **No class-C claim**: the repository contains no class-C definition, so only the finite/formal prime-power coefficient identity is banked. No analytic convergence anywhere.

### 4. Expected-term linearity — `PROVED_ALGEBRAIC`
`factorialPolarization_commutes_linearMap` (+ seven-slot, arithmetic-function and weighted-projection instances). Abstract and conditional; covers principal-character, low-conductor-character and exceptional-character linear operators as instances. `M_fac = M_phys` is **not** proved.

### 5. Pascadi parameter ledger — `PROVED_ALGEBRAIC / PARAMETER_LEDGER`
`pascadi_parameter_eta_le_one_div_4000`, `one_div_seven_gt_one_div_4000`, `pascadi_Q_three_fifths_y_one_seventh_incompatible`, plus the exact margin `−3993/280`. Exact ℚ arithmetic; Pascadi's analytic theorem is not formalised and is not claimed to fail.

### 6–8. Interfaces and compiler
`FactorialOmega7SignedEndpoint` (`AFFINE287-FACTORIAL-OMEGA7-SIGNED-ENDPOINT45`) is stated and **never inhabited**; `MuLogComparisonLowCondMatch` stays uninhabited and source-blocked; the only theorem about `BalancedSevenPacketInput` is the implication `balancedSeven_of_factorialEndpoint_and_comparison`, which keeps the two error channels separate (`E + err`) and inhabits nothing.

### Audit
`lake build` succeeds: 8123 jobs, **zero errors**, and the build log contains no `sorryAx`. A repository-wide scan of all Lean sources for `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `@[implemented_by]` finds **zero occurrences in Lean code** (all matches are documentation prose). `#print axioms` is emitted at build time for the 32 principal new theorems; across the whole repository all 446 printed reports list only `[propext, Classical.choice, Quot.sound]`.

### Status
`OMEGA7-FACTORIAL-EULER-POLARIZATION45: PROVED_ALGEBRAIC` · `POLARIZED-EXPECTED-TERM-LINEARITY45: PROVED_ALGEBRAIC` · `PASCADI-Q3/5-Y1/7-PARAMETER-NOGO: PROVED_ALGEBRAIC/PARAMETER_LEDGER` · `AFFINE287-FACTORIAL-OMEGA7-SIGNED-ENDPOINT45: OPEN_ANALYTIC` · `AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45: SOURCE_BLOCKED/OPEN` · `BALANCED7: CONDITIONAL/OPEN` · `ERDOS287: OPEN`.

No statement was found false and no target failed. Full ledger in `ERDOS287_FACTORIAL_V16_REPORT.md`.

# Summary of changes for run 3a93e89b-e3c6-43b5-bcda-2e46b020bde4
## V15 resumed in place — verdict `ERDOS287_V15_MULOG_POLARIZATION_SAFE_BANK`, `ERDOS287: OPEN`

**Workspace guard: PASS.** All named V14 objects were located before any edit (`vaughan_identity_exact`, `vaughan_affine_pointwise` in `RequestProject/Erdos287/AffineVaughanIdentity.lean`; `AffineVaughanPrimeCell`, `lambdaU_eq_neg_truncMobius` in `AffineVaughanPrimeOuter.lean`; `AffinePrimeModulusTwoOuterPacket` and the determinant-one line theorems in `AffineTwoOuterSource.lean`; the three compilers in `AffineTwoOuterCompiler.lean`). No V14 theorem was deleted, weakened, renamed or rewritten; work is append-only apart from seven import lines in `RequestProject/Main.lean`. No user axiom was added.

### Files added
`RequestProject/Erdos287/AffineMuLogIdentity.lean`, `AffineMuLogHardSource.lean`, `AffineMuLogLine.lean`, `AffineMuLogExponentLedger.lean`, `BalancedSevenFinite.lean`, `BalancedSevenPolarization.lean`, `RequestProject/Status/Erdos287V15Status.lean`, `ERDOS287_MULOG_V15_REPORT.md`. Edited: `RequestProject/Main.lean` (imports only).

### Proved (sorry-free, kernel-checked)
- **Λ = μ ∗ log** (`vonMangoldt_eq_mobius_mul_log`), derived in an arbitrary commutative ring from `μζ = 1`, `log = Λζ`, instantiated with Mathlib's genuine von Mangoldt/Möbius/log/zeta; a `rfl`-check confirms it is the same statement as Mathlib's own `moebius_mul_log_eq_vonMangoldt`. Coefficientwise `Λ(N) = ∑_{qr=N} μ(q) log r` and its divisor form.
- **Affine source** at `N = 2mn ± 1` (`muLog_affine_pointwise`), using the V14 natural-number sign firewall; the named source object is defined only after the equality is proved.
- **Three-way `q`/`r` partition**: exhaustive, pairwise disjoint, with exact recombination for an arbitrary weight in any additive commutative monoid, then specialised to μ·log and to the affine argument. The hard piece is defined, never claimed small.
- **Determinant-one line** `qr − 2mn = ±1`: `r ≠ 0` and `q ≠ 0` proved (not assumed), `gcd(r,2m)=1` and `gcd(q,2n)=1`, forward and reverse directions, the iff, and multiplicity-one uniqueness of the line parameter.
- **Exponent ledger only**: `δ₀ = 1/6 − σ > 0`, `σ + 2/3 + 1/6 = 1 − δ₀`, hence `< 1`, plus `1/6 − ν₀ = 131/300000`. No `O`-estimate is stated as a theorem.
- **Balanced-seven binomial certificate** `∑_{j≤3} (−1)^j C(7,j) = −20`, derived from the already-banked general alternating partial binomial identity; no physical source bridge is claimed.
- **Repeated-prime finite router**: seven labelled slots with one imposed coincidence take at most six values (and the general `Fin n` form), plus `6/7 < 1` as a rational inequality only.
- **Squarefree labelled polarization** (main new algebra): over an arbitrary commutative semiring, the coefficient of `z_1⋯z_n` in `∏_j (∑_i ω_i(p_j) z_i)` is `∑_{σ∈S_n} ∏_j ω_{σ(j)}(p_j)`, each permutation exactly once; specialised to `n = 7` and to ℂ, with `7! = 5040`. The normalisation is separate: scaling by `c` gives `c^n`, and the `1/7` case gives the factor `1/823543 = 7^{-7}`.
- **Squarefree multiplicative encoding**, finite interface only: an abstract multiplicative arithmetic function with prescribed prime values and vanishing at exponent ≥ 2, with `f(p₁⋯p₇) = ∏ a(pᵢ)` under distinctness; shown inhabited by Mathlib's Möbius function so nothing downstream is vacuous.

### Open / uninhabited
`PolarizedOmega7SignedEoD` (`AFFINE287-POLARIZED-OMEGA7-SIGNED-EOD45`, OPEN_ANALYTIC) and `MuLogComparisonLowCondMatch` (`AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45`, SOURCE_OPEN) are stated as specifications and never inhabited. No Bombieri–Vinogradov, DGS, Pascadi, Kuznetsov, large-value, Gate1A/1B, WindowPairSupply or FCL statement is assumed or proved. V14's Vaughan route is recorded as a valid but nonminimal alternative — never as false.

### Audit
`lake build` succeeds (8118 jobs, no errors). A repository-wide scan for `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `@[implemented_by]` finds zero occurrences in Lean code (all matches are documentation prose). `#print axioms` is emitted at build time for all 36 principal new theorems; each reports only a subset of `[propext, Classical.choice, Quot.sound]`. The twenty hostile tests are answered one by one in the docstring of the V15 status file; all pass with no downgrades. Everything is committed and pushed.

**Erdős #287 remains OPEN.** Formalising the polarization algebra does not close the balanced-seven case of anything.

# Summary of changes for run 0d849f24-cf9b-47cd-9af8-65f6801a897e
## Erdős #287 — V14: exact Vaughan source / prime-modulus two-outer structural spine

**Erdős #287 remains OPEN.** Nothing in this run proves it, nor `AFFINE287-PRIME-MODULUS-MU-TWOOUTER45`, smallness of the k = 0 smooth-parity packet, FCL, Gate 1A/1B closure, `WindowPairSupply` for all large M, or the Twin Prime Conjecture.

### Workspace guard
All eight named files (the four singleton V13 files and the four earlier fixed-certificate files) were verified present before any mathematics. `ERDOS287_ARISTOTLE_WORKSPACE_MISMATCH` does not apply; work resumed in place, append-only.

### Files added
`RequestProject/Erdos287/FordGeneratedDepth.lean`, `AffineVaughanIdentity.lean`, `AffineVaughanPrimeOuter.lean`, `AffineTwoOuterSource.lean`, `AffineTwoOuterCompiler.lean`, `RequestProject/Status/Erdos287VaughanV14Status.lean`, `ERDOS287_VAUGHAN_V14_REPORT.md`. (One file more than the suggested plan: the Part-2 finite arithmetic is kept separate from the Vaughan algebra.)

### Files edited
`RequestProject/Main.lean` — six import lines only. No historical statement was modified.

### What was proved (all sorry-free, kernel-checked)
- **Ford depth (PROVED_FINITE):** `general_ford_depth_le_112`, `fixed_certificate_depth_le_76` (+ factored form), `k0_depth_le_40`, with sharpness witnesses. The three input bounds (s ≤ 20, k ≤ 6, ell ≤ 12) are explicit hypotheses classified as published external input; Ford–Maynard Lemma 7.17 is not reproved.
- **Exact Vaughan identity (PROVED_ALGEBRAIC):** `vaughan_identity_abstract` in any commutative ring from `μ∗1 = ε` and `Λ∗1 = log`, instantiated as `vaughan_identity_exact` in the Dirichlet ring with Mathlib's genuine von Mangoldt/Möbius/log/zeta — no coefficientwise postulate, no axiom. Pointwise divisor-sum form `vaughan_pointwise` with `I1/I2/II`, and `vaughan_pointwise_of_lt` proving the `Λ_{≤V}` term vanishes *from* the size hypothesis.
- **Affine specialisation (PROVED_ALGEBRAIC):** `AffineSign`, `affineNat`, `affineNat_cast` (the ℕ-subtraction firewall for s = −1), `vaughan_affine_pointwise`.
- **Outer router (PROVED_FINITE):** prime vs proper-prime-power partition of the Λ-support, exhaustive and disjoint, plus the rational exponent ledger 1 − (1/3)/2 = 5/6. The analytic prime-power bound is the uninhabited `PrimePowerOuterBound`.
- **Prime-outer source cell:** `AffineVaughanPrimeCell` with only finite factorisation data; elementary consequences (divisibility, p odd, p ≥ 3).
- **Cofactor fold (PROVED_ALGEBRAIC):** `lambdaU_eq_neg_truncMobius` for q > 1, tying the new `d > U` cutoff to the banked `truncMobius` `d ≤ T` cutoff explicitly; `lambdaU_prime = −1`.
- **Support no-go (PROVED_FINITE):** `prime_support_obstruction_to_balanced_convolution` and `vaughan_cofactor_balanced_factorization_impossible`, scoped strictly to the stated balanced-support hypotheses.
- **Prime-modulus orientation (PROVED_ALGEBRAIC):** congruence, unique residue class in `ZMod p` under the explicit invertibility hypothesis, and the two coprimality consequences of the unit shift.
- **Two-outer quotient/packet:** `deltaMuOne` with exact unfolding, and `AffinePrimeModulusTwoOuterPacket` as a finite interface with no analytic field.
- **Determinant-one line (PROVED_ALGEBRAIC):** coprimality from the unit shift, both directions as an iff, and uniqueness of the parameter.
- **Exponent kernel:** strict bound 1/6 < 1 − exp(M) − exp(P), explicit-margin form, and the endpoint equality stated separately.
- **Conditional compiler (PROVED_COMPILER):** `singletonTypeII_of_vaughan_twoOuter`, `smoothParity_of_vaughan_twoOuter`, `parentLeakage_of_vaughan_twoOuter`, keeping the Type-I, prime-power, two-outer and comparison channels separate (error `E_I + C·X^{5/6} + E₂`, never merged).

### Open / blocked
Uninhabited interfaces: `PrimePowerOuterBound`, `AffinePrimeModulusMuTwoOuterInput`, `VaughanTypeIGeneratedKappaInput`, `Affine287ToTwoOuterF3Adapter`. Source-blocked: `Affine287TwoOuterComparisonMatch`, and (unchanged) `K0CellIdentitySource`, `SingletonPacketReduction`. No Gate/F3 provider is inhabited by nomenclature.

### Audit
`lake build` succeeds (8111 jobs, no errors). A repository-wide search of all Lean sources for `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `@[implemented_by]` finds **zero occurrences in Lean code** — every match is documentation prose. `#print axioms` is emitted at build time for all principal new theorems by the V14 status file; each reports only a subset of `[propext, Classical.choice, Quot.sound]`.

### Failed targets
None. No statement was found false; the one honest caveat is that the Part-2 depth model `2s + k·ell` is a definition chosen to reproduce the audited constants, and the `76` bound follows from the halved high-prime budget supplied as a hypothesis.

The sixteen hostile checks are answered individually in the docstring of the V14 status file, and the full ledger, source map and theorem list are in `ERDOS287_VAUGHAN_V14_REPORT.md`. Everything is committed and pushed.


# Summary of changes for run 3f26f1c6-6a1d-42e1-a3b1-69c782fc5917
## Workspace check

All six named files were verified present in the working tree before any mathematics was done, so `ERDOS287_ARISTOTLE_WORKSPACE_MISMATCH` does not apply: `RequestProject/Erdos287/FixedCertificateFordData.lean`, `FixedCertificateThreeError.lean`, `FixedCertificateSmoothParity.lean`, `FixedCertificateOrderCounterguard.lean`, `KummerDegeneracyRouters.lean`, and `RequestProject/Status/Erdos287GoldV12Status.lean`. Work resumed in place on the existing branch.

**Erdős #287 remains OPEN.** Nothing here proves it, nor Gate 1A/1B closure, H8/H9 smallness, the seven-prime Kummer bound, full fixed-certificate leakage, or the Twin Prime Conjecture.

## Source archaeology (A) — key finding

`nu0`, `truncMobius`, `FixedCertificateSmoothParityPacket` (with its `cell_identity` field), the parent leakage compiler, the three-error transference theorem and the balanced-cell counterguard are all present and were reused unchanged. But there is **no** `gStar`, **no** `eps`/`epsilonStar`, and **no Ford factorisation or canonical split** anywhere in the tree, and no coagulation/forbidden-region abstraction. The full object-by-object map is in `ERDOS287_SINGLETON_V13_REPORT.md`.

## B — verdict: `K0_CELL_IDENTITY_SOURCE_STILL_EXTERNAL`

Because the canonical split is not encoded, the `k = 0`, `J = ∅` specialization could only be assumed, not proved. No fake Ford factorisation was created; `cell_identity` is left uninhabited; the missing statement is named exactly as `K0CellIdentitySource` and carried as an explicit antecedent by every downstream theorem.

## What was proved (all sorry-free, kernel-checked)

- **D — rational ledger** (exact ℚ, no floating point): `sigma_pos`, `epsilon_lt_sigma`, `epsilon_lt_sigma_div_three`, `sigma_lt_one_sixth`, `two_sigma_div_three_lt_one`, `two_sigma_lt_one`, `six_sigma_lt_one`, `seven_mul_sigma_gt_one`, plus `nu0R_eq_cast_nu0` tying the ledger to the previously banked ν₀ = 16623/100000, and `admissibleEps_nonempty`.
- **C — `exists_subset_sum_in_typeII_window`**, the purely combinatorial smooth-vector lemma, by the two-case argument. The requested coagulation statement was *not* built: no such abstraction exists in the repository, and the missing object is recorded rather than invented.
- **E — `FordSmoothFragmentCertificate`**, classified `CONDITIONAL_INTERFACE / PUBLISHED_SOURCE`, never inhabited. Lemma 7.17 is not reproved. A clearly-labelled toy witness certifies the specification is *satisfiable*, so no downstream conclusion is vacuous.
- **F — `canonical_singleton_typeII`**, `canonical_singleton_card_eq_one`, `singleton_supersedes_depth_five`. Verdict `CANONICAL_SINGLETON_E45_KERNEL_PASS`.
- **G — `singleton_real_power_window`** and its shifted form: the real-power translation was completed, so the "pending" fallback was not needed.
- **H — `SingletonClass`** (tag only) and `singleton_complement_depth_le_39`, which also certifies the complement equals depth − 1.
- **I — `SingletonGeneratedTypeIIInput`**, uninhabited; Λ, B, W, ξ, κ are abstract parameters, not claimed to be the analytic objects.
- **J — `smoothParity_of_singletonTypeII`, `parentLeakage_of_singletonTypeII`, `primeMassPos_of_singletonTypeII`**: `PROVED_COMPILER / CONDITIONAL_ON_OPEN_ANALYTIC_INPUT`. The three error channels stay separate; `E2` is never merged into the sign region.

## Hostile checks — one downgrade

Check 3 failed as stated and was downgraded honestly. The interface does not force a singleton side to be terminal, so the requested `1 ≤ 2σ/3` route needs an extra hypothesis; it is kept as `fragment_singleton_terminal_contradiction`. The route actually used is the unconditional, strictly stronger `fragment_seven_le_card` (`s + r ≥ 7`, from `1 ≤ (s+r)σ` and `6σ < 1`). Check 6 passes only because the terminal-position convention is recorded explicitly as a field. All ten answers are in the status file's docstring.

## Audit

`lake build` succeeds (8105 jobs). Repository-wide scans find **zero** Lean-code occurrences of `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `@[implemented_by]` — every match is documentation prose. All 41 principal new theorems print `[propext, Classical.choice, Quot.sound]`, emitted at build time by the status file.

## Files

Added: `RequestProject/Erdos287/FixedCertificateSingletonParameters.lean`, `FixedCertificateSingletonFragment.lean`, `FixedCertificateSingletonCompiler.lean`, `RequestProject/Status/Erdos287SingletonV13Status.lean`, `ERDOS287_SINGLETON_V13_REPORT.md`. Edited: `RequestProject/Main.lean` (four import lines only). No historical theorem statement was touched. Everything is committed and pushed.

## Final ledger

`K0-SMOOTH-LEAKAGE-SOURCE45: SOURCE_BLOCKED` · `MU-SPLITTABLE45: PUBLISHED_EXTERNAL_INPUT` · `CANONICAL-SINGLETON-E45: PROVED_ALGEBRAIC` · `SINGLETON-COMPLEMENT-DEPTH39: PROVED_FINITE` · `287-SMOOTH-PARITY-FRAGMENT-TO-SINGLETON-TYPEII45: PROVED_COMPILER` · `287-SMOOTH-PARITY-SINGLETON-GENERATED-TYPEII45: OPEN_ANALYTIC` · `SMOOTH-PARITY: CONDITIONAL_INTERFACE / OPEN_ANALYTIC` · `FCL: OPEN_ANALYTIC` · `ERDOS287: OPEN_ANALYTIC`.

# Summary of changes for run 65719825-9f98-4322-874e-6644b235a32e
## Erdős 287 — V11 finalization + V12 gold reproof / Leanify run

Everything is committed and pushed; `lake build` completes successfully (8101 jobs) with no `sorry`, `admit`, `axiom`, `opaque`, `native_decide`, `unsafe` or `@[implemented_by]` anywhere in Lean code (all matches are documentation prose). Every new theorem prints `depends on axioms: [propext, Classical.choice, Quot.sound]`.

**Terminal status: ERDOS287 OPEN.** Nothing here proves #287.

### Files added this run (append-only; only `RequestProject/Main.lean` was edited, import lines only)
- `RequestProject/Erdos287/FixedCertificateFordData.lean` — Part G1: ν₀ = 16623/100000 as an exact rational, the four branch definitions (two-variable coefficient kept as a parameter, since only its support is given), window arithmetic (`twoVarWindow_nonempty`, `twoVarWindow_width`), the shrink and `shrink_le`, plus the never-inhabited `CertificatePinned` / `PositiveComparisonMargin` predicates.
- `RequestProject/Erdos287/FixedCertificateThreeError.lean` — Part G2: four-region partition with **three separate errors**, `sum_a_P_identity4`, `sum_a_P_lower4` (`≥ (1+C)B − ET − EL − E2 − EM`), `sum_a_P_pos4`, `sum_a_P_pos4_fraction` (constant saving suffices), `transference4_nonvacuous`. N2 is never merged into the sign region.
- `RequestProject/Erdos287/FixedCertificateSmoothParity.lean` — Parts G3/I: `truncMobius`, `truncMobius_prime`, `truncMobius_eq_zero_of_le`, the `FixedCertificateSmoothParityPacket` interface, `smoothParity_prime_normalization`, `smoothParity_missing_source`, and the parent leakage compiler `parent_leakage_of_children` / `parent_leakage_two_children` / `parent_prime_mass_pos`.
- `RequestProject/Erdos287/FixedCertificateOrderCounterguard.lean` — Part G4: `alternating_partial_binomial` (∑_{j≤r}(−1)^j C(k,j) = (−1)^r C(k−1,r)), the balanced-cell model and cut lemma, `balancedCellWeight_ne_zero`, the explicit values at k = 7…12 (−20, −35, 70, 126, −252, −462; the k = 9 value matches the banked 70), and `finite_H8H9_only_census_fails`.
- `RequestProject/Erdos287/KummerDegeneracyRouters.lean` — Part F: the four formalizable strata as predicates, `generic_disjoint_strata`, `generic_not_square`, `generic_not_pmExceptional`, `repeatedRoot_router_nonvacuous`.
- `RequestProject/Status/Erdos287GoldV12Status.lean` — Part J route firewall + `#print axioms` for all new theorems.
- `ERDOS287_GOLD_V12_REPORT.md` — the full A–M report (source map in the requested format, verdicts, file/axiom audit, final ledger). The earlier `ERDOS287_GOLD_V11_REPORT.md` was also committed.

### Firewall finding
Neither the V11 nor the V12 dossier is present in the repository (no `.tex`/`.pdf`, no `H8`/`H9`/Ford-(7.23)/principal-mode/conductor identifiers). All literal source-transcription obligations are therefore reported SOURCE BLOCKED and nothing was reconstructed.

### FINAL LEDGER
```
LCBETA PLACEMENT: REPAIRED
LOG-COFACTOR-ASYMPTOTIC287: KERNEL PASS
FIXED-CERTIFICATE287-PIN: SOURCE BLOCKED
FIXED-CERTIFICATE-TRANSFERENCE287: KERNEL PASS
FIXED-CERTIFICATE-SMOOTH-PARITY PACKET: SOURCE BLOCKED
FINITE-H8/H9-ONLY-CENSUS: FAIL (counterguard compiles)
HIGH-ORDER COUNTERGUARD: KERNEL PASS
QUADRATIC-KUMMER FINITE COMPILER: KERNEL PASS
ROOT-STABILIZER ALGEBRA: KERNEL PASS
WEIL / INTERVAL COMPLETION: EXTERNAL INTERFACE
SEVEN-PRIME EXPONENT LEDGER: KERNEL PASS
KUMMER DEGENERACY ROUTERS: PARTIAL
SEVENPRIME-KUMMER: CONDITIONAL CHILD PASS
H8H9-SOURCE-TO-KUMMER45: SOURCE BLOCKED
287-FIXED-CERTIFICATE-SMOOTH-PARITY45 ANALYTIC ESTIMATE: OPEN
FIXED-CERTIFICATE LEAKAGE COMPILER: KERNEL PASS
287-FIXED-CERTIFICATE-LEAKAGE45 ANALYTIC ESTIMATE: OPEN
GENERATED-(7.23) FIXED-gStar SPECIALIZATION: MAY STILL BE NEEDED
ERDOS287: OPEN
```

```
EXACT FIRST OPEN AFTER THIS RUN:
287-FIXED-CERTIFICATE-SMOOTH-PARITY45 — the two fields of
Erdos287.SmoothParity.FixedCertificateSmoothParityPacket (first the source
obligation `cell_identity`, then the analytic bound).

NEXT MATHEMATICAL ACTION:
Obtain the literal Ford factorisation of G_{g*}(m;n) and prove that its k = 0,
J = ∅ cell equals ∑_{d | n, d ≤ n^(1/2−ε)} μ(d) on the smooth sector, i.e.
inhabit the `cell_identity` field.
```

The Properties table has been updated with the new V11 and V12 deliverables and their statuses.

# Summary of changes for run fbe73b56-3c29-4b1a-926b-1a4159cafede
**Erdős #287 is NOT solved, and nothing in the project claims it is.** All work is committed and pushed; `lake build` passes (8086 jobs) with no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide` or `@[implemented_by]` anywhere, and every new theorem depends only on `propext`, `Classical.choice`, `Quot.sound`. No existing theorem was edited, renamed, weakened or deleted; the full written audit (sections A–AD, the Q1–Q30 matrix, counterguard check and final verdict block) is `ERDOS287_END_TO_END_CLOSURE_REPORT.md`.

**Files added**
- `RequestProject/Erdos287/ProblemStatement.lean` — the exact public predicate `Erdos287Counterexample` (card ≥ 2, all denominators > 1, reciprocal sum 1, all gaps ≤ 2), the **one-way** bridge `toGap2CE`, the junk inhabitant `gap2CE_one` (`A={1}`) showing the historical type is strictly broader, `three_le_max`/`four_le_max`, the ordered-sequence form of the public statement (with `k ≥ 2` derived, not assumed), and two non-vacuity guards.
- `RequestProject/Erdos287/FiniteMasterReduction.lean` — the requested patch: sign-sensitive `PlusSophieWitness` (`M/3 < q ≤ (M−1)/2`, `2q+1` prime) and `MinusSophieWitness` (`M/3 < q ≤ ⌊M/2⌋`, `2q−1` prime), both with `q ≥ 5`, their floor-form equivalences, the master theorem `Erdos287Counterexample → SophieWitness (max A) → False`, the retained `39 ≤ M ≤ 250` sweep, and the new free blocker `maxDivisorPrime_blocker` (hence: no counterexample has a prime maximum, none has `M = 2q`). The hypothesis `q² > M` proposed for that blocker is unnecessary — it follows from `M < 3q`, `q ≥ 4` — so it was dropped rather than carried.
- `RequestProject/Erdos287/FiniteRemainder.lean` — the interval-certificate engine: the certified table `CVal` with `C_le_CVal` (from the banked `C 1 … C 9`), and `Gap2CE.blocker_window`, which turns one certificate into exclusion of a whole interval `[L,U]` of maxima.
- `RequestProject/Erdos287/FiniteRangeExtension.lean` — a chain of 34 certificates: **no counterexample with `3 ≤ M ≤ 4·10⁹`** (previously `39 ≤ M ≤ 250`). All primality is discharged by `norm_num` (largest prime used 1 546 710 859); elaboration ≈ 25 s.
- `RequestProject/Erdos287/ClosureInputs.lean` — `WindowPairSupply M`, proved to be implied by a Sophie witness (so the frontier is *weaker* than Sophie–Germain), the non-circular `Erdos287ClosureInputs` (explicit threshold inside the verified range + the supply statement; no field is or implies the conclusion) and the deterministic compiler `Erdos287ClosureInputs → Erdos287Statement`, plus its ordered form.
- `RequestProject/Status/Erdos287EndToEndStatus.lean` — axiom prints for all new theorems and for the preserved V1/V2 bank; also the rational check `1/6 > 1663/10000`.
- Appended to `RequestProject/TrustedBank/R9/Certificate.lean`: `lowSum_eq` (`∑_{j=0}^{4}(−1)^j C(9,j) = 70`) and the cancellation of the two halves — labelled explicitly as binomial identities, **not** `H(n) = 70`.

**Answers to the key questions.** Public statement: represented exactly. `Gap2CE`: broader, not equivalent; only the needed direction is proved. Unconditional finite range: `3 ≤ M ≤ 4·10⁹`. R9 leakage, `H(n)=70`, fresh `c₉`, convolution/multiplicity, `f+δ`, Full-Nine bridge, SW2 shell, Gate-1A/1B, the 287 generated-packet census, generated-(7.23), `C_FM`, Gate-0 Type I, (b.2), N2, prime mass: **not banked / open** — the Ford–Maynard source definitions (Def. 4.3, (7.17), Prop. 7.22, (7.23), Thm 8.3) exist in this repository neither as Lean objects nor as text, so instantiating them would have meant inventing a schematic substitute; nothing was fabricated and no uninhabited interface is used by a proved theorem. `GATE1A_REQUIRED_FOR_287`: unknown (answerable only by the census). No `erdos287` theorem is declared, since the closure structure has no inhabitant.

**Verdict:** `ERDOS287_ALL_INTERNAL_COMPILERS_CLOSED_EXTERNAL_ANALYTIC_INPUTS_REMAIN`. **First exact remaining blocker:** `Erdos287ClosureInputs.supply`, i.e. `∀ M ≥ M₀, WindowPairSupply M` — for every large `M`, two consecutive integers in `[⌈M/2⌉, M]` each divisible by a prime power `> M/10`; an almost-prime-pair statement of Ford–Maynard type, weaker than the Sophie-Germain-type supply used before, and not proved here.

# Summary of changes for run 1453135a-faad-46d6-a201-4be69b18608e
Confirmed receipt of the Erdős-287 material in the project and worked only from it (no external sources were loaded). Both requested runs were carried out proof-first; **#287 is not claimed solved**, and no statement is made anywhere about the supply of Sophie-Germain-type primes for large M. The full written audit is in `ERDOS287_SOPHIE_V1_V2_REPORT.md`.

**Files added** (append-only; no existing theorem edited, weakened or deleted):
- `RequestProject/Erdos287/SophieOptimal.lean` — V1 route
- `RequestProject/Erdos287/SophieBandCompiler.lean` — V1 band
- `RequestProject/Erdos287/V2SophieFinite.lean` — V2 finite/top-layer route
- `RequestProject/Erdos287/V2SophieBand.lean` — V2 band compiler
- `RequestProject/Erdos287/V2BandSupplyChecks.lean` — maximal band + finite sweeps
- `RequestProject/Status/Erdos287V2Status.lean` — status ledger with axiom prints
- `RequestProject/Main.lean` — import lines only

**Source pins (printed before proving).** TL_PIN: `Erdos287.topLayer_congruence` (`Erdos287/TopLayer.lean`), general layer, `Finset ℕ`/`ZMod p` types, cofactors `ordCompl[p] a`, nonemptiness via `1 ≤ topExp A p`, with corollaries `topLayer_card_ne_one`, `topLayer_two_obstruction`, `topLayer_three_obstruction`. ISOLATED_HOLES_PIN: `Erdos287.Gap2CE.holes_isolated` on the closed window `[N,M]`, hole = `∉ A`. No pin failure.

**V1 (threshold route).** `Gap2CE.N_le_of_M_lt_two_mul` (the archive's `e` is literally `Real.exp 1`, so `2 < e` is legitimate — no mismatch); `excludedPP_of_window_two`; `Gap2CE.plus_sophie_blocker`, `Gap2CE.minus_sophie_blocker` (both strictly stronger than the banked `safePrime_blocker`); `band_hypotheses`, `band_exact`, `window_ge_two_of_two_mul_le`; conditional band compiler stated with the supply as an explicit hypothesis (never an axiom). C(2) pin: definition, `C_two` proved by kernel `decide`, `C_spec` greatest — **C2_PIN_PASS**.

**V2 (finite/top-layer only, superseded inputs avoided).** `Gap2CE.halfRange_min_le` (`N ≤ ⌊M/2⌋`), `topExp_le_one_of_lt_sq`, `topHalf_prime_hole`, `q_and_two_mul_q_holes`, `Gap2CE.v2_plus_sophie_blocker`, `Gap2CE.v2_minus_sophie_blocker`, `v2Band_hypotheses`, `Gap2CE.v2_band_plus_blocker` / `v2_band_minus_blocker` / `v2_finite_compiler`, `Gap2CE.v2_exact_compiler`, `no_Gap2CE_M_eq_104`, `sophieWitness_sweep` and `no_Gap2CE_of_M_in_39_250`. The V2 files import only `TopLayer.lean` and `Counterexample.lean`, so neither the `e(N−1)<M` placement nor the `C` threshold is a dependency; both stay in the bank untouched as redundant historical lemmas.

**Repairs found.** (1) `halfRange_min_le` is false without `2 ≤ M`: `A = {1}` satisfies every field of the counterexample structure and there `N = 1 > 0 = ⌊M/2⌋`; the hypothesis was added. (2) The fixed bands `(3/4,4/5)` and `(7/10,24/25)` have real supply gaps — kernel-checked witness `v2Band_supply_gap_152` at `M = 152` — so the finite sweep uses the maximal admissible band `M/3 < q ≤ (M−1)/2`; its small-`M` gap ends at 38 (`not_sophieWitness_35`).

**New unconditional finite consequence.** No gap-≤2 counterexample has `39 ≤ M ≤ 250` (`no_Gap2CE_of_M_in_39_250`), by kernel `decide` over the maximal band. A wider scan was exploratory only and is flagged as unverified in the report.

**Kernel audit.** BUILD: succeeds (8080 jobs). SORRY/ADMIT: none in the new files, none anywhere in `RequestProject`. No `axiom`, `unsafe`, `native_decide`, or `@[implemented_by]`; all finite certifications use ordinary kernel `decide`. AXIOMS: every new theorem reports only `propext, Classical.choice, Quot.sound` (two report less), printed by the status file.

**Verdicts.** V1: `ERDOS287_SOPHIE_FINITE_COMPILER_PASS_WITH_REPAIRS`. V2: `ERDOS287_V2_FINITE_COMPILER_PASS_WITH_REPAIRS`.

**Exact surviving interface** (Lean: `Erdos287.Gap2CE.v2_exact_compiler` / `Erdos287.no_Gap2CE_of_sophieWitness`): for a hypothetical gap-≤2 counterexample with maximum denominator M, the existence of a prime q with M/3 < q ≤ (M−1)/2 and 2q−1 or 2q+1 prime yields a contradiction. This condition is finite and decidable for each fixed M and is verified for 39 ≤ M ≤ 250; nothing is claimed about its validity for large M. All work is committed and pushed.

# Summary of changes for run ca26ff1f-8d7d-4b5e-956c-2175ae3c0a68
**TRUSTED_BANK_DELTA6_PARTIAL_SOURCE_FIELDS_MISSING**

Gate 1A, Gate 1B, ACBV45 / RLS45 / mixed-start NSE, the R9 analytic-mass question and Erdős #287 all remain **OPEN**; nothing in the project claims otherwise. Work was done inside the existing Lean project (toolchain and Mathlib pin unchanged). The full report, in the requested A–O format, is `TRUSTED_BANK_DELTA6.md`.

**A. Build status.** `lake build` succeeds (8074 jobs). Archaeology before editing: build succeeded, no sorries, no stale status labels, one long-standing duplicated *definition* (`lcmUpto` / `lcmUpTo`, identical bodies) left as-is and re-flagged.

**B. Files added:** `RequestProject/TrustedBank/Gate1A/{ScaleLedger,RowConservation,AvgJDRInterface}.lean`, `TrustedBank/Gate1B/{CenteredRho,MobiusCollapse,SeparableWeights,StartInjectivity}.lean`, `TrustedBank/R9/Certificate.lean`, `TrustedBank/Erdos287/GoodPrime.lean`, `Challenges/Delta6Interfaces.lean` (open statements only), `Status/Delta6Ledger.lean` (ledger + bibliographic records), `Validation/Delta6HostileTests.lean`, `TRUSTED_BANK_DELTA6.md`. Modified: `Audit/BankStatus.lean` (axiom prints). No existing theorem edited, renamed, weakened or deleted.

**C. New kernel-proved results.** Gate 1A: exact rational scale ledger with `(natural)/(target) = M/H` and the three gaps `1/18, 1/36, 1/24` at V1/V2/V3; M-row conservation `∑‖X‖² = (∑|w|²)(∑‖x‖²)` with invariance under permutation, unitary maps, direct-sum relabelling and unit-modulus diagonals (establishing only that reorganisation does not erase the row L² mass); AVG-JDR closure as a *conditional* theorem. Gate 1B: the centered identity `ρ(dp) = ρ_d ρ_p + ρ_d/p + ρ_p/d` for coprime d,p; `μ(q/p) = −μ(q)` for squarefree q; the clean collapse to `−μ(q)Λ♯(q)` for product-separable weights; SOURCE-MMD on a clean cell; `SeparableWeightDecomposition` with cost inheritance; same-start injectivity. R9: `∑_{j=5}^{9}(−1)^j C(9,j) = −70` and hence certificate value `70·g(∅)` under the supplied formula. Erdős #287: `GoodPrime`, Good Prime Exclusion, the adjacent good-factor blocker, and the finite (abstract-J) log-cofactor blocker.

**D. Repaired / false statements.** None of the new statements was false. Three deliberate counterexamples are banked and each forces a hypothesis: non-coprime ρ-pairs (d=p=2), the repeated-prime sector (q=4) for the Möbius collapse, and a mixed-start collision showing `T < u` does not give a cross-start diagonal (so mixed-start stays open).

**E. Axioms.** Every new theorem reports only `propext, Classical.choice, Quot.sound` (one reports only `propext`; the C(1..8) certification still reports none). A full scan finds no `sorry`, `sorryAx`, `admit`, `axiom`, `unsafe`, `native_decide` or `@[implemented_by]` anywhere.

**K. Source fields missing** (never invented, always hypotheses or empty specification records): the Gate-1A source identity `Ctilde = H·S + negligible`, the actual nonseparable source weight (`SourceMMDRequirements`, no inhabitant), and the exact Ford `H_g` formula.

**M/N/O — first remaining inputs.** Gate 1A: the authoritative source identity, then SOURCE-AVG-JDR itself. Gate 1B: a separable decomposition (with cost) of the actual smooth weight plus the remaining source fields. #287: the global `LCB_η` adjacent supply with an effective threshold and finite verification below it.

All work is committed and pushed.

# Summary of changes for run 961652a0-7e81-4f59-90e5-e00c79ffb600
**Headline: TRUSTED_BANK_EXTENDED.** Erdős #287, Gate 1A and Gate 1B remain **OPEN**; nothing in the project claims otherwise.

Work was done inside the existing Lean project (toolchain `leanprover/lean4:v4.28.0`, Mathlib rev `v4.28.0`, both unchanged). Full details are in the new `TRUSTED_BANK_AUDIT.md`.

**Archaeology (state before the run).** `lake build` succeeded. The existing Erdős-287 package (18 files under `RequestProject/Erdos287/`, ~130 theorems) was sorry-free except for **three sorries in `RequestProject/Erdos287/Uniform.lean`**. No stale/retracted theorems; one duplicated *definition* (`lcmUpto` in `Universal.lean` vs `lcmUpTo` in `RoughPrime.lean`, identical bodies, confusable names) — left as-is and flagged rather than silently merged.

**The project is now completely sorry-free.** The three remaining sorries were closed: `Erdos287.C_le_lcm_mul_harmonic` (C(j) ≤ lcm(1..j)·H_j), `Erdos287.harmonic_le_nat` (H_j ≤ j), `Erdos287.C_le_U` (C(j) ≤ j·j!). The uniform window-exclusion and forced-hole results that rested on them are now unconditional.

**Banked this run** (all under `RequestProject/TrustedBank/`, all kernel-checked, none importing anything open):
- Bank A `FixedAffine/Basic.lean` — a₁·L₂(n) = a₂·L₁(n) + Δ over any commutative ring, good-prime root transport, and the unit −a₂/Δ sending the two forbidden roots to {0,1}.
- Bank B `FixedAffine/UnitTransport.lean`, `Interfaces/FiniteSumTransport.lean` — unit-multiplication bijectivity, sum/ℓ²-energy invariance, and the exact Kloosterman-shaped reindexing S(A,B;q) = S(Aλ, Bλ⁻¹; q).
- Bank C `Interfaces/ZeroSetTransport.lean` — fixed-unit twists preserve simultaneous zero sets, their cardinalities and weighted sums.
- Banks D+E `Erdos287/BoundedCofactor.lean` — the Bézout parametrisation e·Q − d·P = 1 with the full coprimality package, and the local criterion **admissible ⟺ d·e even**, tested on small examples.
- Bank F `FixedAffine/SingularFactors.lean` — local root counts ν(ℓ) = 1 / 2 and the (ℓ−1)/(ℓ−2) correction (no infinite Euler product).
- Bank G `FixedAffine/CofactorIntensity.lean` — J(n) ≤ J(2) with equality iff n = 2, hence {d,e} = {1,2}.
- Bank H `FixedAffine/SymmetricPacket.lean` — odd-character ± cancellation, instantiated for Dirichlet characters.
- Erdős #287: `Erdos287/CarryTower.lean` (lcm² ∣ ∏a and lcm ∣ ∏ pairwise differences, for reciprocal-sum-1 sets) and `Erdos287/TopLayerConsequences.lean` (generalized fixed-cofactor blocker with every numerical hypothesis explicit).

**Repairs found (section B).** (1) The requested blocker threshold `C(2j−1)` is **not sufficient on its own** — with p = j·q ± 1 and M < 2p the window ⌊M/q⌋ can equal 2j; the repaired theorems use `C(2j)`, and a sharp-window variant keeps `C(2j−1)` under the added hypothesis ⌊M/q⌋ ≤ 2j−1. (2) "lcm² ∣ product" and "lcm ∣ pairwise-difference product" are **false for general finite sets** (A = {2,3}, counterexamples banked) and true under the reciprocal-sum hypothesis, which is the form banked. No statement was weakened.

**Open lines, isolated in `RequestProject/Challenges/`** (Prop-valued targets and interface structures, so no `sorry` and no `axiom`, and never imported by the bank): Gate 1A SB-ν (`SubpolynomialFibre`, plus a proof of its invariance under fixed-unit twists); Gate 1B with the exact one-completion source, β = μ_D·Λ_P linear, the 1/104 margin arithmetic, and the Gate conclusion derived from an explicit convolution-BV interface (NPCF-2C38 recorded dead, not revived); the affine source glue; and a Ford-type blocker-supply dependency specification (Ford–Maynard is *not* postulated as a Lean fact). Note: the authoritative Gate-1A/1B source definitions are not present in this repository, so those challenges are stated against abstract interfaces — this is recorded in the files.

**Audit artefacts.** `RequestProject/Audit/BankStatus.lean` prints axioms for 94 banked theorems — every one reports only `propext, Classical.choice, Quot.sound` (the C(1..8) certification depends on none). `RequestProject/Validation/BankStatements.lean` restates 26 banked results in unfolded form for an independent comparator.

**Final status:** `lake build` completes successfully (8062 jobs); a scan of all Lean sources finds no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `skipKernelTC` or `@[implemented_by]`; new-file linter warnings were fixed at the root. All work is committed and pushed.


# Summary of changes for run 840a104e-1f96-4573-b622-5c483c1e8808
Continued Erdős #287, proof-first and machine-checked. #287 is NOT claimed solved. No prime-distribution / analytic input was used. Both follow-up requests were completed; the whole project builds (`RequestProject.Main`) and every new theorem depends only on the allowed axioms `propext`, `Classical.choice`, `Quot.sound`, with no `sorry`/`axiom`/`unsafe`/`native_decide`.

## Files added
- `RequestProject/Erdos287/NonAdjacentHoles.lean` — the distance-`d` hole investigation.
- `RequestProject/Erdos287/KernelAPBlocker.lean` — the Kernel AP-blocker.
- `RequestProject/Erdos287/NONADJACENT_HOLES.md` — written analysis answering all targets.
- `RequestProject/Main.lean` — imports the two new files.

## Part A — do two holes at distance d > 1 force a contradiction?
Verdict: **No — no non-adjacent-hole contradiction survives.** The gap-≤2 constraint (`holes_isolated`, symbolically `LocallyAdmissible`) is a nearest-neighbour rule whose only forbidden pattern is two *adjacent* holes; that is exactly why the existing `blockerPair_contradiction` works only at distance 1.

Theorems (all in namespace `Erdos287`):
- `twoHoleWord`, `twoHoleWord_has_two_holes`, `twoHoleWord_locallyAdmissible` (d ≥ 2 admits two holes at distance d — refutes the distance-d claim), `twoHoleWord_one_not_admissible` (d = 1 is the unique local contradiction), `no_nonadjacent_local_contradiction`, `distance_band_admissible` (covers the whole band d ∈ {2,…,246}).
- Stronger variants, all shown compatible: `many_holes_block` + `altWord_block_locallyAdmissible` + `altWord_holes_nonadjacent` (a block of 123 forced non-adjacent holes inside an interval of length 246); `mod3HoleWord` + `mod3HoleWord_locallyAdmissible` + `mod3HoleWord_both_parities` (dense holes in both parity classes); `gcd_controlled_models` (coprime and non-coprime endpoints); `exists_residue_in_interval` and `exists_crt_at_distance` (the CRT mechanism can *produce* two hole-forcing multiples at any prescribed distance d ≥ 1, but for d ≥ 2 they are non-adjacent, so `blockerPair_contradiction` never fires).

Local models (counterexamples) provided: `twoHoleWord` (distance d), `altWord` (one parity / dense block), `mod3HoleWord` (both parities) — each proven `LocallyAdmissible`.

## Part B — the Kernel AP-blocker
Formalized and proved. For a `Gap2CE` with M ≥ 8152 and a prime p, with `qₚ = ceilMod p` and kernel modulus `Qₚ = kernelMod p` (= q₂ for p = 2, else 2·qₚ):
- `Gap2CE.HoleForcing.of_dvd`, `Gap2CE.ceilMod_dvd_kernelMod`, `Gap2CE.one_le_kernelMod`, `Gap2CE.kernelMod_holeForcing`.
- `Gap2CE.AP_prime_kills_holeForcing_add` (the +1 companion of the existing −1 lemma).
- `Gap2CE.kernel_AP_blocker` — no prime r ∈ [N+1, M−1] has r ≡ ±1 (mod Qₚ) (stated as Qₚ ∣ (r−1) ∨ Qₚ ∣ (r+1)); and `Gap2CE.kernel_AP_blocker_modEq`, the same in literal `Nat.ModEq` form. Proof: Qₚ ∣ (r∓1) ⟹ qₚ ∣ (r∓1) so r∓1 is a ceiling hole, r is a prime hole by `primeFree`, giving two adjacent holes, contradiction.

## Status
- Build: succeeds. Placeholders in the new files: none. Pre-existing `sorry`s in the unrelated `Erdos287/Uniform.lean` were left untouched (out of scope). Minor lint warnings in other pre-existing files are unchanged.
- A note on faithfulness: `exists_crt_at_distance` needed the extra hypothesis `1 ≤ d` (without it the statement is false in a degenerate N > M / d = 0 case); the intended use is d ≥ 2.

# Summary of changes for run 04a37366-3621-404e-9539-e5aed97ab049
Formalized the Ceiling–CRT Pairing package and the Large-Ceiling / rough-prime reduction for Erdős #287, proof-first and machine-checked. #287 is NOT claimed solved. No analytic number theory, no Sophie-Germain / BP★ / Chen-P₂ / Bateman–Horn were used.

Files changed:
- `RequestProject/Erdos287/CeilingCRT.lean` (new) — ceiling-modulus package and AP reduction.
- `RequestProject/Erdos287/RoughPrime.lean` (new) — rough-prime top-layer exclusion.
- `RequestProject/Main.lean` — added imports of the two new files.

Definitions added (in namespace `Erdos287`, most under `Gap2CE`): `ceilMod p := p^(topExp A p + 1)` (the ceiling modulus qₚ), `HoleForcing Q`, `isCeilModOfPrime`, `minCeil` (= minₚ qₚ), `APPrimeInInterval`; and `lcmUpTo j := (Finset.Icc 1 j).lcm id`.

Theorems proved (Ceiling–CRT):
- `ceilingMultiples_are_holes` — if p prime, x∈[N,M], qₚ∣x then x∉A (Target 1).
- `exists_crt_adjacent` — CRT interval-residue lemma: coprime Q₁,Q₂≥1 with Q₁Q₂≤M−N give x∈[N,M−1] with Q₁∣x, Q₂∣(x+1).
- `coprimeHoleModuli_CRT_pair` (Target 2/4) — coprime positive hole-forcing moduli with Q₁Q₂≤M−N give a contradiction; alias `coprime_holeForcing_contradiction`.
- `coprime_ceilMod`, `ceilingCRT_contradiction`, and `ceilingCRT_pairing` (Target 3) — for distinct primes p,r: qₚ·q_r > M−N; alias `ceilMod_mul_gt`.
- `atMostOne_small_ceiling` (Target 4, ℕ form: not both qₚ²,q_r² ≤ M−N), `at_most_one_ceilMod_le_sqrt` (√ form), `ceilMod_two_three_gt` (q₂q₃>M−N), `max_ceilMod_two_three_gt_sqrt`.
- `minCeil_isCeilMod`, `minCeil_holeForcing`, `AP_prime_kills_holeForcing`, `AP_prime_kills_ceiling`, `AP_prime_kills_minCeil` (Target 5), `LargeCeilingReduction` (Target 6), `no_Gap2CE_of_APPrime` (optional Target 6).

Theorems proved (rough prime):
- `lcmUpTo_pos`, `num_div_nat_le`, `num_le_j_mul_lcm`, `C_le_j_mul_lcm` (the crude bound C j ≤ j·lcm(1..j)), and `roughPrime_topLayer_empty` — for prime ℓ with ℓ²>M and j=⌊M/ℓ⌋≥1, if ℓ > j·lcm(1..j) then no element of A is divisible by ℓ (reduced to the certified `primePower_window_exclusion` at exponent 1 via the crude bound).

Build status: the project builds successfully (`RequestProject.Main`).

Placeholders: none in the two new files — no `sorry`, `axiom`, `unsafe`, or `native_decide` (the C 0 base case uses ordinary kernel `decide`). Representative theorems were checked to depend only on the allowed axioms `propext`, `Classical.choice`, `Quot.sound`.

No statement was found to be false, so no counterexample was needed. Notes: in `roughPrime_topLayer_empty` the hypothesis ℓ²>M is kept because the problem states it but is not needed by the proof (documented in the docstring); likewise `ceilingMultiples_are_holes` keeps x∈[N,M] as requested though divisibility alone forces the hole. Pre-existing `sorry`s in the unrelated `Erdos287/Uniform.lean` were left untouched (outside this task's scope).

# Summary of changes for run d1ddc5ae-e548-4cee-ae41-d8843d248054
Audited the Chen / P₂ relaxation of the blocker-pair contradiction in the Erdős #287 kernel. Work is proof-first and machine-checked; #287 is not claimed solved. All results build and use only the allowed axioms (`propext`, `Classical.choice`, `Quot.sound`), with no `sorry`/`axiom`/`unsafe`/`native_decide`.

Verdict: No — one side of a blocker pair cannot be relaxed from a prime power to a P₂ (semiprime / controlled almost-prime) while still forcing a hole via the top-layer / prime-power exclusion theorem. The natural relaxation is false.

Files changed/added:
- `RequestProject/Erdos287/ChenP2Audit.lean` (new) — the formal audit.
- `RequestProject/Erdos287/CHEN_P2_AUDIT.md` (new) — the written audit answering Tasks 1–4.
- `RequestProject/Main.lean` — now also imports `ChenP2Audit`.

Task 1 (exact relaxed statements): `IsP2`; `ExcludedP2Naive M q` (the most favourable literal analogue of `ExcludedPP`: `q = p₁·p₂`, product window `⌊M/q⌋`, threshold `C(⌊M/q⌋) < p₁`); the relaxed exclusion primitive `P2ForcesExclusion`; and the relaxed blocker-pair theorem `RelaxedBlockerPair` (one side P₂, other side prime power).

Task 2 (attempt): the exclusion proof (`primePower_window_exclusion`) is intrinsically single-prime — divisibility by pᵉ forces the top p-adic layer, whose numerator is ≤ C(⌊M/pᵉ⌋) yet ≡ 0 (mod p). A semiprime provides no single dominant modulus, so the top-layer congruence has nothing to run against; the relaxation is not provable.

Task 3 (false — concrete configuration): `not_P2ForcesExclusion` refutes the primitive. Witness: A = {2,3,6} with ∑ 1/a = 1 (`p2_witness_sum`), M = 6, semiprime q = 6 = 2·3. Its favourable product window ⌊6/6⌋ = 1 gives C 1 = 1 < 2, so the naive P₂ rule predicts a hole at 6 (`p2_six_excludedNaive`), yet 6 ∈ A, so no hole is forced. `p2_window_illegitimate` isolates the fallacy: the argument only ever legitimately offers an individual prime factor's window ⌊M/pᵢ⌋, and both fail here (C(⌊6/2⌋)=11≥2, C(⌊6/3⌋)=3≥3); the relaxation illegitimately shrinks ⌊M/pᵢ⌋ to ⌊M/q⌋. The only sound way a P₂ forces a hole is when a prime factor is itself an excluded prime power (`P2_excluded_via_prime_factor`), which reduces to the existing prime case and is not a genuine relaxation.

Task 4 (Chen tail): No usable infinite tail. A Chen-type theorem yields infinitely many (prime, P₂) neighbours, but converting them to blocker pairs needs the P₂ side to force its hole (`RelaxedBlockerPair`/`P2ForcesExclusion`), which is false (`chen_no_usable_tail`). The prime side gives one hole, the P₂ side none, so no adjacent double hole arises. Since the P₂ relaxation fails, the sound blocker inputs remain the genuine prime-power / large-prime-factor pairs already certified. (Per the instructions, Bateman–Horn and Sophie-Germain are not needed here; the existing `safePrime_blocker` already handles the genuine large-prime case.)

Build: succeeds (`RequestProject.Main`, 8040 jobs). Pre-existing lint warnings in other files are unchanged; the new file is warning-free.

# Summary of changes for run a1eae949-bf51-4fea-812e-515df0bc4c32
Completed the requested audit of the "Fable SFT / follower-graph" proposal for Erdős #287 (no claim that #287 is solved), backing every conclusion with machine-checked Lean.

Verdict: Fable's SFT schema matches the certified kernel only partially. The kernel splits into a genuinely local (radius‑1 SFT) *gap layer* and an essentially *non‑local* arithmetic layer that depends on the global parameters N, M, q = pᵉ, ⌊M/q⌋ and the top‑layer maximum. A fixed finite alphabet with a scale‑invariant local rule captures the gap layer but not the arithmetic layer, so the literal SFT schema is not valid for the whole kernel.

First mismatch: the exclusion rule is not scale‑invariant and the alphabet is not finite. The same prime power q = 2 is excluded at M = 3 but not at M = 4 (`excludedPP_three_two` vs `not_excludedPP_four_two`), and the residue modulus ranges over all primes (`modulus_alphabet_unbounded`).

New files:
- `RequestProject/Erdos287/SFTAudit.lean` — formalizes the audit. Local layer: `Cell`, `LocallyAdmissible`, `Gap2CE.word`, `word_eq_hole_iff`, `Gap2CE.word_locallyAdmissible` (the gap constraint IS a nearest‑neighbour SFT forbidding the block (hole,hole)). Dichotomy (A): `Gap2CE.holes`, `Gap2CE.holes_card_le_A`, `Gap2CE.two_mul_holes_le` (boundedly many holes). Dichotomy (B): `altWord`, `altWord_periodic`, `altWord_locallyAdmissible`, `altWord_has_hole` (the local subshift has periodic "fakes", so local rules alone cannot refute a counterexample). Non‑locality obstructions: `modulus_alphabet_unbounded`, `excludedPP_three_two`, `not_excludedPP_four_two`.
- `RequestProject/Erdos287/SFT_AUDIT.md` — the written audit answering Tasks 1–4, including the recommended sound replacement (the interval / blocker‑pair‑chain certificate graph already formalized in `Erdos287/Chain.lean`: `ChainLink`, `chainFrom`, `BlockerChain`, `BlockerChain.refutes`).
- `RequestProject/Main.lean` — now also imports `SFTAudit`.

Task 4 required output:
- Schema match: partial (local gap layer yes; arithmetic layer no).
- First mismatch: scale‑dependence of exclusion + unbounded prime modulus (theorems named above).
- Theorems formalized: all listed above.
- Build: succeeds (`RequestProject.Main`, 8039 jobs).
- Placeholders: none — no `sorry`, `axiom`, `unsafe`, or `native_decide`; all audited theorems reduce to only `propext`, `Classical.choice`, `Quot.sound` (verified).

Note: this turn built on the reusable certificate framework added earlier in the session (`Blocker.lean`, `Fiber.lean`, `Universal.lean`, `BadPrimes.lean`, `Chain.lean`), which is likewise complete and placeholder‑free; the audit's recommended replacement graph is the `Chain.lean` API.

# Summary of changes for run 35c8cb58-6495-4e1c-af75-56e158c4889f
Certified the elementary structural / prime-power-exclusion package for Erdős #287. The project builds cleanly and is free of `sorry`, `axiom`, `unsafe`, and `native_decide`; every result depends only on the allowed axioms (`propext`, `Classical.choice`, `Quot.sound`), and the certified `C` values depend on no axioms at all. #287 itself is NOT claimed solved — the open blocker-pair (BP) input was deliberately left untouched, as requested.

## Files changed
- `RequestProject/Main.lean` — now imports the whole package (previously just options).
- `RequestProject/Erdos287/Defs.lean` (new) — definitions.
- `RequestProject/Erdos287/Cnum.lean` (new) — the numerator bound `C`.
- `RequestProject/Erdos287/TopLayer.lean` (new) — targets 1–2.
- `RequestProject/Erdos287/Window.lean` (new) — target 4.
- `RequestProject/Erdos287/Counterexample.lean` (new) — target 5.
- `RequestProject/Erdos287/PrimeFree.lean` (new) — targets 6–7.

## Theorems proved (by task target)
Definitions: `topExp`, `topLayer` (with `mem_topLayer`, `topLayer_subset`); `addF`, `sumP`, `numOf`, `denOf`, `C` (a kernel-reducing list computation).

1. `topLayer_congruence` — ∑ over the top p-adic layer of the mod-p inverse cofactors is 0 in `ZMod p`.
2. `topLayer_card_ne_one`; `topLayer_two_obstruction` (p ∣ m₁+m₂); `topLayer_three_obstruction` (p ∣ m₁m₂+m₁m₃+m₂m₃).
3. Bridge `sumP_spec`, `numOf_eq_num` (links the computation to `Rat.num`); explicit values `C_one…C_eight` and bundled `C_values` proving `C(1..8) = (1,3,11,25,137,137,1019,2143)` by kernel `decide`; `C_seven_witness` verifying `C 7 = 1019` is attained by `{1,2,3,4,5,7}` (via `norm_num`); plus faithfulness `num_le_C`, `C_attained`, `C_spec` (`IsGreatest`), and `C_mono`.
4. Helper `dvd_num_of_sum_inv_zero`; `primePower_window_exclusion`.
5. `Gap2CE` structure with `N`, `M`, `N_mem`, `M_mem`, `mem_Icc`, `holes_isolated`, `exp_lower` (e·(N−1) < M), `exp_upper` (M ≤ e²·(N+1)), and `N_gt_M_div_eight` (M ≥ 97 ⇒ M < 8·N, i.e. N > M/8).
6. `Gap2CE.primeFree` — for M ≥ 8152, no denominator is prime (via `primePower_window_exclusion` with e=1, `C_mono`, `C_seven`, and N > M/8, using (7+1)·C(7) = 8152).
7. `Gap2CE.blockerPair_contradiction` — two consecutive holes in [N,M] are impossible.

## Build / soundness status
- Build: succeeds (only lint warnings remain — see below).
- No `sorry`/`axiom`/`unsafe`/`native_decide`/`admit`. The C-value certifications use ordinary kernel `decide` on a bespoke reducing computation (`Rat` arithmetic does not reduce in the kernel, so a list-based reduced-fraction fold, proven equal to `Rat.num`, is used instead).
- No statement was found to be false, so no counterexample was needed.

## Notes
- `primePower_window_exclusion` keeps the hypothesis `hqM : p^e ≤ M` because the problem states it, but the proof does not need it (documented in its docstring); this yields one `unused variable` lint warning.
- A handful of `unused simp argument` lint warnings remain inside machine-generated proofs; they are informational only and do not affect correctness. Everything else is complete.