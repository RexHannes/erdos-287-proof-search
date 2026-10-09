# W2.984 — formalization report

**Erdős #287 remains open. W2.984 is conditional, asymptotic and ineffective.**

## Files

New, append-only subtree (namespace `Erdos287.W2984Publication`):

| file | content |
|---|---|
| `RequestProject/Erdos287/W2984Publication.lean` | aggregator |
| `W2984Publication/ScalarFunctions.lean` | \(e^\gamma\), \(F_{\rm lin}\), \(f_{\rm lin}\), Buchstab \(\omega\); DDE faithfulness; \(\omega\le3/5\) on \([5/3,4]\) |
| `W2984Publication/ScalarOmega.lean` | \(\Omega_1,\Omega_2,\Omega_3\) from Merikoski's definitions; the identity for \(\Omega_1-\Omega_2\); \(\Omega_3\le14\log\frac32-\frac{28}5\); rational log bounds |
| `W2984Publication/ScalarCertificate.lean` | \(\Omega_1-\Omega_2+\Omega_3\le796682507263/(2\cdot10^{11})<3.984\); \(\delta\)-budget arithmetic |
| `W2984Publication/ChenDecomposition.lean` | counterexample to Merikoski's literal pointwise inequality; corrected pointwise and weighted (affine) Chen decomposition |
| `W2984Publication/AffineCRT.lean` | transfer identity, unit residues, complete modulus \(a_jW\), \(\phi(a_jW)=a_j\phi(W)\), distinct roots, local densities, switched identity, non-squarefree base |
| `W2984Publication/ModulusLedger.lean` | five-source ledger for \(S_1/S_2\), \(S_3\) ledger, fixed-base reindexing |
| `W2984Publication/Providers.lean` | `W3FrameworkProvider`, `AffineChenS1/S2/S3Provider`, `AffineChenSquareTailProvider`, derived `PairBoundProvider` |
| `W2984Publication/MainTheorem.lean` | pair expectation = Chen \(S\); providers ⇒ pair bound ⇒ width; **`W2984`**, `W2984_counterexample_form`, `W3_of_selbergPairBound` |
| `W2984Publication/RegressionSuite.lean` | regression controls 1–13 |
| `W2984Publication/AxiomAudit.lean` | build-time axiom, provider and firewall audit |
| `W2984Publication/audit.sh` | source/firewall/build/negative-control script |
| `RequestProject/Erdos287/W3Publication.lean`, `W3Publication/Checkpoint.lean` | W3 checkpoint (aliases into `PostV87V90R`; no new mathematics) |

Documents: `AFFINE_CHEN_TRANSFER_W2984.md`, `W2984_THEOREM.md`, `MERIKOSKI_DICTIONARY.md`,
`OPUS_REAUDIT_PACKET.md`, `W3_PUBLICATION_CHECKPOINT.md`, this file.

## Theorem classification

### Exact / kernel-proved (no hypotheses beyond their statement; axioms `propext`, `Classical.choice`, `Quot.sound` only)

*Scalar:* `Flin_initial`, `flin_dde`, `Flin_dde`, `buchstab_initial`, `buchstab_dde_mid`,
`buchstab_dde_tail`, `buchstab_le`, `buchstab_nonneg`, `Omega1_seventh`, `Omega2_seventh`,
`Omega1_sub_Omega2`, `omega3_arg_mem`, `Omega3_le`, `J_lower`, `log_three_halves_le`,
`log_five_fourths_le`, `pairConstant_le_certificate`, `chenCertificate_lt`, `pairConstant_lt`,
`pairConstant_lt_merikoski`, `certificate_room`, `flin_le_lipschitz`, `explicit_Cerr_lt`,
`explicit_delta0`.

*Chen combinatorics:* `card_triples_ge`, `chen_pointwise`, `chen_weighted`,
`affine_chen_weighted`, `fixture_1925`, **`merikoski_pointwise_fails`**, **`merikoski_weighted_fails`**.

*Affine arithmetic / CRT:* `transfer_identity`, `dvd_form_iff`, `coprime_of_dvd_form`,
`progression_iff`, `progression_surj`, `base_residue_unit`, `totient_mul_of_primeFactors_subset`,
`totient_normalisation_needs_radical`, `prime_dvd_two_forms`, `prime_not_dvd_slope`,
`coprime_of_dvd_forms`, `roots_distinct`, `card_root_one`, `local_density_designated`,
`overlap_empty`, `switched_identity`, `switched_progression`, `switched_modulus_not_squarefree`.

*Ledger:* `ledger_card`, `totalS1_eq`, `v92_core_lt_half`, `totalS1_le`, `totalS1_lt_half`,
`totalS1_ne_without_square`, `totalS3_eq`, `totalS3_le`, `S2_level`, `reindex_fixed_base`.

*Downstream (finite/moment):* `pairExpect_eq_chenS`, `Qcount_eq`, `E_Qcount_eq`, `E_Qcount_le`,
`exists_ratio`, `chenCertificate_bounds`.

*Regression:* `reg1_spectator_density` … `reg13_sign`, `reg12_tag`.

### Conditional on explicit providers (kernel-proved implications)

* `pairExpect_le_chen`, `pairBound_of_chen` — four Chen providers ⇒ pair bound with constant
  \(c_{\rm cert}\).
* `width_of_pairBound` — framework + pair bound with constant \(c_0\in[2,8)\) ⇒ `W3Statement s`
  for all \(s>c_0-1\).
* **`W2984`**, **`W2984_counterexample_form`** — framework + S1 + S2 + S3 + square tail ⇒ W2.984.
* `W3_of_selbergPairBound` — framework + Selberg pair bound (\(c_0=4\)) ⇒ W3.

### Imported analytic (written proof, not formalized)

| provider | written proof | cited ingredients |
|---|---|---|
| `W3FrameworkProvider` | W3 (refereed `PASS`) | BFM Lemmas 4.6(i),(ii), 4.7, Thm 4.2 |
| `AffineChenS1Provider` | §7 | linear sieve; Lemma 6.1; Lemmas 4.1–4.4 |
| `AffineChenS2Provider` | §8 | linear sieve (lower); Lemma 6.1; Lemmas 4.1–4.4 |
| `AffineChenS3Provider` | §9 | BFM Lemma 4.6(iii) Selberg computation; FI Lemma 12.1; Lemma 6.1 (\(\Lambda_0\)) |
| `AffineChenSquareTailProvider` | §10 | divisor bound only |

### Ineffective

`W2984`, `W2984_counterexample_form` (tag `W2984_effectivity = ineffectiveExistential`). This is
inherited from Lemma 6.1, step 5 (the exceptional modulus / Siegel), and from W3.

### Open / obligations

1. **Constant extraction (paper-level).** The identification \(C_1=392/9\), \(C_2=196\log\frac32\),
   \(C_3=5/2\) (§13) is argued in the paper, not formalized. Lean uses only the existence of
   \(\delta\)-independent constants, which is what the asymptotic theorem needs.
2. **The four Chen providers and the framework provider** are not constructed. They encode
   analytic theorems that do not exist in Mathlib (linear sieve, Bombieri–Vinogradov with
   exceptional moduli, Maynard–Tao asymptotics).

## Semantic firewall audit (enforced at build time in `AxiomAudit.lean`)

| provider | inputs | quantifiers | modulus range | coefficients | sign | uniformity | normalisation |
|---|---|---|---|---|---|---|---|
| `AffineChenS1Provider` | framework data for one index \(I\) | \(\forall I,\ \forall\varepsilon>0\ \exists N_0\ \forall\) windows \(M\ge N_0\), \(\forall b,\ i\ne i'\) | implicit (paper: \(\le X^{1/2-\delta}\)) | actual W3 weight \(\nu\) | upper | \(C_1\) independent of \(I\), \(X\), \(\delta\) | units of the framework's `pairNorm` \(\mathfrak M\) |
| `AffineChenS2Provider` | same | same | same | same | **lower** | \(C_2\) same | same |
| `AffineChenS3Provider` | same | same | \(\le X^{1/2-\delta}\) | same | upper | \(C_3\) same | same |
| `AffineChenSquareTailProvider` | same | same | — | same | upper | — | same |

* `#assert_avoids` checks that no provider's statement mentions `W3Statement`,
  `WindowMomentData`, `occupied`, or `ContactWitness`. So no provider contains W2.984 or an
  occupancy/contact conclusion.
* `#assert_mentions` checks that `W2984` takes all four Chen providers and the framework.
* `#audit_providers_w2984` checks that no declaration in the namespace produces a provider
  without taking a provider as hypothesis, and none takes `False` / `IsEmpty _`.
* The \(S_1,S_2,S_3\) sums in the providers are the literal affine Chen sums of `chenS1`,
  `chenS2`, `chenS3` on the forms `C.slope b i * t + 1`, with the framework's sifting primes and
  \(Y=\lfloor X^{1/7}\rfloor\), \(Z=\lfloor X^{3/14}\rfloor\).

## Trust audit

* `lake build RequestProject.Erdos287.W2984Publication` succeeds. `lake build` (all default
  targets) succeeds (9003 jobs).
* `lake env leanchecker RequestProject.Erdos287.W2984Publication` and
  `lake env leanchecker --fresh RequestProject.Erdos287.W2984Publication` both succeed. (The
  installed checker binary is named `leanchecker`.)
* `#print axioms` / `#assert_std_axioms_v90` on every principal theorem: only `propext`,
  `Classical.choice`, `Quot.sound`. No `sorryAx`, no `Lean.ofReduceBool`.
* `audit.sh`: no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `bv_decide`,
  `implemented_by`, `opaque`, `extern`, `Inhabited`, `False.elim` in code. No provider
  constructions. No SR-287/HLS/Zheng/Lichtman/R11/PNP imports. Historical subtrees unchanged.
  Five negative controls are rejected.
* Note: the older script `PostV87V90R/audit.sh`, step 4, flags *any* file changed outside its own
  subtree. It therefore reports the new `W3Publication`/`W2984Publication` subtrees. This is by
  design of that older script, not a regression.

## Regression controls (task §20)

| # | control |
|---|---|
| 1 | `reg1_spectator_density` (conditional density \(0\ne1/4\)) |
| 2 | `reg2_uncorrected_remainder`, `reg2_overlap_prime_large` |
| 3 | `reg3_ledger`, `totalS1_ne_without_square` |
| 4 | `reg4_exponent` |
| 5 | `reg5_nonsquarefree` |
| 6 | `reg6_max_placement` |
| 7 | `reg7_support_lengths` |
| 8 | `reg8_delta_budget` |
| 9 | `reg9_endpoint_excluded`; `audit.sh` negative control 4 |
| 10 | `audit.sh` step 3 |
| 11 | `reg11_narrow_windows_exist` |
| 12 | `W2984_effectivity`, `reg12_tag` |
| extra | `reg13_sign` (unsigned \(S_2\)); `merikoski_pointwise_fails` (literal Lemma 13) |
