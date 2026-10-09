# Erdős #287 — actual atom → positive `W₄`: formal report (with upstream repairs)

**Erdős #287 is still open. TAIL-287 is NOT BANKED.**

Status record (metadata only; none of these labels appears in any Lean hypothesis or proof):
`AstraActualAtomW4Candidate` / `AstraActualAtomW4 = PaperCandidate`,
`V101ResidueAtomW4Candidate` / `V101ActualAtomW4 = PaperCandidate`,
`IndependentAudit = Pending`, `Tail287 = KernelConditional`. The Astra manuscript's
"conditional research preprint" label and any Opus PASS label are metadata too.

New Lean files (append-only; `CurrentTail/` and all protected subtrees unchanged):
`RequestProject/Erdos287/SourceChain/{ActualAtom, W4Route, CrossCoprime,
ActualAtomW4Comparison, UpstreamRepairs}.lean`, plus extensions to `SourceChain/AxiomAudit.lean`
and to the aggregator `SourceChain.lean`.

## Final verdicts

* Actual-atom request: **`ERDOS287 ACTUAL-ATOM INTERFACE BLOCKED`**. The source-level step
  that cannot be reduced further with the material in the repository is the instantiation of
  the canonical `CleanAtom` from the literal packet `F^♯_ξ`. This identity is
  `F^♯_ξ = (M/f_ξ) 𝒦_{A,f_ξ,c_ξ}` together with the actual-object version of
  `#Ω ≪ N²R²S/f`. There is no physical source object in Lean to state it about (see the next
  item). All the algebra downstream of the atom is kernel-proved.
* Provider-discharge request: **`SUBSTANTIVE PROVIDER REMAINS`**. Blocker class:
  **1. physical-source construction**, followed by 3 (seven-block framework) and 4 (deep
  analytic theorems).
  * First obstruction: `TailSourceFamily` and `OrderingBCells` are abstract structures, and the
    repository contains no V99/V100/PHLS definition of the packet set, `Γ_ξ`, linear-sieve
    coefficients, coloured prime coefficients or the smooth profile `Ψ`. So
    `physicalTailSource`, `physicalOrderingBCells` and `physicalFamilyScale` cannot be defined
    faithfully, and `OrderingBPoissonReduction` cannot be proved about real objects. Writing
    surrogate definitions would be a fake construction, so none was written.
  * Second, a project-specific combinatorial provider: `UpperSieveWellFactorable`
    (well-factorability of `𝒟⁺(D)`). This is the exact input needed to derive the three
    critical range inequalities from support membership. It is purely combinatorial, but it is
    **not yet proved**.

No provider-free `Erdos287.SourceChain.Tail287` exists. None was faked.

## 1. Exact algebra now kernel-proved

| Item | Lean |
|---|---|
| Canonical clean atom (shared by both routes; exact CRT system `n₁ρ≡c (f)`, `An₁ρ≡B (qr₁s₁)`, `An₂ρ≡B (r₂s₂)`; explicit inverse witnesses; cross-coprimality; near-diagonal exclusion; ranges) | `CleanAtom` |
| No-dilation general-affine phase, `u=r₁s₁`, `v=r₂s₂`, no `(A,f)=1` | `CleanAtom.noDilation_phase` (via `ph1_phase`) |
| Fixed-local counterfixture: deleting the `Af` colour changes the phase (a genuine instance) | `colour_deletion_counterfixture`, `colour_deletion_counterfixture_hyps` |
| Unit-class expansion mod `D=Af` (Mathlib finite-group orthogonality; no cyclicity assumed), multiplicative split `χ(qr₁C_*)χ(s₁)` | `unit_class_expansion`, `unit_class_expansion_factor` |
| One-bounded twists; mass `≤ φ(D) ≤ D` | `character_coefficient_bound`, `character_count_le`, `character_mass_le` |
| `T_H(ω_t) ≤ Af` (denominator of `(Ac−B)t̄/(Af)`) | `fixedPhase_den_le` |
| First Cauchy + representation multiplicity → positive square | `source_to_W4`, `source_to_W4'` |
| Positive `W₄` (definition only; no bound encoded), non-negativity | `W4`, `W4_nonneg` |
| Fixed-`A` positive domination, explicit injectivity/positivity | `fixedA_domination`, `mulLeft_injOn` |
| Cauchy prefactor `N²/(fQ²R²S³)` | `cauchy_prefactor`, `cauchy_prefactor_bound` |
| Regressions: drop `1/f`, `Q`→`Q²`, `q` treated as independent | `regr_drop_inv_f`, `regr_Q_not_Q2`, `regr_q_independent` |
| Audited Pascadi term `FC²+B₀CS²+FCHS`; old `FHS` rejected | `pascadiInner`, `regr_old_FHS`, `pascadiInner_ge_old`; the build-time check confirms that `specRHS`/`W4SpecEstimate` avoid `pascadiInnerOld` |
| `T^{7/64}` → `T^{7/128}` via the square root; `T_H ≤ Af` | `TH_sqrt_propagation`, `TH_le_Af_power` (with the existing `th_exponent_propagation`) |
| Packet exponent (generic) and both routes | `packet_exponent`, `astra_packet_391`, `v101_packet_775` |
| Astra strong ⟹ weak target (`ρ₀ ≤ 2ε`) | `astra_strong_to_weak` |
| Ledgers `199/128 = 3/2+7/128`, `263/128 = 2+7/128`, `647/128 = 4+1+7/128` | `astra_kernel_ledger`, `v101_kernel_ledger`, `astra_beats_v101` |
| Cross-coprime colouring partition: coprimality inside each class, exact class count, exact indicator identity, subpower weight `≤ 4^K` | `colourClass_coprime`, `colourings_card`, `coprime_indicator_identity`, `colour_weight_le` |
| Partition placement: allowed after a power saving; **regression**: a subpower count times a `(log x)^{-A}` saving is unbounded | `partition_after_power_saving`, `partition_on_log_saving_fails` |
| Degenerate/short-`H` cells; nothing routes to the retired "factor = 1 ⟹ modulus < 1/2" shortcut | `DegenerateCell`, `degenerateRouting`, `no_retired_shortcut` |
| Atom estimate + reciprocal packet norm ⟹ clean-AA aggregate ⟹ tail | `sharpPowerSaving_of_atom`, `sharpPaid_of_atom`, `Tail287_of_AtomProviders` |
| Upper-sieve support `𝒟⁺(D)` (odd-prefix conditions) ⟹ `d < D` | `UpperSieveSupport`, `upperSieveSupport_prod_lt` |
| V97 routing: at most two variables `> 1/3`; complements `U`; window lemma for small variables; two-large exponent summation | `large_count_le_two`, `complement_one_large`, `complement_two_large`, `prefix_hits_window`, `twoLarge_cell_saving` |
| Pair coefficient `2log x/log D = (200/59)(1+ε₀+τ)`; `200/59` alone is not complete; safety `(200/59)(1+10⁻³)+1/295 = 17/5−1/295 < 17/5` | `pair_coefficient`, `pair_coefficient_exceeds`, `pair_coefficient_safety` |
| Parity-sensitive routing (even → upper, odd → lower then negative sign), low/high split, three-colour, `γ(𝐃)=1` | existing `parity_sign_routing`, `lowHigh_unique`, `scalarWeight_eq_sectors`, `canonical_gamma_one` |

## 2. Astra-route analytic providers (narrow; each separate)

* `W4DiagEstimate`: `W_diag ≤ Λ·SHFCB₀`.
* `W4RamEstimate`: `W_Ram ≤ Λ·S²H²FB₀`.
* `W4SpecEstimate`:
  `W_spec ≤ Λ T^{7/64}(1 + C√F/(S^{3/2}H))^{7/32} · HS²√F · (FC²+B₀CS²+FCHS)^{1/2}`.
* The structural split `𝒲₄ ≤ W_diag + W_Ram + W_spec` is an explicit hypothesis of
  `W4_bound_of_pieces`. It comes from Poisson/Kuznetsov, which is analytic.
* At the atom level these combine into `AstraAtomBound`, the input of
  `Tail287_of_AtomProviders`.

## 3. V101-route analytic providers

The same three-piece shape, applied to `W_{A₀}` after residue atomisation. Its ledger is kept
separate (`v101_kernel_ledger`, `v101_packet_775`), and V101 is never used to prove the Astra
exponent.

## 4. Comparison (`ActualAtomW4Comparison.lean`, kernel-checked)

| Route | Source split | Kernel exponent | Final exponent | Status |
|---|---|---:|---:|---|
| Astra | product-residue character separation after Ordering B | 263/128 (199/128 claimed stronger) | 391/256 | PaperCandidate |
| V101 | four-coordinate residue atomisation | 647/128 | 775/256 | PaperCandidate |

`route_final_of_kernel` checks final = (kernel+1)/2, and `routes_not_banked` checks that
neither route is banked.

## 5. Provider count before / after

* Before (`Tail287_of_NarrowProviders`), critical piece: `PascadiSpectralY`, `SharpMembership`,
  `PascadiRangeExport` constants, partition count.
* After (`Tail287_of_AtomProviders`), critical piece: `AstraAtomBound`, which reduces by
  kernel-proved algebra to the three `W₄` estimates plus the split. Separately exposed:
  `UpperSieveWellFactorable` (combinatorial, not yet proved) and `TwoLargeEstimate` (analytic,
  exact form). The cross-coprime partition is now a kernel-proved identity
  (`coprime_indicator_identity`), not a provider.
* Unchanged: `SevenBlockTailFramework`, `BaseSWProvider` (below-half base-only BV + large-smooth;
  V99 item 1 algebra is already kernel-proved in `CurrentTail`), `CoprimalityPaid`,
  `OrderingBPoissonReduction`, `CenteringPaid`, `SpectatorReciprocalNorm`, the 7 non-critical
  `PiecePaid` cells.

## 6. Source mismatches

None found. The Astra phase identity coincides exactly with the already-proved PH.1
(`ph1_phase`), with `l = q`. The corrected spectral term `FCHS` is used everywhere, and the
obsolete `FHS` term has no consumer.

The pair-coefficient repair is recorded rather than flagged as a mismatch: the complete
coefficient is `(200/59)(1+ε₀+τ)`, and `200/59` alone is strictly smaller
(`pair_coefficient_exceeds`).

## 7. Current strongest conditional tail theorems

```
Tail287_of_MinimalAnalyticProviders :
  ∀ {ι} (S : TailSourceFamily ι) (C : OrderingBCells S),
    SevenBlockTailFramework S → BaseSWProvider S → CoprimalityPaid S →
    OrderingBPoissonReduction S C → CenteringPaid S C →
    (∀ p : CellPiece, PiecePaid S C p) → Tail287Statement
```

`Tail287_of_NarrowProviders` and `Tail287_of_AtomProviders` refine the critical `PiecePaid .sharp`
input, the first through `PascadiSpectralY` + `SharpMembership`, the second through
`AstraAtomBound` + `SpectatorReciprocalNorm` + `391σ/256 < ε/2`. `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for all three. A clean axiom list does **not** make
them unconditional: they still take the hypotheses listed above.

## 8. Trust

* `lake build RequestProject.Erdos287.SourceChain`: success. The build-time check
  `#sc_assert_all_std_axioms` passes for all 481 theorems in `Erdos287.SourceChain`.
* `lake env leanchecker <module>` (installed checker; `lean4checker` is not installed): exit 0
  for each of the 19 `SourceChain` content modules checked individually, about 20 s each.
  `AxiomAudit` and the aggregator were not checked separately.
* `lake env leanchecker RequestProject.Erdos287.SourceChain` on the whole aggregate (non-fresh)
  was stopped after about 50 min at roughly 63 GB of memory. `--fresh` on the aggregate was
  therefore **not completed** in this session.
* Token scan, the no-unconditional/no-alias check and the protected-files check all pass.
