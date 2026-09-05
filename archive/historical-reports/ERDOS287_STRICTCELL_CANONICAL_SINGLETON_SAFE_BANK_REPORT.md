# ERDŐS #287 — STRICT-CELL CANONICAL-SINGLETON FRONTIER
## Append-only safe-bank report

**Erdős #287 is not solved and is not claimed to be solved.**  The analytic singleton
Type-II estimate is **not** proved; it is banked as an explicitly uninhabited input.

---

## 1. Files

### Added (four new modules, one report)

| file | content |
|---|---|
| `RequestProject/CurrentProgramme/Erdos287StrictCellCanonicalSingleton.lean` | items 1–13, 15, 17, 18 of the request |
| `RequestProject/CurrentProgramme/Erdos287StrictCellProductWeightBridge.lean` | items 14, 16, 19 (two uninhabited interfaces + conditional compilers) |
| `RequestProject/Status/CurrentStatusErdos287StrictCellCanonicalSingleton.lean` | item 20 (new authoritative status layer) |
| `RequestProject/Status/AxiomAuditErdos287StrictCellCanonicalSingleton.lean` | 83 × `#print axioms` |
| `ERDOS287_STRICTCELL_CANONICAL_SINGLETON_SAFE_BANK_REPORT.md` | this report |

### Modified

* `RequestProject/Main.lean` — **four appended `import` lines only**.  No existing line was
  changed, reordered or deleted.

Nothing else in the repository was touched: no file was deleted, renamed, weakened or
relocated, and no earlier status layer was rewritten.  `ARISTOTLE_SUMMARY.md` was not edited.

---

## 2. What was formalised, item by item

**1. Exact weighted prime-vector → integer pushforward.**
`cellVectors`, `pushforward`, `omegaSharpFibre`, `OmegaSharp` (the pushforward `Ω♯_C(w,n)` of
a weight `w` along `v ↦ ∏ᵢ vᵢ`), with `OmegaSharp_unitWeight`,
`OmegaSharp_eq_zero_of_not_mem_image`, `mem_omegaSharpFibre_iff`.

**2. `Ω♯_C = 1` is not automatic.**  `omegaSharp_one_not_automatic`: the balanced certificate
`λᵢ = {2,3}` satisfies the banked `SP2PacketNormalization`, and the fibre over `2⁶·3 = 192`
has mass `7` (`countermodel_fibre_card`, `omegaSharp_eq_seven`).

**3. `k = 0` and `J = ∅`.**  `StrictCellHypotheses` states the collapse as
`C.k + C.J.card = 0`; `strictCell_k_zero` and `strictCell_J_empty` derive the two conditions,
`strictCell_packetNormalization` recovers the banked packet metadata, and
`strictCellHypotheses_inhabited` is a non-vacuity guard.

**4. Balanced-seven divisor depth and `H^* = -20`.**  `depthSubsets`,
`balancedSeven_divisorDepth` (`C(6,3) = 20` depth-3 divisor patterns on the six-prime
complement), `hStar`, `hStar_eq_neg_twenty`, `hStar_constant`.  No `HStar` symbol existed in
the repository before this pass; the banked binomial value
`Erdos287.BalancedSeven.balancedSeven_lowSum_eq_neg20` (`∑_{j≤3}(−1)^j C(7,j) = −20`) was
**reused, not re-proved**, and the consistency of the two readings is recorded in
`hStar_eq_balancedSevenLowSum`.

**5. Physical Ford coordinate count.**  `slotCount U = |U| + 1`, `rankCount U = 8 − |U|`,
`coordCount`, `ford_coordCount_eq_nine` (`N = 9` for every `U ⊆ Fin 7`), plus
`slotCount_le_four`, `rankCount_ge_five` on the small branches.

**6. 64 branches.**  `fordBranches_card : #{U ⊆ Fin 7 : |U| ≤ 3} = 64` (kernel `decide`;
`1 + 7 + 21 + 35`), with `mem_fordBranches`.

**7. Seven prime coordinates, two unit coordinates.**  `CoordKind`, `coordKind`,
`physicalPrimeCoords_card = 7`, `terminalUnitCoords_card = 2`, `coordKind_partition = 9`.

**8. All physical `k = 0` (7.20) conditions.**  `PhysicalK0Conditions720` (twelve fields) and
`physicalK0_of_strictCell`: every field is a consequence of the strict-cell hypotheses.

**9. No `d_{h,j}` variables.**  `dIndex`, `dIndex_eq_empty`, `dIndex_card_zero`, plus
`dIndex_not_automatically_empty` showing the hypothesis `k = 0` is genuinely used.

**10. Deterministic canonical singleton.**  `canonicalSingleton U` = least coordinate outside
`U`, with `canonicalSingleton_not_mem`, `canonicalSingleton_le` and the pinning theorem
`canonicalSingleton_unique`.

**11. Singleton Type-II window.**  `singleton_mem_window` (`v(i(U)) ∈ [Y,Z]`),
`complement_pushforward_bounds` (`[Y⁶, Z⁶]`), `pushforward_bounds` (`[Y⁷, Z⁷]`).  This is the
*window* only; the analytic estimate is not proved.

**12. No generic subsum inclusion–exclusion.**  `cellVectors_card`, `omegaSharp_total_mass`
(exact total mass `∏ᵢ|λᵢ|` summed over the image of the pushforward) and
`productWeight_total_mass` (`∑ᵥ ∏ᵢ fᵢ(vᵢ) = ∏ᵢ ∑_{p∈λᵢ} fᵢ(p)`), both exact identities.

**13. Zero Ford hard-condition Perron contour count.**  `fordHardConditions`,
`perronContourCount`, `perronContourCount_eq_zero`.

**14. `BalancedSevenSP2StrictCellProductWeightPhysicalBridge` — UNINHABITED.**  Explicit
fields: slot-box physical cell (`slotBox_cell`, `slotBox_weight`), product or fixed-nuclear
vector weight (`weight_form`), distinctness / repeated-prime routing (`routing`), Ford-`H`
binding (`ford_H_binding`), cutoff binding (`cutoff_binding`), physical `B` binding
(`B_binding`), plus the kernel data (`kernel_separable`, `kernel_normalised`) and the
strict-cell hypotheses.  No inhabitant is constructed anywhere in the repository;
`bridge_not_automatic` exhibits data refuting it, and `bridge_is_an_input_not_a_theorem`
records that the conditional compilers are implications only.

**15. Counterguards.**  `weight_not_product_separable` (the diagonal cell weight is not
rank-one) and `kernel_not_automatically_separable` (the diagonal kernel is not rank-one): an
arbitrary `C.Om` does **not** imply rank-one / product separation.

**16. Exact factorisation `K(m,n) = ξ(m)·κ(n)` and the six-prime complement.**
`bridge_kernel_factorisation`, with the canonical deterministic factors `xiOf K n₀ m =
K(m,n₀)` and `kappaOf K m₀ n = K(m₀,n)`; `kernel_canonical_factor_eq` pins the factor against
any other factorisation.  `bridgeSixPrimeComplement` is the six-prime complement definition.

**17. Complement depth `6`.**  `complementDepth_eq_six`, `bridge_complement_depth_eq_six`,
with `canonicalSingleton_not_mem_complement` and `singleton_union_complement`.

**18. Deterministic finite Cauchy / product-energy interfaces.**  `finite_cauchy_schwarz`,
`productEnergy_factorises`, `cell_cauchy_productEnergy`.

**19. `SP2LabelledSingletonGeneratedTypeIIInput` — UNINHABITED.**  The exact bilinear
inequality in the splitting singleton coordinate against the six-prime complement, with the
window, labelling and gain fields.  `typeII_input_not_automatic` refutes it at explicit
parameters.  The estimate itself is **not** proved.

**20. New authoritative status layer** (`strictCellLedger`):

```
GENERIC FORD723 CENSUS                                       : SUPERSEDED
SP2-LABELLED64-CANONICALSINGLETON-PACKETCENSUS45             : KERNEL-PROVED
                                                               CONDITIONAL ON
                                                               PHYSICAL BRIDGE
BALANCED7-SP2-STRICTCELL-PRODUCTWEIGHT-PHYSICAL-BRIDGE45     : OPEN / UNINHABITED
SP2-LABELLED-SINGLETON-GENERATEDTYPEII45                     : OPEN ANALYTIC
ERDOS287                                                     : OPEN
```

with the ledger facts `erdos287_open`, `ford723Census_superseded`,
`superseded_ne_retracted`, `packetCensus_conditional`, `bridge_open`, `typeII_open`,
`unique_kernelProved_row`, the eleven `backing_*` theorems tying the kernel-proved row to
actual theorems, `census_is_an_implication` (the census is an implication out of the
uninhabited bridge), and the scope guards `no_analytic_typeII_claimed`,
`erdos287_not_closed`.

---

## 3. Build and audit

* Baseline `lake build` before this pass: success, **8330 jobs**, 0 errors, 32 cosmetic
  warnings in pre-existing files.
* `lake build` after this pass: success, **8334 jobs**, **0 errors**, the same **32**
  pre-existing warnings — **0 warnings from the new modules**.
* `RequestProject/Status/AxiomAuditErdos287StrictCellCanonicalSingleton.lean` emits **83**
  `#print axioms` reports for every principal new theorem.  Across the whole build log every
  reported axiom set is a subset of `{propext, Classical.choice, Quot.sound}`; **zero**
  occurrences of `sorryAx`.
* Repository scan of the new files for `sorry`, `admit`, `axiom`, `unsafe`, `opaque`,
  `native_decide`, `implemented_by` as Lean code: **none**.  (The strings occur only inside
  docstring prose, e.g. "admits no factorisation".)
* All finite censuses (`64`, `7`, `2`, `9`, `20`, `6`, `128`, the fibre count `7`) are closed
  by kernel `decide`, never by `native_decide`.

---

## 4. Scope statement

Proved unconditionally: the finite strict-cell package (items 1–13, 15, 17, 18).
Proved conditionally on the uninhabited physical bridge: the packet census, the exact kernel
factorisation and the physical `k = 0` consequences (items 14, 16).
Left open: the physical bridge, the labelled singleton-generated Type-II analytic input, and
Erdős #287 itself.
