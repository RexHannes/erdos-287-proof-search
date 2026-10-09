# Erdős #287 — top-layer / prime-power exclusion package: re-audit (2026-10-08)

This is not a claim that #287 is solved. It re-checks only the elementary structural package.

## Files (no Lean source was changed in this audit)
- `RequestProject/Erdos287/Defs.lean`: `topExp`, `topLayer`, and the computable `C`
- `RequestProject/Erdos287/TopLayer.lean`
- `RequestProject/Erdos287/Cnum.lean`
- `RequestProject/Erdos287/Window.lean`
- `RequestProject/Erdos287/Counterexample.lean`: the `Gap2CE` structure
- `RequestProject/Erdos287/PrimeFree.lean`
- `RequestProject/Erdos287/Blocker.lean`

## Theorems, all proved
| Item | Lean name |
|---|---|
| 1 | `Erdos287.topLayer_congruence` |
| 2 | `Erdos287.topLayer_card_ne_one`, `Erdos287.topLayer_two_obstruction`, `Erdos287.topLayer_three_obstruction` |
| 3 | `Erdos287.C_values` (by kernel `decide`), `Erdos287.C_seven_witness` (num of 1+1/2+1/3+1/4+1/5+1/7 = 1019/420 is 1019), `Erdos287.C_spec` (`C j` is the greatest numerator), `Erdos287.C_mono`; extra: `C_nine : C 9 = 7129` |
| 4 | `Erdos287.primePower_window_exclusion` |
| 5 | `Gap2CE.holes_isolated`, `Gap2CE.N_mem`, `Gap2CE.M_mem`, `Gap2CE.exp_lower`, `Gap2CE.exp_upper`, `Gap2CE.N_gt_M_div_eight` |
| 6 | `Gap2CE.primeFree` (needs `8152 ≤ M`) |
| 7 | `Gap2CE.blockerPair_contradiction`, and `Gap2CE.excludedPP_blockerPair` (the two holes come from excluded prime powers) |

## Checks
- `lake build` of the seven modules above succeeds. The only warning is the unused hypothesis `hqM` in the window theorem, which was kept because the statement asks for it.
- `#print axioms` for every theorem above gives only `propext`, `Classical.choice` and `Quot.sound`. `C_values` uses no axioms.
- These files contain no `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `native_decide` or `bv_decide`.
- No statement failed, so there is no counterexample to report.

## Formalization notes
- The `Gap2CE` gap condition is: every `a ≠ max A` in `A` has `a+1 ∈ A` or `a+2 ∈ A`. This is the same as saying all consecutive gaps are `≤ 2`.
- `C j` is computed exactly with rational arithmetic over sublists of `[1..j]`. It is linked to `Rat.num` by `numOf_eq_num`.
- `primePower_window_exclusion` keeps the hypothesis `q ≤ M` from the requested statement, but the proof does not use it.
