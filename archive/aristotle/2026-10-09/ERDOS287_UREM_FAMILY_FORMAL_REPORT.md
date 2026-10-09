# Erdős #287 — family-averaged Urem estimate: formal report

**Verdict: `UREM PAPER REPAIRED; PUBLISHED ANALYTIC FORMALIZATION REMAINS`.
Erdős #287 is still open. `Tail287Statement` is NOT proved.**

All earlier declarations are kept unchanged, including `not_ordinaryBVUremProviderScoped`
(the packetwise provider is still false and is no longer on any route used here).

## 1. What was built (all in `RequestProject/Erdos287/SourceChain/Physical/TypeII/`)

| File | Content |
| --- | --- |
| `UremFamilyFinite.lean` | discrepancies `disc` (E), `relDisc` (Δ); CRT projection (3.2); energy contraction (3.3); occupancy count; packet Cauchy (5.4) |
| `UremFamilyResidue.lean` | exact residue rearrangement (5.1) of the literal `physUrem` inner sum |
| `UremFamilyCauchy.lean` | residue-pair occupancy (5.2); per-packet Cauchy (5.3) with relative energy `R_r(f)` |
| `UremFamilyCompose.lean` | per-packet bound, modulus grouping (4.2), family bound in terms of the BDH energy |
| `UremFamilyPhysical.lean` | `physUrem` = sum of family blocks (actual atom coefficients); unconditional physical family bound |
| `UremFamilyMaynard.lean` | statement of Maynard I Def. 1 (6.1) and Lemma 13.8; SW masking; Maynard ⇒ masked BDH energy; Maynard ⇒ physical family bound |
| `UremFamilyMultiplicity.lean` | packet multiplicity of the literal packets: `a_f ≤ (V B_f^k)² k² τ(f)^{2k}` |
| `UremFamilyActual.lean` | instantiation on literal `PhysData` packets; reconnection to `scalarTypeII_eq_cells` |

`SourceChain/Physical.lean` imports the new files; `SourceChain/RepairAudit.lean` prints axioms.
Build: `lake build RequestProject.Erdos287.SourceChain RequestProject.Erdos287.SourceChain.RepairAudit`
succeeds. No `sorry`, `axiom`, `native_decide`, `unsafe` or `implemented_by` in the new files. Every
new theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.

## 2. Proved theorems (kernel-checked, no hypotheses beyond those displayed)

Finite exact adapter (report §§3, 5):
* `relDisc_eq_projection` — (3.2) Δ^{f,c}(l,a) = E(fl, CRT(c,a)) − φ(l)⁻¹ Σ*_{a'} E(fl, CRT(c,a')), for (f,l)=1.
* `relDisc_energy_le` — (3.3) Σ*_c Σ*_a Δ² ≤ Σ*_{b mod fl} E(fl,b)² (no φ(f), φ(l) loss).
* `inner_urem_eq_relDisc` — (5.1) for the literal inner sum of `physUrem`:
  Σ_{v<K'} (α*β)(v) 1_{v≡c(f)} h_l(v) U_r(v) = φ(r)⁻¹ Σ_m β_m 1_{(m,flr)=1} Δ^{f,c m̄}_{α^{(r)}}(l, B(Am)⁻¹),
  under (c,f)=1 and (A|B|, l)=1 only. No inverse of A mod f is used.
* `sum_occupancy_le` — (5.2) each unit residue pair is hit at most M/(fl)+1 times in [M,2M).
* `urem_r_sq_le_relative_energy` — (5.3) Y² ≤ (Σ z²)(Σ β²)(M/(fL)+1) R_r(f), with the actual β L² norm.
* `packet_weighted_cauchy`, `weighted_cauchy` — (5.4).
* `energy_grouping` — (4.2) Σ_f a_f R_r(f) ≤ C_a Σ_{q<2FL} τ(q)^{K+1} Σ*_b E(q,b)² when a_f ≤ C_a τ(f)^K.
* `family_urem_le_bdhEnergy` — family bound for a packet family sharing one sequence.

Physical source:
* `physUrem_eq_uremBlocks` — exact: `physUrem` = Σ_{J,P,χ} Σ_r φ(r)⁻¹ Σ_i Y(2^i, r) with the actual
  coefficient `physCoefCut` (Γ occurs exactly once, inside `physCoefCut`).
* `physical_family_urem_le` — **unconditional**: for one group (common α, packet-dependent β, Γ, f, c, A, B),
  Σ_ξ |physUrem_ξ| ≤ Σ_{J,P,χ} Σ_r φ(r)⁻¹ Σ_{i<n₀} W_{J,P} √Bβ √(Σ_ξ|Γ_ξ|(M/f_ξ+2^i)) √(C_a · bdhEnergy(α^{(r)}, 2F2^i)).
* `packet_multiplicity` — for literal packets with a bounded tensor, Σ_{ξ: f_ξ=f} |Γ_ξ| ≤ (V B_f^k)² k² τ(f)^{2k}
  (all spectator multiplicities kept; no squarefree saving used).
* `physData_f_pos`, and (from earlier) `PhysData.cRes_unit`, `physData_affinePrimesDivideBase`.
* `group_typeII_sub_cells_le` — reconnection: any bound on Σ_ξ|physUrem_ξ| bounds
  |Σ_ξ scalarTypeII_ξ − Σ_ξ (cells)_ξ| (from `scalarTypeII_eq_cells`).

Analytic layer:
* `SWCondition` — Maynard I Definition 1, (6.1), transcribed from arXiv:2006.06572v2
  (n ∼ N means N < n ≤ 2N; every d ≥ 1, q ≥ 1, (a,q)=1, A > 1; bound c_A N τ(d)^{B₀}/(log N)^A).
* `MaynardLemma13_8` — Lemma 13.8 as a `Prop` (weaker quantifier order: the cutoff exponent C may also
  depend on the SW constants, so the published statement implies it). **Not proved; not an axiom.**
* `swCondition_masked` — proved: SW is preserved by α ↦ α·1_{(n,r)=1}/τ(r)^{B₀}.
* `bdhEnergy_masked_le` — proved from `MaynardLemma13_8`: bdhEnergy(α^{(r)}) ≤ (τ(r)^{B₀})² C' N²/(log N)^A.
* `physical_family_urem_maynard`, `actual_family_urem_maynard` — proved from `MaynardLemma13_8`:
  the family Urem bound for the literal packets with each BDH energy replaced by
  (τ(r)^{B₀})² C' N'²/(log N')^A, N' = N_n − 1/2.

No argument of type `OrdinaryBVUremProviderScoped` or `OrdinaryBVUremProviderRepaired` appears in any of these.

## 3. Hypotheses still carried by `actual_family_urem_maynard`

1. `MaynardLemma13_8` — published theorem (Maynard I, Lemma 13.8).
   **Formalization gap, not a missing proof.**
2. `SWCondition α (N_n − 1/2) B₀ cSW` and `|α_n| ≤ τ(n)^{B₀}` for the **actual** `alphaSeq`
   (rough constant / rough log / rough truncated μ, normalized by 1+log 2N for the log case).
   Paper proof: report §6.2–6.3 (fundamental lemma; Siegel–Walfisz for μ; Maynard II Lemma 5.4).
   **Not formalized.** This is the first remaining source-fit obligation of the Urem branch.
3. `Σ_m |β_ξ(m)|² ≤ Bβ` — follows from the proved pointwise bound `abs_betaSeq_le` plus a divisor
   moment bound; the moment bound is not formalized.
4. Base cap `f_ξ ≤ F`, band cap `l < 2^{n₀}` for nonzero coefficients (available from `physCell_contract`:
   l ≤ N X^{−κ}), and the cutoff `2F·2^{n₀} ≤ N'/(log N')^C` (true eventually when F = X^σ, σ < κ).
5. Collapsing the explicit bound to `C X/(log X)^{A*}` needs: Σ_{r<K} τ(r)^{B₀}/φ(r) ≪ (log X)^{C₃} (5.5),
   Σ_ξ|Γ_ξ|/f_ξ ≪ (log X)^{K₁} (2.7, from `packet_multiplicity`), the number of bands ≪ log X,
   the atom total variation (`total_variation_le`, proved), and MN ≍ X. These are elementary but
   **not formalized** here.

## 4. Remaining independent obligations for Tail287 (Priority 2), unchanged by this work

1. Actual critical Pascadi/spectral estimate on `physCell` (Kloosterman/Deshouillers–Iwaniec input): not formalized, and the
   source fit (fixed affine data, roughness, SW, base exponent, normalization) is not proved.
2. Corrected FCHS/W4 estimates on actual atoms: not proved.
3. Exhaustive noncritical HB routing, prime-power and partial-summation errors: not proved.
4. Base-only remainder (ordinary BV) and relative main-term normalization: not proved.
5. One-sided seven-block framework and contact windows: not proved.

## 5. Strongest completed unconditional statement

`physical_family_urem_le` (with `packet_multiplicity`, `physUrem_eq_uremBlocks`,
`group_typeII_sub_cells_le`): the literal Urem family sum is bounded, with no analytic hypothesis, by
explicit atom weights × packet density × complete-modulus BDH energies of the masked common sequence.
The first remaining obligation is the Siegel–Walfisz condition (6.1) for the actual `alphaSeq`
(together with formalizing Maynard I, Lemma 13.8 itself).

`Tail287Statement` is **not** established, at paper level or in Lean.
