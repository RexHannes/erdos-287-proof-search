# Erdős #287 — physical pair-packet source (Part IV of `sources/physical_spec.md`)

**Erdős #287 remains open. `Tail287` is NOT proved unconditionally.** All work is append-only;
earlier modules are unchanged except for one new import line in
`RequestProject/Erdos287/SourceChain.lean`.

## 0. Source file check

* No ZIP archive, no SHA-256 manifest and no `sources/KNOWN_GAPS.md` were present in the
  repository. The specification was present as `physical_spec.md` at the repository root.
  It was copied unchanged to `sources/physical_spec.md` (the root copy is kept).
* `sources/physical_spec.md`: 41,774 bytes, 2,302 lines; SHA-256
  `8a235ea38a40c5d70aec57c56119be6f64f7092c5be9255951f18743b00f0303` (computed here; there was no
  manifest to compare against).
* The file was read in full, through Part XII ("Trust and stop conditions") and the final line
  "Begin with the literal physical packet construction, its designated-pair indexing, and the
  true one-sided seven-block moment interface."

## 1. Files (all new, `RequestProject/Erdos287/SourceChain/Physical/`)

| File | Content |
|---|---|
| `CRT.lean` | exact finite CRT (`crt_int`, `crt_two`), explicit Bézout inverse (`gcdA_inv`), `mul_congr_iff_inv` |
| `Packet.lean` | `PhysData`, `PhysData.WGood`, `Packet` (= `ξ = (j,ℓ,d,d')`), `L`, `omega` (= `ω_d`), `q`, `spec`, `q0`, `f`, `Gamma`, `specRes`, `System`, `cRes`, `Admissible`, `g`, `A`, `B`, `bRes` |
| `Residues.lean` | residue theorems (§§9–10) and `packet_congruence_iff` |
| `PairIdentity.lean` | `Tset`, `InJ`, `Pcount` (= `P_j`), `Vmain` (= `V_j`), `Eerr` (= `E_j`), `Dvec`, `MaynardInner`, `Xi` (= `Ξ_{jℓ}`), `ScalarSieve`, `PairSum`, `PairPackets`, `PairMain`, `PairRem`; the exact pair identity |
| `Remainder.lean` | `pairs`, `XiAll` (= `Ξ`), `RSigmaP` (= `R_Σ^P`), `Rrel`, `Rbase`, `packetTensor` adapter, regression |
| `Presieve.lean` | `physW X = primorial ⌊log log log X⌋`, `wgood_eventually`, `maynardInner_eq_divisors` |
| `Profile.lean` | explicit plateau `physPsi`, `physPsiHat`, `physPF` |
| `Tail.lean` | `OneSidedFrameworkFor`, `tail_of_littleO_for`, `physDataAt`, `PhysicalFamily`, `Tail287_of_physical` (conditional) |
| `AxiomAudit.lean` | build-time `#print axioms` for 35 theorems |
| `../Physical.lean` | aggregator (imported by `SourceChain.lean`) |

## 2. Definitions (literal formulas of the source)

* `ω_d = 1_{(∏d_i,W)=1} (∏ μ(d_i)) ∑_v ∏_i f'_{i,v}(log d_i / log X)` — `PhysData.omega`.
* `ξ = (j, ℓ, d, d')`, `q_i = [d_i, d'_i]`, `q_0 = ∏_{i≠j,ℓ} q_i`, **`f_ξ = a_j W q_0`**,
  **`Γ_ξ = ω_d ω_{d'}`**.
* Admissible support: `j < ℓ`, `d_j = d'_j = d_ℓ = d'_ℓ = 1`, entries positive and coprime to `W`,
  spectator `q_i` pairwise coprime. Distinct labelled tuples are never merged.
* **`c_ξ`** = least solution `< f_ξ` of `p ≡ 1 (mod a_jW)`, `p ≡ 1 - a_j a_i⁻¹ (mod q_i)`
  (every inverse is the explicit Bézout coefficient `Nat.gcdA`).
* `g_{jℓ} = (a_j, a_ℓ)`, `A_{jℓ} = a_ℓ/g`, `B_{jℓ} = (a_ℓ - a_j)/g` (integer).
* **`b_{ξ,d}`** = least `b < f_ξ d` with `b ≡ c_ξ (mod f_ξ)`, `A b ≡ B (mod d)`.
* `𝒥_j(X) = (a_j c₁X+1, a_j c₂X+1)`, `P_j(q,b)` = number of **primes** in `𝒥_j` with
  `p ≡ b (mod q)`, `V_j = ∫ dt/log t` over `𝒥_j` (= `Li` difference), `E_j = P_j - V_j/φ(q)`.
* `PairSum = ∑_t 1_{W∣t} 1_{L_j(t) prime} U_X(L_ℓ(t)) (∑_{d} ω_d)(∑_{d'} ω_{d'})` with
  `d_j = d_ℓ = 1`, `d_i ∣ L_i(t)`, `U_X(v) = ∑_{d∣v} ℓ_X(d)`.
* **`R_Σ^P = ∑_{j<ℓ} ∑_{ξ∈Ξ_{jℓ}} Γ_ξ ∑_{d, (d,f_ξ)=1} ℓ_X(d) E_j(f_ξ d, b_{ξ,d})`** —
  `PhysData.RSigmaP`.
* `W = ∏_{p ≤ log log log X} p` — `physW`.
* `Ψ(u) = θ(4u-2) θ(10-4u)` with `θ = Real.smoothTransition` — `physPsi`.

## 3. Theorems proved (no `sorry`; axioms `propext, Classical.choice, Quot.sound` only)

Residues (§§9–10), under `WGood` and `Admissible`:
`cRes_spec`, `cRes_unique`, `cRes_unit` (`(c_ξ,f_ξ)=1`); `AB_coprime` (`(A,B)=1`, proved, not
assumed); `g_coprime` (`(g,d)=1`); `reduce_iff` (`a_ℓp ≡ a_ℓ-a_j ↔ Ap ≡ B (mod d)`);
`bRes_spec`, `bRes_unique`, `bRes_unit`; `base_iff` (`W∣t ↔ p ≡ 1 (mod a_jW)`);
`spectator_iff` (`q_i ∣ L_i(t) ↔ p ≡ 1-a_ja_i⁻¹ (mod q_i)`); `scalar_iff`;
**`packet_congruence_iff`**: all packet divisibility conditions on `t` ⟺
`L_j(t) ≡ b_{ξ,d} (mod f_ξ d)`.

Pair indexing (§12):
* `cnt_eq` — number of physical `t` = `P_j(f_ξ d, b_{ξ,d})` (bijection `t ↦ a_j t + 1`);
* `cnt_zero_of_not_coprime`, `term_zero_of_not_admissible` — off-support terms vanish;
* **`pairSum_eq_packets`** — literal pair term = `∑_{ξ∈Ξ_{jℓ}} Γ_ξ ∑_{(d,f_ξ)=1} ℓ_X(d) P_j(f_ξ d,b_{ξ,d})`;
* `pairSum_eq_main_add_rem`, `pairTotal_eq_main_add_RSigmaP` — `∑_{j<ℓ} PairSum = Main + R_Σ^P`;
* **`RSigmaP_eq_packetIndexed`** — `R_Σ^P` over the single packet set `Ξ` with `j = j(ξ)`;
* `RSigmaP_eq_rel_add_base` — `R_Σ^P = R_rel + R_base` (§21) on the same support;
* `RSigmaP_eq_sum_packetTensor`, `RSigmaP_eq_sum_rel_paid` — proved adapter to the existing
  generic `TensorSource` (one single-packet source per labelled packet, `ell = 1`);
* `generic_unrestricted_j_overcounts` — regression: an unrestricted generic `j`-sum multiplies
  the remainder by `ell`.

Presieve/profile: `wgood_eventually`, `physDataAt_wgood` (the presieve hypotheses hold at the
physical `W` for large `X`); `maynardInner_eq_divisors` (divisor truncation lossless);
`physPsi_contDiff`, `physPsi_plateau`, `physPsi_hasCompactSupport`, `physPsi_nonneg`,
`physPsi_le_one`.

Conditional tail: `tail_of_littleO_for`, `framework_iff`,
`PhysicalFamily.physical_littleO_of_rel_base`, **`PhysicalFamily.Tail287_of_physical`** —
hypotheses: the one-sided seven-block framework for the physical `R_Σ^P`, the support/presieve
conditions for large `X`, `R_rel = o(𝒩_X I)`, `R_base = o(𝒩_X I)`. Not unconditional.

## 4. Structural finding about the old interface

The existing `TailSourceFamily`/`TensorSource` cannot carry the physical `R_Σ^P` as a single
source: (i) its scalar support must be coprime to every `f_ξ` simultaneously, while the
physical support condition `(d, f_ξ) = 1` depends on `ξ`; (ii) its sequences `α_j` cannot
depend on `ξ`, while the window is `𝒥_{j(ξ)}`. Hence `physicalTailSource : TailSourceFamily`
in the old sense is not instantiable faithfully; the packet-wise adapter
(`RSigmaP_eq_sum_packetTensor`) and the remainder-function tail boundary
(`tail_of_littleO_for`, equivalent to the old one by `framework_iff`) replace it.

## 5. Formulas still unavailable, and the first theorem each blocks

| Missing exact formula | First blocked theorem |
|---|---|
| The low-prime fundamental-lemma weights `λ_low^±` at level `D_low` (§15 names them but gives no construction), and the concrete grid of high-prime box endpoints `P_h` (§14 gives only the constraints) | the definition of `ℓ_X` itself (here `ScalarSieve.coeff` is a parameter), hence the pointwise claim `U_X ≥ 0` / majorisation (§15) |
| Type-II coefficients `c_{ξ,l,r}` and the sequences `α_n` from the Heath–Brown decomposition (§§20, 24) | the physical Ordering-B square `V_ξ` (§24), i.e. `physicalOrderingBCells` |

`sources/KNOWN_GAPS.md` was not in the repository, so these were identified directly against the
specification.

## 6. What remains open (not claimed)

* Seven-block framework (actual slopes from `prescribedShape_gcdClique`, Maynard weights `w_X`,
  the one-sided moment asymptotics): still the hypothesis `OneSidedFrameworkFor`.
* `R_rel = o(𝒩_X I)` and `R_base = o(𝒩_X I)`: analytic, still hypotheses.
* Poisson summation for `physPsi`, Ordering-B cells, atom map, `W_4` estimates: not done.

## 7. Checks

* `lake build RequestProject.Erdos287.SourceChain` — success (8117 jobs), including all new modules.
* No `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `implemented_by` in the new files
  (the only textual hits are the words "admits" and "sorryAx" in comments).
* `#print axioms` for 35 new theorems: `[propext, Classical.choice, Quot.sound]`.
* `leanchecker` exits 0 on each of the 8 new content modules, checked one at a time.
* The full `SourceChain/audit.sh` (which re-runs checker passes on the whole subtree) did not
  finish within the time limit in this session and is not reported as passed.
