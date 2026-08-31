# ERDŐS #287 — PRIMITIVE-CONDUCTOR / SHORT-LIFT REDUCTION Δ
## SAFE BANK REPORT (append-only)

```
FRONTIER BEFORE : 287-K0-SP2-DET1-PRIMITIVE-CONDUCTOR-SHORTLIFT-GRAM45
FRONTIER AFTER  : 287-K0-SP2-DET1-PRIMITIVE-LOCALPROFILE-GRAM45
```

Mode: exact algebra + finite combinatorics + append-only status bank.
No new analytic number theory is proved. No `axiom`, `sorry`, `admit`, `opaque`, `unsafe`,
`native_decide` or `@[implemented_by]` occurs in any file of this delta.

---

### FILES ADDED

| file | content |
|---|---|
| `RequestProject/CurrentProgramme/PrimitiveRamanujanAlgebra.lean` | §A primitive `t` Ramanujan algebra |
| `RequestProject/CurrentProgramme/PrimitiveRamanujanReassembly.lean` | §B representation loop |
| `RequestProject/CurrentProgramme/ShortLiftLocalProfile.lean` | §C local profile + finite Euler collapse + analytic socket |
| `RequestProject/CurrentProgramme/PrimitiveDMultiplicity.lean` | §D `D`-frequency multiplicity |
| `RequestProject/CurrentProgramme/PrimitiveFareyNearCollision.lean` | §E Farey near-collision finite count |
| `RequestProject/CurrentProgramme/PrimitiveLocalProfileGramSocket.lean` | §F current source socket |
| `RequestProject/Status/CurrentStatusErdos287PrimitiveLocalProfile.lean` | §G append-only status layer |
| `RequestProject/Status/AxiomAuditErdos287PrimitiveLocalProfile.lean` | §H axiom audit |

`RequestProject/Main.lean` received **import lines only**. No historical file was modified.

---

### FORMALLY PROVED

**§A — Ramanujan algebra.** The Ramanujan sum is built from the repository's own additive
phase `Erdos287.NormalForm3221.phase x = exp(2πix)`:

```
ramanujan g N = ∑_{t < g, gcd(t,g)=1} e(tN/g).
```

* `full_phase_sum` — `∑_{t<g} e(tN/g) = g·1_{g ∣ N}`.
* `ramanujan_eq_divisor_sum` — **DET1-PRIMITIVE-RAMANUJAN-DIVISOR-NORMALFORM45**:
  `c_g(N) = ∑_{r ∣ gcd(g,N)} r·μ(g/r)`, proved from the exponential-sum definition
  (Möbius expansion of the coprimality indicator, sum interchange, `r`-multiples reindexing,
  `r ↦ g/r` duality).
* `ramanujan_congr`, `ramanujan_unit_mul` — invariance mod `g` and under multiplication by a
  unit.
* `ramanujan_unit_shift` — **DET1-PRIMITIVE-T-RAMANUJAN45**: for `2b·w ≡ 1 (mod g)`,
  `c_g(a + s·w) = c_g(2ab + s)`.
* `moebius_mul_moebius_div` — for squarefree `g = r·k`, `gcd(r,k)=1`: `μ(g)·μ(g/r) = μ(r)`.
* `ramanujan_moebius_normalForm` — **DET1-RAMANUJAN-MOBIUS-SIMPLIFICATION45**:
  `μ(g)/g · c_g(N) = ∑_{rk = g, r ∣ N} μ(r)/k`.

**§B — reassembly (representation loop).**

* `reassemblyBranch_of_coprime` — on the sector `gcd(2b,n) = 1`,
  `∑_{kd=n} μ(d)1_{gcd(2b,k)=1}1_{gcd(b,d)=1} = [n = 1]`: the `r > 1` cancellation.
* `moebius_properDivisors_sum` — `∑_{d ∣ n, d < n} μ(d) = -μ(n)` for `n > 1`.
* `primitive_ramanujan_reassembly` — **DET1-PRIMITIVE-RAMANUJAN-REASSEMBLY45**:
  `μ(g)/g · c_g(N) = rawProgression(g,N) − additiveZeroMode(g,N)`.
  `REPRESENTATION LOOP; FORMALLY VERIFIED; NOT FALSE` — an identity between two descriptions
  of the same finite sum, not an estimate.

**§C — short-lift local profile (algebra only).**

* `mProfile g b D Ψ T` — the finite/dyadic profile `∑_{d ≤ T, gcd(d,2bg)=1} μ(d)/d·Ψ(d/D)`,
  with `mProfileSharp`, additivity and homogeneity in `Ψ`.
* `mProfileDivisor_euler_product` — for squarefree `n`:
  `∑_{d ∣ n, gcd(d,H)=1} μ(d)/d = ∏_{p ∣ n, p ∤ H}(1 − 1/p)`.
* `shortLift_euler_collapse_finite` — the `H_H/ζ` shape at the finite-prime-product level:
  `= (∏_{p ∣ n}(1 − 1/p)) · ∏_{p ∣ n, p ∣ H}(1 − 1/p)⁻¹`.

**§D — multiplicity.**

* `dLine_solution_form` — all integer solutions of `r₂t₁ − r₁t₂ = D` are
  `t₁ = t₁⁰ + r₁u`, `t₂ = t₂⁰ + r₂u`.
* `dSolutionSet_card_le` — **DET1-PRIMITIVE-D-MULTIPLICITY45**: at most `g₀ + 1` solutions in
  the box `1 ≤ tᵢ ≤ gᵢ` (the proof gives the sharp `g₀`, banked as
  `dSolutionSet_card_le_g0`).

**§E — Farey near-collisions (exact finite precursor).**

* `lcm_of_coprime_cofactors` — `lcm(g₀r₁, g₀r₂) = g₀r₁r₂`.
* `farey_near_collision_D_bound` / `farey_near_collision_lcm_bound` —
  `|t₁/g₁ − t₂/g₂| ≤ 1/A ⟹ |D| ≤ lcm(g₁,g₂)/A`, exact rational arithmetic.
* `nearCollisionSet_card_le` — with the explicit integer floor `B = ⌊lcm(g₁,g₂)/A⌋`, the
  number of near-collision pairs in the box is `≤ (2B+1)·g₀`, by fibring over `D` and
  applying §D.

---

### ANALYTIC / UNINHABITED

* `Erdos287.ShortLift.ShortLiftEulerAnalyticInput` — the literal Dirichlet-series identity
  `∑_{gcd(d,H)=1} μ(d)d^{-s} = H_H(s)/ζ(s)` for `Re s > 1`.  **No inhabitant.**  Only use:
  the trivial conditional consumer `shortLift_euler_collapse_of_input`.
* `Erdos287.PrimitiveLocalProfile.PrimitiveLocalProfileGramInput` — the Gram-side analytic
  target `|Gram(c)| ≤ C·X·(log X)^{-3-η}`, uniformly over valid local-profile
  primitive-conductor configurations.  **No inhabitant**; `primitiveLocalProfileGram_not_automatic`
  exhibits explicit refuting data, and `exists_valid_config` shows the configuration class is
  nonempty (so the socket is neither vacuous nor automatic).

Nothing of the shape `exp(−c√(log D))`, and no arbitrary-log cancellation, is formalised.

---

### RESEARCH STATUS

```
DET1-PRIMITIVE-T-RAMANUJAN45                 : FORMALLY PROVED
DET1-PRIMITIVE-RAMANUJAN-DIVISOR-NORMALFORM45: FORMALLY PROVED
DET1-RAMANUJAN-MOBIUS-SIMPLIFICATION45       : FORMALLY PROVED
DET1-PRIMITIVE-RAMANUJAN-REASSEMBLY45        : REPRESENTATION LOOP; FORMALLY VERIFIED; NOT FALSE
DET1-SHORTLIFT-EULER-COLLAPSE45              : RESEARCH PASS CANDIDATE; ANALYTIC / UNINHABITED;
                                               NANC PROMOTION AUDIT PENDING
DET1-PRIMITIVE-D-MULTIPLICITY45              : FORMALLY PROVED
DET1-PRIMITIVE-FAREY-NEARCOLLISION45         : COMBINATORIAL PASS (exact finite precursor proved);
                                               ANALYTIC MIXED-WEIGHT ROUTING OPEN
```

The displayed asymptotic `gcd(g₁,g₂) + g₁g₂/A` is **not** formalised (range/asymptotic
notation absent from the repository); only the exact finite precursor is banked and the
asymptotic wrapper stays conditional.

---

### SUPERSEDED BUT NOT FALSE

```
PRIMITIVE-CONDUCTOR-SHORTLIFT-GRAM45 : SUPERSEDED AS CONTROLLING FRONTIER;
                                       STRICTLY REDUCED; NOT FALSE
```

recorded in the ledger as `supersededNotFalse` (`shortLiftGram_superseded_not_false`); no row
of this ledger is `closed`.

### CURRENT STATUS

```
PRIMITIVE-LOCALPROFILE-GRAM45 : ANALYTIC OPEN; UNINHABITED; FIRST EXACT MAIN-LINE RESIDUAL
UNIFORM k=0                   : OPEN
FCL                           : NOT REACHED
ERDOS287                      : OPEN
```

(`localProfileGram_is_first_exact_mainline_residual`, `uniform_k0_open_fcl_not_reached`,
`erdos287_open`, `no_closed_rows`.)

---

### BUILD

`lake build` — 8243 jobs, 0 errors.  Every new module also builds individually.  The only
warning in the repository is the pre-existing linter note at
`RequestProject/Erdos287/FixedCertificateSmoothParity.lean:60`, untouched by this pass; the
new files are warning-free.

### AXIOM AUDIT

`RequestProject/Status/AxiomAuditErdos287PrimitiveLocalProfile.lean` prints axioms for every
principal new declaration.  All results are subsets of `{propext, Classical.choice,
Quot.sound}`; two status rows depend on no axioms at all.  No `sorryAx`, no custom axiom, no
hidden proof escape.

### COMMITS / PUSH

Staged and pushed in phases: §A; §B; §C; §D+§E; §F+§G+§H + report + `Main.lean` imports.

---

```
ERDOS287 OPEN.

FIRST EXACT MAIN-LINE RESIDUAL:
287-K0-SP2-DET1-PRIMITIVE-LOCALPROFILE-GRAM45.
```
