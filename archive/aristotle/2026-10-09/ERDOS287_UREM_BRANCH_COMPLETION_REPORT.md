# Erdős #287 — Urem branch: completion report

**Verdict: UREM BRANCH PAID, CONDITIONAL ON TWO PUBLISHED ANALYTIC INPUTS.
Erdős #287 is still open. `Tail287Statement` is NOT proved.**

In Lean, the Urem contribution of an actual Heath–Brown cell, summed over any family of literal
packets, is now bounded by `O_A(X/(log X)^A)` for every `A > 0`. The only mathematical
hypotheses are:

1. `MaynardLemma13_8`: Maynard I, Lemma 13.8, a published theorem. It is not formalized and is
   stated as a `Prop`. It is never an axiom.
2. `IntervalSWAt`: Maynard's Siegel–Walfisz condition (6.1) on initial segments, required for the
   two base sequences `1_{P^-(n) ≥ z₀}` and `μ(n) 1_{P^-(n) ≥ z₀}` at the actual scale and with
   uniform constants. This is a Siegel–Walfisz-type input (paper-level, §4 below), not formalized.

No `Ordinary…Provider`, `Pascadi…Provider` or other provider statement appears. Every other
hypothesis is a parameter-range condition (§3).

All earlier declarations are kept and none were renamed: CRT, energy contraction, packet Cauchy,
source reconstruction and multiplicity. `not_ordinaryBVUremProviderScoped` is unchanged.

## 1. Files added or changed

All new files are in `RequestProject/Erdos287/SourceChain/Physical/TypeII/`.

| File | Content |
| --- | --- |
| `UremFamilyMoments.lean` | elementary divisor moments (Mathlib only) |
| `UremFamilySW.lean` | SW weight form, interval SW, truncation, Abel summation, log normalisation, SW + divisor bound for the actual `alphaSeq` |
| `UremFamilyAggregate.lean` | packet density, atom total, explicit family bound |
| `UremFamilyCell.lean` | linearity of `physUrem`, support and dyadic splitting of the actual `betaSeq`, the actual `β` second moment, the cell bound |
| `UremFamilyFinal.lean` | absorbing the polylogarithmic losses: `cell_urem_polylog`, `cells_urem_polylog` |

`SourceChain/Physical.lean` now imports `UremFamilyFinal`. `SourceChain/RepairAudit.lean` has
`#print axioms` lines for every theorem listed below.

**Build:** `lake build RequestProject.Erdos287.SourceChain RequestProject.Erdos287.SourceChain.RepairAudit`
succeeds (8164 jobs). The five new files contain no `sorry`, `admit`, `axiom`, `native_decide`,
`unsafe` or `implemented_by`. Every new theorem depends only on
`[propext, Classical.choice, Quot.sound]`.

## 2. Theorems

"Unconditional" means the theorem has no analytic hypothesis at all. "Conditional" means it
takes (1) and/or (2) as explicit hypotheses. Every theorem below is kernel-checked.

### 2.1 Unconditional elementary estimates (`UremFamilyMoments.lean`)

* `sum_tau_pow_div_le (x k : ℕ) : ∑ n ∈ Icc 1 x, (τ n)^k / n ≤ (1 + log x)^(2^k)`.
  Proof: since `τ(ab) ≤ τ(a)τ(b)`, the `(k+1)`-st moment is at most the square of the `k`-th.
  The case `k = 0` is `H_x ≤ 1 + log x`.
* `nat_le_card_divisors_mul_totient (n) : n ≤ τ(n) φ(n)`. Proof: `n = ∑_{d∣n} φ(d)` and `φ(d) ∣ φ(n)`.
* `sum_tau_pow_div_totient_le (K B : ℕ) : ∑ r ∈ Ico 1 K, τ(r)^B / φ(r) ≤ (1 + log K)^(2^(B+1))`.
  This is the reciprocal-divisor moment (5.5).
* `sum_tau_pow_le`, `sum_Ico_tau_pow_le`: `∑_{n ≤ x} τ(n)^k ≤ x (1 + log x)^(2^k)`.

### 2.2 Siegel–Walfisz condition for the actual `alphaSeq` (`UremFamilySW.lean`)

The definition is

```
def IntervalSWAt (g : ℕ → ℝ) (N B0 : ℝ) (cSW : ℝ → ℝ) : Prop :=
  ∀ t d q a, 1 ≤ d → 1 ≤ q → Nat.Coprime a q → ∀ A, 1 < A →
    |∑ n ∈ simN N with n ≤ t, g n * swW d q a n| ≤ cSW A * N * tau d ^ B0 / Real.log N ^ A
```

Here `swW d q a n = 1_{n≡a (q), (n,d)=1} − φ(q)⁻¹ 1_{(n,dq)=1}`, so this is (6.1) on every initial
segment `(N, t]`.

Proved, all unconditional:

* `swCondition_iff_weight`: (6.1) is equivalent to its weight form.
* `swCondition_of_intervalSW`: interval SW implies (6.1).
* `intervalSW_trunc`: the truncation `1_{n ≤ z}` preserves interval SW. This is the truncated
  Möbius case.
* `abel_bound`: discrete partial summation, `|∑_{a<n≤b} c_n L_n| ≤ 2 E L(b)`.
* `swCondition_log_of_intervalSW`: **logarithmic normalisation.** Interval SW for `g` implies
  (6.1) for `g(n) log n / (1 + log 2N)` with constants `2c_A`.
* `alphaSeq_swCondition (z j e c) (hN : 2 ≤ alphaScale e c) (h1 : IntervalSWAt (roughOne z₀) N' b cSW)
  (hμ : IntervalSWAt (roughMu z₀) N' b cSW) : SWCondition (alphaSeq z z₀ j e c / alphaNorm e c) N' b (2·cSW)`,
  where `N' = alphaScale e c = 2^{e_c} − 1/2`. This covers every component: rough log (`c = 0`,
  normalised by `alphaNorm = 1 + log 2N'`), rough constant (`ζ`), rough truncated Möbius (`M_z`),
  and the unit `δ` (which vanishes on `n ∼ N'`). The constants are uniform in `z, j, e, c`.
* `alphaSeq_abs_le_tau`: `|alphaSeq / alphaNorm| ≤ 1 ≤ τ(n)^{B₀}`. This is the divisor-power
  coefficient bound of Lemma 13.8.

The **additional mask** `(n, r) = 1` is handled by the earlier `swCondition_masked`: masking
divides by `τ(r)^{B₀}`, using `τ(dr) ≤ τ(d)τ(r)`. `bdhEnergy_masked_le` multiplies the loss
`(τ(r)^{B₀})²` back in, and `actual_family_urem_explicit` pays for it with the reciprocal-divisor
moment `∑_r τ(r)^{b}/φ(r)` from §2.1.

### 2.3 Collapsing the family bound (`UremFamilyAggregate.lean`, `UremFamilyCell.lean`)

All of the following are unconditional except where marked:

* `packet_density_le`: `∑_ξ |Γ_ξ|(M/f_ξ + Q) ≤ C_a (1+log F)^{2^K} (M + F Q)`, assuming
  `1 ≤ f_ξ ≤ F` and multiplicity `≤ C_a τ(f)^K`.
* `atom_total_le`: `∑_{J,P,χ} w_{J,P} ≤ ∑_{J≤T²} H^J 3^J`.
* `actual_family_urem_explicit` (conditional on (1)): `actual_family_urem_maynard` with every
  sum evaluated. The bound is
  `(∑_J H^J3^J)(1+log K)^{2^{b+1}} n₀ √B_β √(C_a(1+log F)^{4^k}(M+F2^{n₀})) √(C_a C' N'²/(log N')^A)`.
* `physUrem_scale_left` and `physUrem_sum_right`: `physUrem` is linear in `α` and in `β`.
* `betaSeq_lt`, `betaSeq_eq_sum_dy`: the actual `β` is supported on `m < 2^E` with
  `E = betaTop e c = ∑_{i≠c}(e_i+1)+1`, and `β = ∑_{k<E} dy k β` exactly.
* `betaSeq_dy_sq_le`: the **actual `β` second moment**,
  `∑_{2^k ≤ m < 2^{k+1}} (dy k β)_m² ≤ (1+log 2M)^{10}·2M(1+log 2M)^{256}` with `M = 2^k`.
  It comes from `|β_m| ≤ (1+log m)^5 d_5(m)`, `d_5 ≤ τ^4` and §2.1.
* `cell_urem_bound` (conditional on (1) and (2)): the bound for one actual cell, with
  `α = alphaSeq`, `β = betaSeq`, the literal packets, and a sum over the dyadic `β` pieces.

### 2.4 The final bound (`UremFamilyFinal.lean`)

Both theorems are conditional on (1) and (2).

```
theorem cell_urem_polylog (hM : MaynardLemma13_8) (k₀ : ℕ) {b : ℕ} (hb : 2 * k₀ + 1 ≤ b)
    (cSW : ℝ → ℝ) {Astar η Wmax CaMax : ℝ} (hA : 0 < Astar) (hη : 0 < η) :
    ∃ C Cfin : ℝ, ∀ P, P.WGood → P.k ≤ k₀ → ∀ Bf, (∀ v i t, |P.fp v i t| ≤ Bf) →
    (P.V * Bf ^ P.k) ^ 2 * (P.k : ℝ) ^ 2 ≤ CaMax →
    ∀ Ξ, Ξ ⊆ P.XiAll → ∀ S, S.Good → (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) ≤ Wmax →
    ∀ δ N (K n n0 K' F : ℕ), K ≤ 2 ^ n → ∀ z z₀ j e c,
    4 * 2 ^ e c * 2 ^ betaTop e c ≤ K' → (∀ ξ ∈ Ξ, P.f ξ ≤ F) → (band cap l < 2^n0) →
    2 ≤ alphaScale e c →
    IntervalSWAt (roughOne z₀) (alphaScale e c) b cSW →
    IntervalSWAt (roughMu z₀) (alphaScale e c) b cSW →
    ((2 * F * 2 ^ n0 : ℕ) : ℝ) ≤ alphaScale e c / Real.log (alphaScale e c) ^ C →
    ∀ X : ℝ, 3 ≤ X → ((2 ^ e c * 2 ^ betaTop e c : ℕ) : ℝ) ≤ X → (K : ℝ) ≤ X → (F : ℝ) ≤ X →
    ((2 ^ n0 : ℕ) : ℝ) ≤ X → ((F * 2 ^ n0 : ℕ) : ℝ) ≤ ((2 ^ betaTop e c : ℕ) : ℝ) →
    η * Real.log X ≤ Real.log (alphaScale e c) →
    ∑ ξ ∈ Ξ, |physUrem S δ N (P.Gamma ξ) (P.f ξ) (P.cRes ξ) (P.A ξ) (P.B ξ) K K'
        (alphaSeq z z₀ j e c) (betaSeq z z₀ j e c)| ≤ Cfin * X / Real.log X ^ Astar
```

`C_fin` depends only on `k₀, b, c_A, A, η, Wmax, CaMax`. Internally the proof applies Maynard's
lemma with `A_Maynard = 2(136 + 2^{b+1} + 4^{k₀} + A)`.

`cells_urem_polylog` sums this over any set `𝒞` of cells `(j, e, c)` that satisfy the per-cell
conditions, giving the bound `|𝒞|·C_fin X/(log X)^A`. Also, `card_cellBox` gives
`|cellBox E₀| = 18 E₀^6`, so with `E₀ ≤ 2 log X` the total over all Heath–Brown cells is
`O(X/(log X)^{A−6})`.

## 3. Residual hypotheses of `cell_urem_polylog`

| Hypothesis | Kind | Status |
| --- | --- | --- |
| `MaynardLemma13_8` | published theorem (Maynard I, Lemma 13.8) | paper: published; Lean: not formalized |
| `IntervalSWAt (roughOne z₀)` and `IntervalSWAt (roughMu z₀)` at `N' = 2^{e_c}−1/2`, constants `c_A` fixed in advance | Siegel–Walfisz-type input | paper: §4; Lean: not formalized |
| `P.k ≤ k₀`, `b ≥ 2k₀+1`, `C_a ≤ CaMax`, `∑_J H^J3^J ≤ Wmax` | fixed data bounds | parameter |
| `K ≤ 2^n`, `4·2^{e_c}2^E ≤ K'`, `f_ξ ≤ F`, band cap `l < 2^{n₀}`, `N' ≥ 2` | structural | parameter (as in the earlier family theorems) |
| `2F2^{n₀} ≤ N'/(log N')^C` | Lemma 13.8 modulus range `q = fl < N/(log N)^C` | parameter |
| `F 2^{n₀} ≤ 2^E` | moduli are at most the length of `β` | parameter, **new**, see below |
| `2^{e_c}2^E ≤ X`; `K, F, 2^{n₀} ≤ X`; `X ≥ 3` | size (`MN ≤ X`) | parameter |
| `log N' ≥ η log X` | the critical (SW) variable is not short | parameter (routing) |

**Note on `F 2^{n₀} ≤ 2^E`.** The residue occupancy step (5.2) counts `M/(fl) + 1` values of `m`
per class. The `+1` term costs `F 2^{n₀}` against `M`. So this bound gives `O_A(X/(log X)^A)`
only when all moduli satisfy `q = f l ≤ min(M, N/(log N)^C)`, which forces `q ≤ X^{1/2}`. Whether
the actual routing of `physCell` / `physUrem` stays in this range (via `physCell_contract`:
`l ≤ N X^{−κ}`, and the base cap `F`) has **not** been checked here. This is the one structural
point that must be confirmed when the noncritical routing is written down. It is a parameter
condition, not a new analytic provider.

**`MN ≍ X`.** Only the upper bound `2^{e_c}·2^E ≤ X` is used. The lower bound is not needed for an
upper bound on the remainder.

**`z₀`.** The repository never fixes the cell roughness parameter `z₀` (`alphaSeq` is
parameterised by `z₀` and is not tied to `ScalarParams`). The theorem is uniform in `z₀`: the
only `z₀`-dependence is in hypothesis (2).

## 4. Paper-level status of input (2) and formal dependency statement

The Lean dependency is exactly `IntervalSWAt (roughOne z₀) N' b cSW ∧ IntervalSWAt (roughMu z₀) N' b cSW`
with constants `cSW` fixed before all parameters. The paper argument depends on the size of `z₀`:

* **Small roughness, `z₀ ≤ exp(c√log N)`.** For `q > (log N)^{A+2}` the trivial bound suffices.
  For smaller `q`, expand in characters mod `q`.
  * `μ·1_{(n,D)=1}` with `D = d·P(z₀)`: write `μχ1_{(·,D)=1} = (μχ) * (χ 1_{D^∞})`. Then apply the
    Siegel–Walfisz bound `∑_{n≤y} μ(n)χ(n) ≪_A y(log y)^{−A}` for `q ≤ (log y)^B` (a consequence of
    Siegel's theorem) when `y ≥ exp(√log N)`. Bound the remaining `m ∣ D^∞` with Rankin's trick.
    The factor `∏_{p∣d}(1−1/p)^{−1} ≤ d/φ(d) ≤ τ(d)` is exactly `nat_le_card_divisors_mul_totient`.
  * `1_{(n,dP(z₀))=1}`: use the fundamental lemma of sieve theory with level `N^{1/2}`. The
    residue-class count and the `φ(q)^{−1}`-average have the same main term
    `(t/q)∏_{p∣dP(z₀),p∤q}(1−1/p)`, and the errors are `O(N e^{−u} + N^{1/2+o(1)})` with
    `u ≥ √log N`.
* **Power roughness, `z₀ = N^δ`.** On `(N, 2N]` the sequences `1_{P^-≥z₀}` and `μ1_{P^-≥z₀}` are
  finite signed combinations of products of at most `1/δ` primes, each `≥ z₀`. Siegel–Walfisz for
  primes, together with the standard fact that the SW property is preserved under convolution with
  divisor-bounded sequences supported on `[z₀, ∞)`, gives (6.1) with `τ(d)^{B₀}` losses.

These are standard arguments, not reproduced in full here. The Siegel–Walfisz theorem itself
rests on Siegel's ineffective bound for exceptional zeros, which is not in Mathlib. Formalizing
it would be a separate large project. This is **paper-level use of published theorems**, not a
Lean proof.

**Maynard I, Lemma 13.8, match.** `MaynardLemma13_8` (previous run) transcribes Definition 1,
(6.1) and Lemma 13.8 of arXiv:2006.06572v2. The match is:

* the coefficient bound is `|α_n| ≤ τ(n)^{B₀}` (`alphaSeq_abs_le_tau`, after normalisation);
* the SW constants are uniform (`cSW` is fixed before `N`, `α` and `Q`, and `C`, `C'` depend only
  on `B₀, cSW, A`);
* the moduli are complete, `q = f l` with `q < N/(log N)^C` (`2F2^{n₀}` cutoff);
* the `τ(q)^{B₀}` weight absorbs the packet multiplicity `τ(f)^{2k}` via `energy_grouping` with
  `K = 2k ≤ b − 1`;
* the coefficient multiplicity `(τ(r)^{B₀})²` is paid by §2.1.

The statement uses a weaker quantifier order than the paper (`C` may depend on `cSW`), so it is
implied by the published lemma.

## 5. What this does and does not establish

* **Established (Lean, conditional on (1) and (2) plus parameter ranges):** the Urem term of
  every actual Heath–Brown cell is `O_A(X/(log X)^A)`, and summed over all cells it is
  `O_A(X/(log X)^{A−6})`.
* **Not established:** a Lean proof of (1) or (2); the check that the actual routing satisfies
  `fl ≤ min(M, N/(log N)^C)` and `log N ≥ η log X`; and the other Tail287 obligations.

## 6. Next critical item (not started in this run)

Since the Urem branch is now conditionally paid, the next item is the **critical Pascadi/W4 source
estimate**: the spectral/Kloosterman bound for the critical cells `physCell` beyond the
Bombieri–Vinogradov range, together with the corrected FCHS/W4 estimates on the actual atoms.
The noncritical routing, the base-only remainder with main-term normalisation, and the seven-block
framework also remain open. **`Tail287Statement` is not claimed.**
