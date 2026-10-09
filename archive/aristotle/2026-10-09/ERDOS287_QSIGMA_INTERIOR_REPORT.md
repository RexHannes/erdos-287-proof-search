# Erdős #287: exact source, the `Q_Σ` certificate, and the interior (hostile self-audit)

**Erdős #287 is not closed. The asymptotic interior is not closed. No explicit `M₀` was found.**
The interior finite splice is likewise not closed. The only finite range covered is the
kernel-checked range `M ≤ 4·10⁹` that the project already had, now connected to the exact source.

Outcome: **SUCCESS D (exact obstruction).** The obstruction is quantitative. Its Q_Σ half rests on a
heuristic, and its strip half is a paper argument. The formal results are listed below.

---

## 0. Scope and provenance (read first)

* The "V53–V54 / Astra audit" documents named in the request are **not in this repository**. The
  newest bank here is V30. So everything below was rebuilt from the definitions written out in the
  request.
* The exact source is formalised for an **arbitrary compulsory omission set `R`**. "Compulsory"
  means `R ∩ A = ∅` for the counterexample `A`. Any baseline that is proved compulsory plugs in
  directly.
* The logarithmic rough baseline `R_b = {n : P⁺(n) > M/(b log M)}` is **not** formalised, and
  its compulsoriness is **not** re-verified here. The project contains one compulsory baseline that
  is fully proved: the window baseline (`windowBaseline_compulsory`). It is the exact, computable
  version of `b ≈ 1`.
* **Audit caveat on `b = 1`.** The naive top-layer argument for `R_1` needs
  `lcm(K)·|K| < p` for every row `K ⊆ [a/p, M/p]` and every `p > M/log M`. At the edge `p ≈ M/log M`
  this amounts to `ψ(x) < x − O(log x)` with `x = log M`. Littlewood's oscillation theorem shows
  that inequality fails for infinitely many `x`. So `b = 1` needs the sharper audited argument,
  which is not in this repository. Every fixed `b < 1` is safe by the prime number theorem with an
  error term. The window baseline sidesteps the issue because its cutoff is defined exactly by
  `C(⌊M/p^e⌋) < p`.

---

## 1. Formal bank (Lean, no `sorry`, standard axioms only)

New files (nothing else was modified):

| File | Content |
|---|---|
| `RequestProject/Erdos287/QSigma/Source.lean` | `B`, `V`, `W`, `T` (in `ℤ`, no truncation), `tau`, `Indep`, `SourceSol`, `RT` |
| `RequestProject/Erdos287/QSigma/Carry.lean` | `eW`, `S`, `RepairSizes`, `kappa`, `Gamma`, `QSigma`; carry lemma, sum-of-depths valuation, **(DIV)** |
| `RequestProject/Erdos287/QSigma/Certificate.lean` | `Pmax`, `Pmass`, **(CERT)**, mass-sharpened CERT, `kappa_mono`, baseline transport |
| `RequestProject/Erdos287/QSigma/Audit.lean` | floor `W/gcd(W,|T|) ∣ Q_Σ`, ceiling `Q_Σ ∣ ∏_V n`, comparator sandwich |
| `RequestProject/Erdos287/QSigma/Bridge.lean` | literal adapter to `Erdos287Counterexample`, exact equivalence, window baseline, conditional terminal theorem |
| `RequestProject/Erdos287/QSigma/Splice.lean` | splice with the kernel-checked range `M ≤ 4·10⁹` |
| `RequestProject/Erdos287/QSigma.lean` | aggregator |

Theorems in namespace `Erdos287.ExactSource`. `E` is a solution of the exact source, and `0 < a` throughout:

* `tau_eq`: `τ = ∑_{n∈B} 1/n − 1`.
* `SourceSol.recip_eq_tau`: `∑_{n∈E} 1/n = τ`.
* `SourceSol.card_mul_W_le`, `SourceSol.card_le_RT`: `|E|·W ≤ M·T`, and `|E| ≤ R_T = ⌊MT/W⌋`.
* `card_inter_mem_RepairSizes`, `kappa_le_card_inter`: `E ∩ S_{p,d}` is a repair set, so `|E ∩ S_{p,d}| ≥ κ_{p,d}`.
* `no_solution_of_infeasible`: if some depth `d ≤ e` is infeasible (`κ = ∞`), there is no solution.
* `Gamma_le_factorization_prod`: `v_p(∏_E n) ≥ ∑_{d=1}^{e} κ_{p,d}`. This is the **sum** over depths, not the maximum.
* `QSigma_dvd_prod`: **(DIV)** `Q_Σ ∣ ∏_{n∈E} n`.
* `prod_le_Pmass`, `Pmass_le_Pmax`, `prod_le_Pmax`: `∏E ≤ P_mass(V,τ) ≤ P_max(V,R_T)`.
* `no_solution_of_QSigma_gt_Pmass`, `no_solution_of_QSigma_gt_Pmax`: **(CERT)** and its sharpened form.
* `kappa_mono`: `κ_{p,d} ≤ κ_{p,d+1}` whenever depth `d+1` is feasible.
* `one_le_kappa`, `denominator_dvd_QSigma`: each depth `d > v_p(T)` costs at least one repair, so `den τ ∣ Q_Σ`.
* `kappa_le_card_S`, `QSigma_dvd_prod_V`: the ceiling `Q_Σ ∣ ∏_{n∈V} n`, i.e. `log Q_Σ ≤ ∑_V log n`.
* `Pmax_le_pow`, `pow_le_Pmass`: `a^{|F|} ≤ P_mass` for every admissible `F`, and `P_max(V,k) ≤ M^k`.
* `tau_add_compulsory_mass`, `tau_transport`, `omissions_transport`: the exact baseline-transport law (§2E).
* `holes_isolated`, `sourceSol_of_counterexample`, `counterexample_of_sourceSol`: the literal source adapter in both directions. Endpoints are retained, nothing is double-charged, and the omission set is `E = B \ A`.
* `erdos287_iff_no_source`: the original statement holds **iff** no source `(a, M, R=∅)` with `1<a<M` has a solution.
* `windowBaseline_compulsory`: a proved compulsory baseline.
* `erdos287_of_universal_certificate`: **conditional**. GOAL for all `1<a<M` implies Erdős #287.
* `no_sourceSol_of_M_le_4e9`, `erdos287_of_universal_certificate_above_4e9`: **conditional**, with the finite range spliced in. GOAL is needed only for `M > 4·10⁹`.

Convention: `κ_{p,d}` is an `sInf` and takes the junk value `0` when the depth is infeasible.
This never affects soundness. Infeasibility already kills the source
(`no_solution_of_infeasible`), and whenever a solution exists every depth set is nonempty, so `κ` is
the true minimum.

---

## 2. Mathematics: the priority attacks

Notation: `λ = log(M/a)` and `q(λ) = 1 − e^{−λ}`. Primes are written on the scale
`p = M/(c log M)`.

### 2A. General-λ row entropy: PROVISIONAL (paper proof; asymptotic constants not effective)

*Row length.* The multiples `kp` of `p` in `[a, M]` have `k ∈ [a/p, M/p] = [c e^{−λ} log M, c log M]`.
So `L(c,λ) = (c q(λ) + o(1)) log M`. This is exact from the endpoints, and no `λ → 1` assumption is
used.

*Fingerprints.* Take `p > √M`. Then `e_p(W) = 1`, and the elements of `A` divisible by `p` are the whole
top layer. The top-layer congruence gives `p ∣ num(∑_{k∈K_p} 1/k)`, where `K_p` is the set of
selected cofactors. Also `num ≤ |K|·lcm[1, c log M] = M^{c+o(1)}` (prime number theorem). So any one
nonempty pattern `K` serves at most `c + o(1)` primes of the strip.

The number of patterns with deletion proportion `≤ θ ≤ 1/2` is at most `exp(L h(θ))`, where `h` is
binary entropy in nats. On a thin strip `[M/(c(1+η) log M), M/(c log M)]`, therefore, the number of
primes with a nonempty row of deletion proportion `< θ` is at most `M^{c q(λ) h(θ) + o(1)}`.

**Dichotomy.** If `c q(λ) h(θ) < 1`, all but `o(M/log² M)` primes of the strip have a row that
is empty or has deletion proportion `≥ θ`. If `c q(λ) log 2 < 1`, almost every row is completely
omitted. At `λ = 1` this gives back the Astra threshold `c_* = 1/((1−e^{−1}) log 2)`.

Define `θ_*(c,λ)` by `c q(λ) h(θ_*) = 1`. It is the critical deletion proportion for
`c ≥ c_λ := 1/(q(λ) log 2)`.

The minimum omitted reciprocal mass of a row with deletion proportion `θ` is attained by deleting
the largest cofactors:
`μ(θ,λ)/p` with `μ(θ,λ) = −log(1 − θ q(λ))`, and `μ(1,λ) = λ` for a fully omitted row.

### 2B. Multi-strip accumulation: PROVISIONAL (paper proof)

Rows of distinct primes `> √M` are disjoint, and multiples of `p ≤ Y_b` are never `b`-rough. So
every charge below is an optional omission, and nothing is double-charged. Summing over the strips
with Mertens' estimate `∑_{x<p≤y} 1/p = log(log y/log x) + O(1/log x)` gives:

**Theorem (paper).** For fixed `0 < b ≤ 1` and `δ > 0`, every large candidate satisfies

    τ_b ≥ (F_b(λ) − δ)/log M,   F_b(λ) = λ log(c_λ/b) + I(λ),
    I(λ) = ∫_{c_λ}^{∞} −log(1 − θ_*(c,λ) q(λ)) dc/c   (convergent: θ_* ~ 1/(c q log c)).

The integral was evaluated numerically (midpoint rule). This is not a verified computation:

| λ | c_λ | λ log c_λ | I(λ) | F_1(λ) |
|---|---|---|---|---|
| 1.00 | 2.2823 | 0.8252 | 0.1556 | 0.9808 |
| 1.25 | 2.0220 | 0.8801 | 0.1772 | 1.0573 |
| 1.50 | 1.8571 | 0.9285 | 0.1944 | 1.1229 |
| 2.00 | 1.6685 | 1.0239 | 0.2186 | 1.2424 |

At `λ = 1`, `F_1(1) = β_* + I(1)`. This *includes* the banked `β_* = 0.8252` and adds the
partial-deletion term. I did not spend effort optimising it further, as instructed.

**Translation to λ.** The rough mass is
`ρ_b = [λ(log log M + log b + γ) − λ²/2 + o(1)]/log M`. This comes from splitting
`∑_k (1/k)∑_{p∈(max(Y_b,a/k), M/k]} 1/p` at `k = a/Y_b`. Also `τ_b = λ − 1 − ρ_b + O(1/a)`.
Hence the paper theorem eliminates the corridor

    (λ − 1) log M < λ log log M + K(λ) − δ,   K(λ) = λγ − λ²/2 + λ log c_λ + I(λ),

**independently of `b`**. The gap-two half-omission bound gives `λ ≤ 2 + o(1)` (already in the
project as `M ≤ e²(N+1)`). So the remaining interior is

    1 + (log log M + O(1))/log M  <  λ  ≤  2 + o(1).

**Obstruction for Attacks A and B (paper argument).** Every row and strip charge comes from primes
with `c = O(1)`, i.e. `p ≍ M/log M`. On that range `∑ 1/p ≍ 1/log M`. For `p ≤ M^{1−ε}` the rows
have length `≥ M^{ε}`, and the fingerprint count exceeds the prime count once `θ ≥ θ_* ≈ 1/(c log c)`.
So the total forced optional mass the method can ever produce is at most `F_b(λ)/log M = O(1/log M)`.
The interior has `τ ≍ λ − 1`, which is far larger than `log log M/log M`. **No strip
accumulation, however refined, can close the interior.**

### 2C. Deeper `p`-adic amplification: rigorous floor; usefulness PROVISIONAL-negative

* Rigorous (Lean, `denominator_dvd_QSigma`): `Γ_p ≥ e_p − min(e_p, v_p(T))`, hence `den(τ) ∣ Q_Σ`.
  By `kappa_mono`, depth costs are monotone.
* Digit analysis (paper). Fix `p ≤ √M`. The `j`-th `p`-adic digit of the target is moved only by
  elements of exact valuation `e − j`. Whenever `p^{e−j+1} ≤ M − a − 2`, those elements run through
  `≥ p` consecutive cofactors and so cover every unit residue. Such a digit costs at most one
  repair, and carries only move upward.
  * By maximality of `e`, digit `0` (the top layer) is always "short": it has `< p + 1` elements.
  * So `κ_{p,d} ≤ t_p + d`, where `t_p ≤ (M−a)/p^e + 1 ≤ p + 1`, provided the top digit is feasible.
  * The total contribution of `p ≤ √M` is then `∑_p (e t_p + e²) log p = O(M)`.
  * **This range cannot supply the `M log M` scale that the interior needs.**

### 2D. Sharpened product bound: rigorous sandwich; RETIRED as a closure lever

* `P_mass` is formalised, with `∏E ≤ P_mass ≤ P_max(V,R_T)` (Lean).
* `pow_le_Pmass` (Lean) gives `log P_mass ≥ |F| log a` for every independent `F ⊆ V` with
  `∑_F 1/n ≤ τ`.
* Taking `F` to be every other admissible integer down from `M` (the rough set has density `o(1)`)
  gives `|F| = (M/2)(1 − e^{−2τ})(1 − o(1))`. Hence
  `log P_mass ≥ (1−o(1)) (M/2)(1−e^{−2τ}) log M`.
* Combined with `P_max ≤ M^{R_T}` (Lean, `Pmax_le_pow`), the sharpening gains only a factor
  bounded in terms of `τ`, i.e. a constant in the interior. **There is no order-of-magnitude gain.**

### 2E. Baseline transport: BANK (exact law in Lean) + RETIRED (b-optimisation)

* Exact (Lean, `tau_add_compulsory_mass`): `τ_R + ∑_{r∈R} 1/r = H(a,M) − 1` for every
  compulsory `R ⊆ [a,M]`.
* Exact (Lean, `tau_transport`): for `R₁ ⊆ R₂`,
  `τ_{R₁} − τ_{R₂} = ∑_{R₂\R₁} 1/r`.
* Exact (Lean, `omissions_transport`): the omission set relative to `R₁` is that relative to `R₂`
  plus `R₂ \ R₁`, disjointly.
* Paper, for every λ (not only λ = 1):
  * Moving from `b₁` to `b₂` changes `τ` by `(λ log(b₁/b₂) + o(1))/log M`.
  * It changes the boundary threshold `F_b(λ)` by exactly `λ log(b₁/b₂)`.
  * The `b`-dependence therefore cancels to first order. **Answer (B): varying `b` only
    reclassifies the same reciprocal mass.** Stop optimising `b`.

---

## 3. The global ledger: the earliest failed inequality

The requested ledger compares `LHS = log Q_Σ` with `RHS = log P_sharp`.

* **RHS lower bound (rigorous given the admissible `F` above).**
  `log P_mass ≥ (1−o(1)) (M/2)(1−e^{−2τ}) log M`. This is `≍ τ M log M` in the interior.
* **LHS upper bound.**
  * Rigorous: `log Q_Σ ≤ ∑_{n∈V} log n`. This is not enough to decide the question.
  * Heuristic (random-residue model for the targets `T mod p^d`). `κ_{p,1} ≈ θ_*(c_p) L_p` for
    `p > √M`, and `O(e)` per prime for `p ≤ √M` (§2C). So
    `log Q_Σ ≈ (M − a) ∫ θ_*(c) dc/c + O(M) = O_λ(M)`.

**Earliest failed inequality: GOAL itself, `log Q_Σ > log P_sharp`, as soon as
`τ log M → ∞`.** Under the model, LHS is `O(M)` and RHS is `≍ τ M log M`. GOAL can therefore hold
only when `τ = O(1/log M)`, which is exactly the boundary regime already banked. Throughout the
interior it is expected to fail by a factor `≍ τ log M`.

*Exploratory, unverified illustration* (Python, `R = ∅`, exact `κ` computed by DP, all depths
feasible). This is **not** a Lean-verified computation and is **not** offered as evidence of
anything beyond the trend:

| (a, M) | λ | τ | log Q_Σ | log of a greedy admissible `F` (mass ≤ τ) |
|---|---|---|---|---|
| (80, 400) | 1.61 | 0.617 | 710 | 776 |
| (323, 1600) | 1.60 | 0.602 | 3173 | 3854 |
| (646, 3200) | 1.60 | 0.601 | 6616 | 8491 |
| (963, 3200) | 1.20 | 0.202 | 6147 | 4178 |

`log Q_Σ / M` stays near `2`, while the comparator grows like `log M`. On the λ ≈ 1.6 rows, if
these numbers are right, `Q_Σ ≤ P_mass` already holds, even though no solution exists (none exists
for `M ≤ 4·10⁹`).

**Minimum-damage repair (for the next run, same owner).** `Q_Σ` counts each prime's obligations
separately, and its generic size is `O(M)`. The interior candidate set `E` has `|E| ≍ τ M`, so its
product has size `≍ τ M log M`. Closing the gap requires a lower bound on `∑_{p,d} κ_{p,d} log p`
of order `M log M`. Equivalently, one must prove that the actual targets `T mod p^d` are
*atypically* expensive for a positive proportion (in `log p/p` weight) of primes `p ≤ M^{1−ε}`.

* No such mechanism is known.
* The only primes for which large `κ` is forced are `p ≍ M/log M`, and those carry total weight
  `O(M)`.
* The honest owner statement is therefore: **prove `κ_{p,1} ≥ ϑ L_p` for a positive-weight set of
  primes `p ∈ [M^{1−ε}, M/log M]`**, or give an exact construction showing it fails.

I did not rename the owner.

---

## 4. Effectivity and finite splice

* Every constant in §2A–2B uses the prime number theorem, Mertens and `ψ(x) ~ x` only through
  `o(1)` terms. Explicit versions exist (Rosser–Schoenfeld type bounds), but no `M₀` was extracted:
  **explicit M₀: OPEN.**
* Finite range: `no_Erdos287Counterexample_of_max_le_4e9` (already in the project, kernel-checked)
  is now spliced into the exact source by `no_sourceSol_of_M_le_4e9` and
  `erdos287_of_universal_certificate_above_4e9`. Any future interior proof needs only
  `M > 4·10⁹`. The interior itself is open, so the splice is not closed.
* The rough baseline only becomes a small perturbation once `λ log log M/log M` is small. So
  effective versions of §2B will need `M` far beyond `4·10⁹`. That gap is itself open.

---

## 5. Final ledger

| Object | Status | Exact theorem / obstruction |
|---|---|---|
| V53 exact source | BANK | `SourceSol`, `sourceSol_of_counterexample`, `counterexample_of_sourceSol`, `erdos287_iff_no_source` (general compulsory `R`; the rough `R_b` itself is not formalised) |
| full carry automata | BANK | `S`, `RepairSizes`, `kappa`, `card_inter_mem_RepairSizes`, `no_solution_of_infeasible`, `kappa_mono` |
| Q_Sigma divisibility | BANK | `Gamma_le_factorization_prod` (sum of depths), `QSigma_dvd_prod` |
| product exclusion | BANK | `no_solution_of_QSigma_gt_Pmax`, `no_solution_of_QSigma_gt_Pmass` |
| audited beta_b boundary theorem | PROVISIONAL | not in this repository; reproduced on paper as the `λ=1` case of §2B (`F_b(1) ≥ β_b`); `b=1` caveat in §0 |
| general lambda-row entropy | PROVISIONAL | §2A dichotomy `c q(λ) h(θ) < 1`; paper proof, not effective |
| multi-strip accumulation | PROVISIONAL | §2B: `τ_b ≥ (λ log(c_λ/b) + I(λ) − δ)/log M`; eliminates `(λ−1) log M < λ log log M + K(λ) − δ`; ceiling `O(1/log M)` |
| deeper p-adic amplification | STRICT REDUCE | floor `denominator_dvd_QSigma` (Lean); range `p ≤ √M` contributes only `O(M)` (paper, §2C) |
| sharpened product upper bound | RETIRED | `Pmass` formalised (`prod_le_Pmass`, `Pmass_le_Pmax`, `pow_le_Pmass`); gain only a factor bounded in terms of `τ` |
| baseline-b transport | BANK | `tau_add_compulsory_mass`, `tau_transport`, `omissions_transport`; b-optimisation RETIRED (first-order cancellation, §2E) |
| full interior domination | OPEN | GOAL is expected to fail once `τ log M → ∞` (heuristic, §3); conditional theorems `erdos287_of_universal_certificate(_above_4e9)` |
| explicit M_0 | OPEN | none extracted |
| finite splice | OPEN | `M ≤ 4·10⁹` is closed and spliced (`no_sourceSol_of_M_le_4e9`); the interior range is open |
| original Erdős #287 | OPEN | only conditional implications are proved |
