# V12 CONTROLLING CORRECTION

The previous V11 expectation that a fixed Ford certificate would reduce the leakage census to H8/H9 + QK56
is withdrawn.  The new first task is to verify the explicit fixed certificate and extract the exact smooth
Möbius-parity packet.  Do not blind-attack H8/H9 as the controlling first open.

# ERDOS 287 — ARISTOTLE V12 GOLD REPROOF / LEANIFY RUN

Work only on the new finite/compiler and Kummer-backend claims introduced in **ERDOS287_STANDALONE_VERIFICATION_DOSSIER_V12** and the existing Erdős-287 project bank.

This is an **append-only hostile reproof and Leanification run**. It is not a request to assume the new analytic claims. Do not add axioms, `sorry`, `admit`, opaque theorem placeholders, or hypotheses that simply restate the desired conclusion.

## AUTHORITIES AND FIREWALL

1. The existing Erdős-287 Lean project is authoritative for pre-existing finite theorems and definitions.
2. `ERDOS287_STANDALONE_VERIFICATION_DOSSIER_V12.tex/pdf` is authoritative only for the **new candidate statements** to be checked.
3. The Gold Closure Attempt supplied with V12 is research input, not a formal theorem source.
4. If V12 and the Lean bank disagree, the Lean bank controls.
5. Preserve all historical files. Add new files only.
6. Distinguish rigorously between:
   - finite / algebraic statements that can be kernel-checked now;
   - asymptotic real-analysis statements that Mathlib can prove without new axioms;
   - classical external analytic inputs such as Weil bounds or interval-completion bounds;
   - literal Gate-1B source-transcription obligations;
   - genuinely open analytic estimates.
7. A compiler conditional on an explicitly named external theorem is acceptable. An axiom pretending to inhabit that external theorem is not.

---

# A. EXACT ARCHAEOLOGY OF THE LOG-COFACTOR INTERFACE

Locate and print the exact Lean declarations, namespaces, types and statements corresponding to:

- `Gap2CE`;
- `N`, `M`;
- the theorem `N <= floor(M/2)` or its exact banked equivalent;
- `WindowPairSupply`;
- `LCBeta` and every current variant;
- `logCofactor_finite_blocker`;
- `C(j)`;
- the banked upper bound corresponding mathematically to `C(j) <= j * j!`;
- any existing `PlacedLCBeta`-like or upper-half placement predicate;
- any theorem already repairing the missing lower placement.

Before editing anything, print an exact source map:

```text
OBJECT:
LEAN NAME:
FILE:
LITERAL STATEMENT:
USED BY:
STATUS:
```

## A1. Hostile check of current `LCBeta`

The V12 claim is that the current abstract `LCBeta(M,J)` records `x+1 <= M` but not enough information to derive `N <= x`.

Determine literally whether that is true.

Return exactly one:

- `LCBETA_PLACEMENT_ALREADY_PRESENT`
- `LCBETA_PLACEMENT_MISSING`
- `LCBETA_DIFFERENT_FROM_V12_DESCRIPTION`

If missing, do **not** mutate the historical predicate. Define the weakest append-only repaired predicate, preferably one of:

```text
PlacedLCBeta ce J
```

or

```text
UpperHalfLCBeta ce J
```

whose witness includes at least

```text
ce.M <= 2*x
x + 1 <= ce.M
```

and the existing prime-factor conditions.

Prove from the exact banked half-range theorem that

```text
ce.M <= 2*x  ->  ce.N <= x.
```

Then prove an append-only compiler from the repaired predicate to the existing finite blocker.

Do not call the repaired theorem `PASS` unless it compiles in the actual project.

---

# B. LOG-COFACTOR ASYMPTOTIC287

The mathematical claim to reprove is:

For fixed real `eta` with `0 < eta < 1/2`, define

```text
J(M) = floor(eta * log M / log(log M)).
```

Assume the banked finite threshold satisfies

```text
C(j) <= j * j!.
```

Then for all sufficiently large `M`, every prime `q` satisfying

```text
M <= 2 * J(M) * q
```

also satisfies

```text
q^2 > M
q > C(2 * J(M)).
```

## B1. Formalization strategy

Attempt the strongest honest Lean theorem that the current Mathlib analysis library supports.

Preferred theorem shape:

```lean
theorem logCofactor_asymptotic287
    (eta : ℝ) (heta0 : 0 < eta) (heta : eta < 1/2) :
    ∃ M0 : ℕ, ∀ M >= M0, ...
```

with exact casts and exact definition of `J`.

Required proof ingredients must be explicit:

- `J(M) = O(log M / log log M)`;
- `log((2J)!) <= 2J * log(2J)` or a stronger existing factorial estimate;
- `log C(2J) <= (2 eta + o(1)) log M` or an explicit epsilon version;
- comparison with `M/(2J)`;
- `M/(2J) > sqrt M` eventually.

If a full asymptotic theorem is impractical in Mathlib, **do not insert an axiom**. Instead:

1. prove every finite inequality and monotonicity step available;
2. isolate the smallest standard real-analysis asymptotic lemma that is missing;
3. return the exact missing lemma in mathematical notation;
4. prove the final compiler conditional on that lemma.

Return one:

- `LOG_COFACTOR_ASYMPTOTIC287_KERNEL_PASS`
- `LOG_COFACTOR_ASYMPTOTIC287_COMPILER_PASS_EXTERNAL_ASYMPTOTIC`
- `LOG_COFACTOR_ASYMPTOTIC287_FAIL`

---

# C. FIXED-CERTIFICATE TRANSFERENCE287

This part should be formalizable as pure finite/order algebra and is a priority.

Create a generic finite theorem independent of the detailed Ford–Maynard implementation.

Let finite sets / predicates partition the scale into:

- `P` — prime/certificate-positive region;
- `N` — good composite region;
- `U` — leakage region, the complement inside the dyadic support.

Let real-valued functions `a b w H` satisfy

```text
w = a - b
0 <= a n
H p = 1             for p in P
H n <= 0            for n in N
```

Define

```text
B = sum_{p in P} b p
Leakage = sum_{n in U} w n * H n
Total = sum_{n in support} w n * H n
```

Assume exact finite inequalities/equalities corresponding to

```text
|Total| <= E
|Leakage| <= E
sum_{n in N} b n * H n >= C * B - E
1 + C > 0
```

(or the closest exact inequality formulation avoiding asymptotic notation).

Prove an explicit lower bound of the form

```text
sum_{p in P} a p >= (1 + C) * B - O(E).
```

Then provide a version specialized to `E <= delta * B` giving a strictly positive lower bound whenever

```text
delta < (1 + C)/constant.
```

The formal theorem should make the logic of V12 Theorem `Fixed-certificate transference` kernel-checkable without importing Ford–Maynard.

Suggested new file:

```text
RequestProject/Erdos287/FixedCertificateTransference.lean
```

Return exact theorem names and `#print axioms` output.

Target verdict:

`FIXED_CERTIFICATE_TRANSFERENCE287_KERNEL_PASS`

---

# D. QUADRATIC-KUMMER BACKEND: SEPARATE ALGEBRA FROM WEIL

Do **not** pretend Mathlib proves a new Weil bound if it does not.

The candidate analytic theorem is:

For odd prime `p`, quadratic character `chi`, a degree-two polynomial `F` with nonzero discriminant, interval-supported coefficients `alpha_m`, `beta_n`, and `N < p`,

```text
|sum_{m,n} alpha_m beta_n chi(F(m*n))|^2
  <= p^o(1) * ||alpha||_2^2 * ||beta||_2^2
     * [ M + (M/sqrt(p) + sqrt(p))*N ].
```

The research proof has three logically different layers. Formalize them separately.

## D1. Finite Cauchy / correlation compiler

Prove a completely finite theorem:

If a kernel `K(m,n)` has correlations satisfying

- for each `n1`, at most `s` values of `n2` are exceptional;
- exceptional correlations are bounded by `M`;
- all other correlations are bounded by `R`;

then

```text
|sum alpha_m beta_n K(m,n)|^2
 <= ||alpha||_2^2 ||beta||_2^2 * (s*M + R*N)
```

up to the exact constants required by the proof.

This should be kernel-checked without any number theory.

Suggested theorem name:

```text
kummer_bilinear_of_correlation_bounds
```

## D2. Root-stabilizer algebra

Hostile-check the claim:

For a squarefree quadratic polynomial `F` and nonzero `n1,n2 mod p`, the product

```text
F(n1*X) * F(n2*X)
```

can be a square polynomial only when multiplication by `n2/n1` preserves the unordered pair of roots of `F`; the stabilizer has cardinality at most two.

Attempt to formalize this in the weakest technically reasonable setting.

Important:

- handle the irreducible quadratic case correctly, e.g. via an algebraic closure / splitting field or a coefficient criterion;
- do not silently assume the two roots lie in `ZMod p`;
- exclude `n1 = 0` or `n2 = 0` modulo `p` explicitly;
- distinguish repeated-root (`disc F = 0`) from the generic squarefree case.

If the splitting-field formalization is prohibitively heavy, return the exact algebraic lemma as the formal boundary and prove the rest conditional on it.

## D3. Weil / completion input

Search the actual Mathlib/project for a theorem strong enough to give the incomplete correlation bound

```text
|sum_{m in interval} chi(F(n1*m) * F(n2*m))|
  <= C * (M/sqrt(p) + sqrt(p)) * polylog(p)
```

for nonexceptional pairs.

If no such theorem exists, do not axiomatize it. Define a local explicit interface structure / theorem parameter, e.g.

```text
QuadraticKummerCorrelationBound
```

and prove the bilinear theorem from that interface plus D1/D2.

Return exactly:

- `WEIL_INPUT_FOUND_IN_LIBRARY`
- or `WEIL_INPUT_EXTERNAL_INTERFACE_REQUIRED`.

---

# E. SEVEN-PRIME 5|2 SPECIALIZATION AND EXPONENT LEDGER

Formalize the deterministic exponent specialization from the generic bilinear bound.

Use variables corresponding to

```text
M = Y^5
N = Y^2
Y^(5/2 - o(1)) <= p <= Y^8
X = Y^9.
```

At minimum prove the rational-exponent inequalities underlying

```text
( Y^-2 + p^-1/2 + p^1/2 * Y^-5 )^1/2
    <= Y^-1/2+o(1)
```

at the two controlling endpoint exponents for `p`.

Prefer an exponent-ledger theorem using rational exponent variables rather than trying to formalize every `X^{o(1)}` symbol.

The deterministic conclusion should certify the fixed-power margin

```text
Y^-1/2 = X^-1/18.
```

Suggested file:

```text
RequestProject/Erdos287/KummerExponentLedger.lean
```

No PASS unless all rational inequalities compile.

---

# F. DEGENERACY ROUTERS

Locate the current H8/H9 / affine audit definitions for:

- repeated-root / discriminant-zero sector;
- isolated pure multiplicative-character mode;
- principal / zero mode;
- nonunit, repeated-prime, collision or conductor-loss strata.

Do not assert these are negligible from prose.

For each one print:

```text
ROUTER:
EXACT CONDITION:
DIMENSION/VARIABLE LOSS:
TARGET THEOREM:
LEAN STATUS:
ANALYTIC INPUT STILL NEEDED:
```

Where possible, prove append-only finite routing lemmas showing that generic packets are disjoint from all degeneracy strata.

---

# G. EXPLICIT FIXED CERTIFICATE + SMOOTH-PARITY CENSUS — NEW CONTROLLING TASK

The V12 correction supersedes the earlier expectation that the fixed-certificate leakage census will immediately reduce to H8/H9 + QK56.

## G1. Pin the literal Ford certificate

Locate or formalize data corresponding to the explicit Ford certificate:
- central parameter `nu0 = 0.16623` (represent rationally if exact source data permit; otherwise keep the numerical/source statement external);
- `g0(empty)=1`;
- one-variable branch `-1_{x <= 1/2}`;
- two-variable branch supported on `(1-nu0)/2 < x1+x2 < 1/2`;
- three-variable branch `-1_{x1+x2+x3 <= 1/2}`;
- the fixed small shrink `gStar`.

Do NOT invent an effective decimal epsilon if the source only proves existence through `CStar = C0 + O(eps)`.

Required status:
`FIXED_CERTIFICATE287_PIN = SOURCE/PUBLISHED PASS`
only if the literal source statement is pinned.

## G2. Formalize the finite arithmetic weight interface

Define an abstract finite version of
`HStar(n) = sum_{d|n} GStar(d;n)` with:
- prime normalization `HStar(p)=1`;
- a named main-composite region `N1` with sign `HStar(n) <= 0`;
- a separate exceptional region `N2`.

Kernel-check the transference theorem with THREE distinct errors:
1. total correlation;
2. leakage outside `P ∪ N1 ∪ N2`;
3. the `N2` error.

Do not merge `N2` into the sign region.

Also formalize the constant-saving variant:
if `|leakage| + |N2Error|` is less than a fixed fraction of the positive certificate margin, positivity follows.
Arbitrary-log saving is sufficient but not logically required.

## G3. Extract the exact smooth-parity packet

Hostile goal: prove that the cell `k=0`, `J=empty` produces the finite identity corresponding to
`HStar(n) = sum_{d|n, d <= n^(1/2-eps)} mu(d)`
on the smooth-prime-factor sector.

Do NOT merely assert this from prose. Recover the actual predicates/splits from the project if they exist.
If the relevant Ford factorisation is not encoded, report the exact missing source theorem.

Create a named interface:
`FixedCertificateSmoothParityPacket`

and status label:
`ERDOS287_FIXED_CERTIFICATE_SMOOTH_PARITY45`.

This is the current FIRST LITERAL ANALYTIC OPEN unless the run genuinely proves a provider.

## G4. Kernel-check the H8/H9-only counterguard

Formalize the binomial identity
`sum_{j=0}^r (-1)^j * choose k j = (-1)^r * choose (k-1) r`
for `r < k`.

Build a finite balanced-cell abstraction showing that, under the threshold assumptions, the truncated Möbius divisor weight can be nonzero for arbitrary larger defect order `k`.

At minimum instantiate/check k = 7,8,9,10,11,12 with the claimed coefficients when the chosen rational gamma range makes the same r-values valid.

Required verdict:
`FINITE_H8_H9_ONLY_CENSUS = FAIL`
if the counterguard compiles.

Do NOT allow any theorem named `FullNine` to imply exhaustiveness by nomenclature.

# H. QUADRATIC-KUMMER BACKEND — CHILD PROVIDER ONLY

Retain the V11 Kummer finite compiler / root-stabilizer / exponent ledger tasks, but change the interpretation:

- `SEVENPRIME_KUMMER` may be `CONDITIONAL ANALYTIC CHILD PASS`;
- it MUST NOT imply fixed leakage closure;
- `H8H9-SOURCE-TO-KUMMER45` remains an open child/source interface;
- it is not the first literal fixed-certificate open once the smooth-parity packet is verified.

# I. FIXED-CERTIFICATE LEAKAGE PARENT

Define the parent leakage interface as the sum of:
- the smooth-parity packet;
- every other literal fixed-gStar packet.

The formal compiler may prove:
`all child bounds + total correlation + N2 bound + comparison margin -> positive affine prime mass`.

But keep the parent analytic theorem
`287-FIXED-CERTIFICATE-LEAKAGE45`
OPEN unless every child is actually bounded.

Required controlling status after a conservative successful run:

```text
FIXED-CERTIFICATE287-PIN:
[SOURCE/PUBLISHED PASS / BLOCKED]

FIXED-CERTIFICATE-TRANSFERENCE287:
[KERNEL PASS / FAIL]

FINITE-H8/H9-ONLY-CENSUS:
[FAIL EXPECTED / UNRESOLVED]

287-FIXED-CERTIFICATE-SMOOTH-PARITY45:
[FIRST ANALYTIC OPEN unless genuinely solved]

SEVENPRIME-KUMMER:
[CONDITIONAL CHILD PASS / FORMAL BOUNDARY / FAIL]

H8H9-SOURCE-TO-KUMMER45:
[PASS / SOURCE BLOCKED / FAIL]

287-FIXED-CERTIFICATE-LEAKAGE45:
[OPEN unless all fixed-gStar packets are controlled]

ERDOS287:
OPEN
```

# J. OPTIONAL ROUTE FIREWALL

The fixed-certificate route removes the need for a theorem uniform over all Ford certificates, but the new smooth-parity counterguard shows that one must NOT claim the analytic content has collapsed to H8/H9/QK56.

Keep the following as valid sufficient alternatives:
- universal `FullFMTypeII_1/6`;
- the generated Ford equation-(7.23) route;
- `SOURCE-ADAPTER45`;
- the global replacement certificate `C_FM`.

A fixed-gStar specialization of the generated route may still be needed to control the smooth small-prime packets. Therefore document only:

```text
fixed-certificate leakage route is a logically sufficient alternative wrapper
```

and explicitly forbid the stronger claim:

```text
fixed-certificate route is analytically shorter
```

unless a source-exhaustive packet theorem actually proves it.

---

# K. APPEND-ONLY FILE PLAN

Prefer new files such as:

```text
RequestProject/Erdos287/PlacedLCBeta.lean
RequestProject/Erdos287/LogCofactorAsymptotic.lean
RequestProject/Erdos287/FixedCertificateTransference.lean
RequestProject/Erdos287/FixedCertificateSmoothParity.lean
RequestProject/Erdos287/FixedCertificateOrderCounterguard.lean
RequestProject/Erdos287/KummerFiniteCompiler.lean
RequestProject/Erdos287/KummerExponentLedger.lean
RequestProject/Erdos287/FixedCertificateLeakageCompiler.lean
RequestProject/Status/Erdos287GoldV12Status.lean
```

Use existing project naming/import conventions if different.

Do not overwrite old theorem statements merely to make the new route compile.

---

# L. FULL BUILD / AXIOM AUDIT

Run the complete relevant project build.

For every new theorem report:

```text
THEOREM:
FILE:
COMPILES:
#print axioms:
USES EXTERNAL INTERFACE:
ROLE:
```

Search the new files for:

```text
sorry
admit
axiom
opaque
```

and explain any occurrence. User-introduced axioms are forbidden.

---

# M. FINAL LEDGER

Return exactly this ledger:

```text
LCBETA PLACEMENT:
[PASS / REPAIRED / FAIL]

LOG-COFACTOR-ASYMPTOTIC287:
[KERNEL PASS / COMPILER PASS WITH EXTERNAL ASYMPTOTIC / FAIL]

FIXED-CERTIFICATE287-PIN:
[SOURCE/PUBLISHED PASS / SOURCE BLOCKED / FAIL]

FIXED-CERTIFICATE-TRANSFERENCE287:
[KERNEL PASS / FAIL]

FIXED-CERTIFICATE-SMOOTH-PARITY PACKET:
[KERNEL/SOURCE PASS / SOURCE BLOCKED / FAIL]

FINITE-H8/H9-ONLY-CENSUS:
[FAIL EXPECTED IF COUNTERGUARD COMPILES / UNRESOLVED]

HIGH-ORDER COUNTERGUARD:
[KERNEL PASS / PARTIAL / FAIL]

QUADRATIC-KUMMER FINITE COMPILER:
[KERNEL PASS / FAIL]

ROOT-STABILIZER ALGEBRA:
[KERNEL PASS / FORMAL BOUNDARY / FAIL]

WEIL / INTERVAL COMPLETION:
[LIBRARY PASS / EXTERNAL INTERFACE]

SEVEN-PRIME EXPONENT LEDGER:
[KERNEL PASS / FAIL]

KUMMER DEGENERACY ROUTERS:
[PASS / PARTIAL / SOURCE BLOCKED / FAIL]

SEVENPRIME-KUMMER:
[CONDITIONAL CHILD PASS / FORMAL BOUNDARY / FAIL]

H8H9-SOURCE-TO-KUMMER45:
[PASS / PASS WITH REPAIRS / SOURCE BLOCKED / FAIL]

287-FIXED-CERTIFICATE-SMOOTH-PARITY45 ANALYTIC ESTIMATE:
[OPEN unless genuinely proved]

FIXED-CERTIFICATE LEAKAGE COMPILER:
[KERNEL PASS / PARTIAL / SOURCE BLOCKED / FAIL]

287-FIXED-CERTIFICATE-LEAKAGE45 ANALYTIC ESTIMATE:
[OPEN unless every literal fixed-gStar child is controlled]

GENERATED-(7.23) FIXED-gStar SPECIALIZATION:
[OPTIONAL SUFFICIENT / MAY STILL BE NEEDED / NOT AUDITED]

ERDOS287:
OPEN
```

Then print:

```text
EXACT FIRST OPEN AFTER THIS RUN:
[default expected answer: 287-FIXED-CERTIFICATE-SMOOTH-PARITY45,
 unless this run genuinely proves that analytic estimate]

NEXT MATHEMATICAL ACTION:
[exactly one theorem/source attack on that first open; do not default to H8/H9]
```

Do not end with `ERDOS287_SOLVED` unless every analytic and effective antecedent is actually proved and the finite remainder is certified. The expected conservative terminal status of this run is still `ERDOS287 OPEN`.
