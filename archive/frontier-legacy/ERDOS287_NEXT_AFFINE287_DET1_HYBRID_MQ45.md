# NEXT — AFFINE287-DET1-HYBRID-MQ45

**Status:** research attack target only. Erdős #287 remains open.

The singleton provider dictionary has now been audited. The direct identification

```text
singleton generated Type II = Gate-1B common-conductor signed covariance
```

is false. The first general unresolved analytic object is the determinant-one hybrid correlation

```text
AFFINE287-DET1-HYBRID-MQ45
```

with the equivalent descriptive label

```text
HYBRID-MQ-KLOOSTERMAN-LARGE-SIEVE.
```

## Exact source form

After sign separation and the generated two-outer reduction, the residual has the form

\[
\mathcal K^{(2)}_{s,\pi}
=
\sum_{q\sim Q}\lambda_\pi(q)
\sum_{\substack{m\sim M,\ n\sim N\\qab=2mn+s}}
\xi_\pi(m)\kappa_\pi(n)
\Psi_{\pi,1}(a)\Psi_{\pi,2}(b),
\qquad s=\pm1,
\]

with

\[
MN\asymp X,\qquad M=X^\mu,\qquad \varepsilon_*<\mu\le3/20,
\qquad QAB\asymp X.
\]

The determinant-one identity is

\[
(qa)b-(2m)n=s.
\]

Hence

\[
(qa,2m)=1,\qquad (b,n)=1,
\]

and after fixing `q,a,m` and one particular solution,

\[
b=b_0+2mt,\qquad n=n_0+qa\,t.
\]

The inner problem is therefore

\[
\sum_{t\in I_{q,a,m}}
\Psi_{\pi,2}(b_0+2mt)\,\kappa_\pi(n_0+qa\,t),
\]

summed coherently over `q,a,m` with the literal generated source weights.

## Already routed subranges

Do not reopen these as the first target unless their source certificate fails:

1. large shifted-output block -> existing one-outer/F3 route;
2. low/moderate modulus AP child -> Wright-compatible route, conditional on the actual short coefficient satisfying the needed Siegel-Walfisz adapter;
3. native QK5 child -> possible common-conductor covariance child, only after
   `SINGLETON-TO-NATIVE-QK5-SOURCE-ADAPTER45` and
   `OUTER-GENERATED-COEFFICIENT-STABILITY-OF-CC45`;
4. 3-/4-/higher-outer source -> exact algebraic reduction to generated two-outer.

## Hostile rules for the next run

The next proof attempt must preserve:

- the affine sign `s=±1`;
- the exact ranges of `q,a,m,n,b,t`;
- the original source prefactor;
- the generated outer coefficient grammar, not only divisor-bound envelopes;
- every Möbius carrier with its actual variable provenance;
- common/composite conductor routing;
- principal/zero/nonunit/collision strata;
- coefficient norms and multiplicities;
- low/mid/high conductor reassembly.

Do not identify Ford outer `mu(m)` with a shifted-output modulus Möbius factor: exact coprimality forbids that variable identification.

## Allowed outcomes

Return exactly one of:

1. **PASS** — with a complete proof and signed margin;
2. **SPECIALIZATION** — exact reduction to an existing theorem, with literal source/range/norm dictionary;
3. **NARROWER RESIDUAL** — print the first exact surviving kernel and required saving;
4. **FAIL** — show the obstruction precisely.

Until such a result exists:

```text
AFFINE287-DET1-HYBRID-MQ45: OPEN
K0-SMOOTH-PARITY: OPEN
FCL: OPEN
ERDOS287: OPEN
```
