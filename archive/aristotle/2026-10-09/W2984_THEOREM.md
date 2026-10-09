# W2.984 — theorem statement

**Erdős #287 remains open.** The theorem below is asymptotic, conditional on the analytic
lemmas written in `AFFINE_CHEN_TRANSFER_W2984.md`, and **ineffective** (`ineffectiveExistential`).
It makes no claim at the endpoint \(s=2.984\) and no global #287 claim.

## Theorem (W2.984)

For every real \(s>2.984\) there exists \(M_s\) such that every hypothetical Erdős #287
counterexample \(A\) with \(M=\max A\ge M_s\) satisfies
\[ \frac{M}{\min A}<s . \]

Equivalently, with \(W\) ranging over exact #287 words with smallest denominator \(a(W)\) and
largest denominator \(M(W)\):
\[ \forall s>2.984\ \exists M_s\ \forall W:\ \ M_s\le M(W)\ \wedge\ s\,a(W)\le M(W)\ \Longrightarrow\ \neg\,\mathrm{Counterexample287}(W). \]

## Lean form (`RequestProject/Erdos287/W2984Publication/MainTheorem.lean`)

```lean
theorem W2984 (S1 : AffineChenS1Provider P) (S2 : AffineChenS2Provider P)
    (S3 : AffineChenS3Provider P) (Ssq : AffineChenSquareTailProvider P) :
    ∀ s : ℝ, 2.984 < s → W3Statement s

theorem W2984_counterexample_form (S1 : AffineChenS1Provider P) (S2 : AffineChenS2Provider P)
    (S3 : AffineChenS3Provider P) (Ssq : AffineChenSquareTailProvider P) :
    ∀ s : ℝ, 2.984 < s → ∃ Ms : ℕ, ∀ A : Finset ℕ, ∀ hA : Erdos287Counterexample A,
      Ms ≤ A.max' hA.nonempty → (A.max' hA.nonempty : ℝ) / A.min' hA.nonempty < s
```

Here `P : W3FrameworkProvider` is the unchanged W3/BFM framework with the pair constant left
free. `W3Statement s` is the W3 width statement, imported from `Erdos287.W3Publication`.

## Hypotheses (one recognisable analytic lemma each)

| Lean provider | paper lemma | content |
|---|---|---|
| `W3FrameworkProvider` | W3 inputs (BFM Lemma 4.6(i),(ii), Lemma 4.7; W3 compiler) | Maynard weights, first moment, normaliser, window data. No pair bound, occupancy, or contact statement |
| `AffineChenS1Provider` | Lemma 7.1 `AffineChenS1` | \(S_1\le(\Omega_1+C_1\delta+\varepsilon)\mathfrak M\) |
| `AffineChenS2Provider` | Lemma 8.1 `AffineChenS2` | \(S_2\ge(2\Omega_2-C_2\delta-\varepsilon)\mathfrak M\) |
| `AffineChenS3Provider` | Lemma 9.1 `AffineChenS3` | \(S_3\le(2\Omega_3+C_3\delta+\varepsilon)\mathfrak M\) |
| `AffineChenSquareTailProvider` | Lemma 10.1 `AffineSquareTail` | \(S_{\rm sq}\le\varepsilon\mathfrak M\) |

None of these structures is ever constructed in the repository.

## Corollary (the pair constant)

Under the same hypotheses, for each pair of distinct coordinates \(j\ne\ell\) (`pairBound_of_chen`):
\[ \mathbb E\bigl[1_{\mathbb P}(L_j)1_{\mathbb P}(L_\ell)\bigr]\le\Bigl(c_{\rm cert}+C_{\rm err}\delta+\tfrac52\varepsilon\Bigr)\mathfrak M,\qquad c_{\rm cert}=\frac{796682507263}{200000000000}=3.983412536315 . \]
The bound \(\Omega_1-\Omega_2+\Omega_3\le c_{\rm cert}<3.984\) is proved in the kernel without
hypotheses (`pairConstant_le_certificate`, `pairConstant_lt`).

## Remarks

* The proof gives every \(s>c_{\rm cert}-1\approx2.983413\). The published statement is
  deliberately restricted to \(s>2.984\).
* The same machinery with the Selberg constant \(4\) recovers W3 (`W3_of_selbergPairBound`).
