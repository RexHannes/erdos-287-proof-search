# Erdős #287 draft — V13 Gate 1A replacement/update

This text is intended to replace the current publication-facing dependency discussion of
Gate 1A.  It does **not** change the finite Lean theorem and does **not** assert that Gate
1A has been closed.

## Gate 1A: a conditional canonical packet theorem, not a mandatory global gate

Gate 1A should be separated into two statements.

First, the project contains a substantial finite/operator mechanism for a canonical
common-weight packet.  In the notation of the existing dossier, a row is

\[
e=(r,k,m),\qquad m'=m+kr,
\]

and the two affine forms satisfy the exact determinant identity

\[
m'A_e(t)-mB_e(t)=2k.
\]

For the canonical source

\[
C_e(b,d)=\sum_t W_D(t)
\Bigl(\sum_{p\asymp L}b_p\rho_p(A_e(t))\Bigr)
\Bigl(\sum_{q\asymp L}d_q\rho_q(B_e(t))\Bigr),
\]

the current conditional theorem gives the target-scale energy estimate once five
load-bearing source statements are supplied:

1. source-preserving Poisson--Bruhat transport and the physical/normalised bridge;
2. fixed-state exclusion with polynomial-height control;
3. the outer-root physical energy identification;
4. projective/diagonal source routing at the final target scale;
5. literal source recombination with the required error bound.

The finite/operator part of this mechanism includes the determinant algebra, the scale
ledger, row-energy conservation, non-projective participation/energy bookkeeping, the
projective ratio-class identity and the finite outer-square-root inequality.  These
pieces do not by themselves supply the five source statements above.

### V13 dependency correction for Erdős #287

Full Gate-1A closure is **not a logically mandatory prerequisite** for the current
Erdős-287 strategy.

The shortest post-V13 route aims to control a fixed Ford certificate's leakage
correlation directly, rather than first proving universal Full Type II or every
Ford-generated coefficient pair.  On that route Gate 1A is only an optional provider.
It is needed precisely to the extent that a literal physical leakage packet is shown to
match the canonical Gate-1A source after a valid scale/source dictionary.

Thus the correct dependency statement is

\[
\boxed{
\text{Gate 1A is invoked only for packets that are source-exactly routed to its
canonical common-weight theorem.}
}
\]

It is incorrect to write

\[
\text{Gate 1A closed}\Longrightarrow\text{Erdős #287 endgame}
\]

without the intervening source dictionary.

### If Gate 1A is invoked: mandatory #287 scale/source dictionary

Gate 1A uses its own ambient scale \(X_1\), with for example

\[
M=X_1^{1/3},\qquad R=X_1^a,\qquad L=X_1^b,
\]

whereas the Ford--Maynard/#287 bilinear variable lies in a fixed interval of the form

\[
(X/2)^{\varepsilon_*}<m\le X^{1/6-\varepsilon_*}.
\]

Therefore a use of Gate 1A in the #287 proof must explicitly provide:

- the relation between \(X_1\) and the #287 scale \(X\);
- identification of the actual physical bilinear variable with the Gate-1A row variables;
- the resulting values/ranges of \(R,L,H,K,U,D\);
- preservation of the canonical **common physical weight** \(W_D\), or a proved
  finite-template/nuclear reduction with acceptable total cost;
- preservation of the binding fixed-power margin after every scale conversion,
  truncation and multiplicity cost.

No conclusion follows merely from using the same symbol \(X\) or from the existence of a
canonical Gate-1A estimate at a different scale.

### Publication-facing status

The recommended ledger is:

| Gate-1A component | V13 status |
|---|---|
| determinant / row algebra | finite algebra available |
| scale ledger and row conservation | banked finite/operator material |
| canonical common-weight analytic theorem | conditional on five source pins |
| global arbitrary packet exhaustiveness | not claimed |
| #287 scale/source dictionary | required only if an actual #287 packet is routed here |
| logical role in #287 | optional analytic provider |

Accordingly the full #287 dependency graph should show Gate 1A as a side provider:

\[
\begin{array}{c}
\text{fixed-certificate #287 leakage packets}\\
\downarrow\\
\begin{cases}
\text{Gate 1B / direct analytic estimate},\\
\text{Gate 1A, only for a packet with a proved literal dictionary},\\
\text{direct exceptional/standard estimate}
\end{cases}\\
\downarrow\\
\text{fixed-certificate leakage bound}\\
\downarrow\\
\text{Ford--Maynard lower-bound replay / large-}M\text{ supply}.
\end{array}
\]

This wording keeps the existing Gate-1A mathematics available without making the
Erdős-287 proof depend on a global Gate-1A closure that the final leakage decomposition
may not use.
