# Algebraic FCHS propagation and compatible parameter choices

**Scope.** The statements proved here are elementary implications. They do not prove a spectral large-sieve estimate, a provider, the tail theorem, or a finite splice. No input Lean or PDF was modified. These additions should be integrated and checked in the next Aristotle run.

## A. Keep the corrected expression, and pay it

For nonnegative F,C,B0,S,H with F<=B0 and H<=S,

\[
FCHS\le B_0CS^2,
\]

because FH<=B0 S and CS>=0. Consequently,

\[
FC^2+B_0CS^2+FCHS\le FC^2+2B_0CS^2.
\]

Monotonicity of the square root yields the corresponding root bound. More generally, F<=c B0 and H<=d S give FCHS<=cd B0 C S^2 for nonnegative fixed c,d.

The source uses length envelopes Bbar~NR and Fbar~N/Q, with Q,R>=1. Therefore Fbar<=c Bbar for one fixed constant. With g>=1, F=Fbar/g remains within that envelope. If actual dyadic B0 is much smaller than its upper envelope, enlarge the nonnegative upper bound before applying the lemma; do not assert F<=B0 for every unmodified dyadic cell.

This makes the enlarged term no worse than a fixed multiple of an already-present square-root monomial. It explains how the four range comparisons can be retained without silently omitting the extra C.

## B. Correct g-scaling identity

Let g>0, F=F0/g, C=C0/g, and all radicands be nonnegative. Then

\[
\sqrt F\sqrt{FC^2+B_0CS^2+FCHS}
=
\frac{\sqrt{F_0}}g
\sqrt{\frac{F_0C_0^2}{g^2}+B_0C_0S^2+\frac{F_0C_0HS}{g}}.
\]

Proof: square both nonnegative sides and expand. Both equal

\[
\frac{F_0^2C_0^2}{g^4}
+\frac{F_0B_0C_0S^2}{g^2}
+\frac{F_0^2C_0HS}{g^3}.
\]

For g>=1, the right-hand side is bounded by the same expression with the two internal reciprocal-g factors replaced by 1, times 1/g. The exceptional factor involving C sqrt(F) also decreases with g.

## C. Do not confuse the primary paper's two stages

The normalized algebraic identity in Pascadi's proof is

\[
\frac{B_0}{C}
\sqrt{H^2S^4FC/B_0}
\sqrt{C^2(FC/B_0+S^2)+FCHS/B_0}
=
HS^2\sqrt F\sqrt{FC^2+B_0CS^2+FHS}
\]

for positive B0,C and nonnegative other data. Squaring verifies it directly. The intermediate FCHS/B0 is not the same normalization as the final FHS.

The archive deliberately uses a larger FCHS envelope at the final stage. Under C>=1 that enlargement is a valid inequality. The A/B lemmas above show a conservative way to pay it. At short scales not covered by C>=1, use the actual positive-scale theorem convention or a direct bound; do not infer the enlargement without hypotheses.

Correct the documentation comment at W4Route.lean:145-146: the proved order is `pascadiInnerOld <= pascadiInner`. A bound by the smaller RHS implies a bound by the larger one. The reverse implication does not follow. This concerns bound ordering, not the validity of an unproved old estimate.

## D. Explicit parameter repair at the current source contract

The source contract exports

\[
\epsilon=\kappa/2000.
\]

The current provider allows \(\sigma_{old}=\kappa/1000\), but the supplied actual-atom theorem only proves a sufficient range \(\sigma\le\epsilon/100\). With the displayed packet exponent,

\[
\frac\epsilon2-\frac{391}{256}\sigma_{old}
=-\frac{327}{256000}\kappa<0.
\]

A consistent conservative replacement is

\[
\sigma=\kappa/1000000,
\qquad
\delta_{spectator}=\sigma/4.
\]

Then

\[
\sigma<\epsilon/100,
\qquad
2\delta_{spectator}=\sigma/2<\sigma,
\]

and

\[
\boxed{
\frac\epsilon2-\frac{391}{256}\sigma
=\frac{63609}{256000000}\kappa>0.
}
\]

The remaining exponent half is available for fixed slopes, the actual growing presieve and cutoff constants. That support statement must be proved from the constructed physical family. This repair narrows a sufficient source class; it is not a theorem that the broader old provider was false. A proved stronger epsilon export is an alternative.

Order of choices: choose positive kappa and the fixed scalar construction; choose the spectral reserve and support exponents; construct the fixed Maynard dimension/test function and affine tuple; then let the physical scale tend to infinity. Track any exponent dependence on dimension rather than hiding it in an absolute constant.

## E. Finite checks

`verify_review.py` verifies these polynomial/rational implications on exact finite fixtures and the numerical fraction identities. The proofs are the algebra above; the fixtures are regression checks, not substitutes for universal reasoning or analytic estimates.
