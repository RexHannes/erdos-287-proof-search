# ERDŐS #287 — COMPLETE MESSAGE-LEVEL MATHEMATICAL SOURCE AND PHYSICAL TAIL CONSTRUCTION

Continue the existing `RequestProject/Erdos287/SourceChain` and `RequestProject/Erdos287/CurrentTail` formalisation.

**IMPORTANT: This message contains the mathematical source data required for the task. Do not ask me to upload V97, V99, V100R, V100R2, V100R4R, the Astra report, or the final manuscript. Those materials are not accessible in your current workspace. Their relevant formulas and mathematical obligations are supplied directly below.**

Treat the formulas as **message-level mathematical source**, not as already proved Lean theorems.

Do not infer that a statement has been proved merely because this message supplies it. Derive it, prove it, or isolate its exact remaining analytic hypothesis.

Preserve all previously kernel-proved declarations. Do not restart the project.

The immediate objective is to construct the **actual physical #287 source**, not another abstract model of one.

The eventual objective is:

\[
\boxed{
\exists M_0\;\forall M\ge M_0:
\text{no gap-two unit-fraction representation has maximum }M.
}
\]

This is the existential asymptotic tail theorem, **not** an effective onset or global resolution of Erdős #287.

---

# PART I — THE PHYSICAL MATHEMATICAL PROBLEM

## 1. Exact counterexample

A putative counterexample is a finite set

\[
E=\{e_1<e_2<\cdots<e_t\}
\subseteq\mathbb N_{\ge2}
\]

such that

\[
\sum_{n\in E}\frac1n=1
\]

and

\[
e_{i+1}-e_i\le2
\]

for every consecutive pair of elements.

Define

\[
a_*=\min E,\qquad M_*=\max E.
\]

Thus there are no two consecutive omitted integers strictly inside the interval occupied by the representation.

The harmonic-series comparison gives

\[
a_*\le\frac{M_*}{e}+1
\]

and consequently

\[
a_*<\frac38M_*
\]

for sufficiently large \(M_*\).

**Notation firewall:** \(M_*\) denotes the largest denominator. Later, \(x=MN\) uses \(M,N\) as Type-II convolution lengths. These quantities must not be identified.

Use the project's existing exact #287 representation type where possible. Prove any required equivalence to the above definition rather than introducing a new unrelated predicate.

---

# PART II — THE SEVEN-BLOCK COMPILER AND FINITE CONTRADICTION

## 2. Contact graph

Let the seven vertices be \(\mathbb Z/7\mathbb Z\).

Two different vertices are connected by a useful edge when their difference is

\[
\pm2\quad\text{or}\quad\pm3\pmod7.
\]

Equivalently, the differences are \(2,3,4,5\) modulo seven.

Call this graph \(\Gamma_{7,2}\).

Its independence number is

\[
\boxed{\alpha(\Gamma_{7,2})=2.}
\]

Each vertex is blown up into an equal block of affine-form indices.

Therefore, whenever three blocks contain prime values, at least two occupied blocks are joined by a useful edge.

The compiler used in the moment argument requires **complete compatibility across each useful block pair**, not merely one designated compatible edge.

## 3. Prescribed-shape integer slopes

Choose finitely many pairwise disjoint positive rational intervals \(J_i\) for offsets.

Construct distinct positive integers

\[
a_i=A_0+b_i
\]

with the normalized offsets \(b_i/T\) in the prescribed intervals and satisfying

\[
\boxed{\gcd(a_i,a_j)=|a_i-a_j|}
\]

for all distinct indices in the prescribed compiler family.

The existing Lean archive contains the general theorems

- `prescribedShape_gcdClique`;
- `edgeOnly_compiler`;

in the older `ResearchBankV14/EdgeOnlyCompilerInterface.lean` development.

Inspect their actual declarations and attempt to specialise the already-proved existence result to the seven-block geometry. Do not rebuild the CRT construction from scratch if the general theorem suffices.

Do not mistake an older fixed eleven-block compiler for the actual seven-block compiler.

Define the affine forms

\[
L_i(t)=a_it+1.
\]

For \(a_i<a_j\), let

\[
d_{ij}=a_j-a_i=\gcd(a_i,a_j).
\]

Then

\[
\boxed{
\frac{a_j}{d_{ij}}L_i(t)
-
\frac{a_i}{d_{ij}}L_j(t)
=1.
}
\]

This is the exact adjacency identity.

For useful edges put

\[
\lambda_{ij}=\frac{a_ia_j}{|a_i-a_j|}.
\]

Choose the offset boxes and their common translation so that

\[
\frac{\lambda_{\max}}{\lambda_{\min}}<\frac83.
\]

Then choose fixed positive rationals \(c_1,c_2\) with

\[
\frac3{8\lambda_{\min}}
<c_1<c_2<
\frac1{\lambda_{\max}}.
\]

These parameters place the two resulting adjacent physical integer positions strictly inside

\[
\left(\frac38M_*,M_*\right)
\]

for physical parameters

\[
c_1M_*<t<c_2M_*.
\]

The affine forms at these parameters are primes of size at least

\[
\kappa_0 M_*
\]

for some fixed \(\kappa_0>0\).

Prove the physical contact-window construction with the actual slopes. Do not merely assume an abstract `WindowControl`.

## 4. Bounded-cofactor row rigidity

Set

\[
H=\left\lceil\frac1{\kappa_0}\right\rceil,
\]

\[
L_H=\operatorname{lcm}(1,\ldots,H),
\qquad
B_H=\sum_{j=1}^H\frac{L_H}{j}.
\]

If \(p\) is prime with

\[
p>\max(H,B_H)
\]

and

\[
\left\lfloor\frac{M_*}{p}\right\rfloor\le H,
\]

then no multiple of \(p\) can belong to a reciprocal representation \(E\) whose reciprocal sum is one.

The elementary proof multiplies the reciprocal identity by \(p\), reduces modulo \(p\), clears denominators by \(L_H\), and uses positivity to show that the relevant nonnegative numerator must be zero.

Thus simultaneous prime values on a useful edge force two adjacent physical integers to be omitted.

These positions lie between \(a_*\) and \(M_*\), contradicting the gap-two condition.

Reuse already-proved row-rigidity and affine-adjacency lemmas where their types match.

---

# PART III — ACTUAL MAYNARD WEIGHTS AND THE MOMENT FRAMEWORK

## 5. Test function and coefficients

Fix a sufficiently small spectator-support exponent

\[
\delta_s>0.
\]

Then choose a sufficiently large fixed integer \(k\), divisible by seven, and a symmetric finite-tensor smooth function \(F\) supported on

\[
t_1+\cdots+t_k\le\delta_s.
\]

Use a finite tensor decomposition

\[
F(t_1,\ldots,t_k)
=
\sum_{v=1}^{V}
\prod_{i=1}^{k}f'_{i,v}(t_i),
\]

where the one-variable functions are smooth and compactly supported.

Define

\[
I(F)=\int F(\mathbf t)^2\,d\mathbf t,
\]

\[
J_i(F)=
\int
\left(
\int F(\mathbf t)\,dt_i
\right)^2
d\mathbf t_{\widehat i},
\]

\[
L_{ij}(F)=
\int
\left(
\iint F(\mathbf t)\,dt_i\,dt_j
\right)^2
d\mathbf t_{\widehat{i,j}}.
\]

The finite-tensor Maynard/Banks–Freiberg–Maynard construction is intended to supply a fixed function with strict first- and pair-moment margins.

Its existence is a mathematical theorem to formalise/import or isolate narrowly; it is not a license to assume that the desired blocks are occupied.

## 6. Presieve and physical weight

For sufficiently large global parameter \(X\), put

\[
w=\log\log\log X,
\qquad
W=\prod_{p\le w}p,
\]

\[
B_X=\frac{\phi(W)}W\log X,
\]

and

\[
\mathcal N_X=
\frac{(c_2-c_1)X}{W}B_X^{-k}.
\]

All prime divisors of the fixed slopes and their nonzero differences eventually divide \(W\).

For a divisor vector

\[
\mathbf d=(d_1,\ldots,d_k)
\]

define the actual coefficient

\[
\boxed{
\omega_{\mathbf d}
=
\mathbf1_{(\prod_i d_i,W)=1}
\left(\prod_{i=1}^k\mu(d_i)\right)
\sum_{v=1}^{V}
\prod_{i=1}^k
f'_{i,v}\!\left(\frac{\log d_i}{\log X}\right).
}
\]

Its support satisfies

\[
\prod_i d_i\le X^{\delta_s}.
\]

Define the nonnegative squared Maynard weight

\[
\boxed{
w_X(t)=
\mathbf1_{c_1X<t<c_2X}
\mathbf1_{W\mid t}
\left(
\sum_{\substack{\mathbf d\\d_i\mid L_i(t)\;\forall i}}
\omega_{\mathbf d}
\right)^2.
}
\]

This is the physical weight to construct in Lean. It is not an arbitrary nonnegative weight record.

Set

\[
S_0=\sum_t w_X(t).
\]

The analytic main-term claim is

\[
S_0=(1+o(1))\mathcal N_XI(F).
\]

The first-prime moment is

\[
S_1=
\sum_t w_X(t)
\sum_{i=1}^k
\mathbf1_{L_i(t)\text{ prime}},
\]

with expected main term

\[
S_1=(1+o(1))
\mathcal N_X\sum_iJ_i(F).
\]

These asymptotics depend on Euler-product evaluations and analytic prime-distribution results. Do not treat them as pure algebra.

## 7. One-sided seven-block moment dictionary

Let \(Y_b(t)\) be the number of prime form values in block \(b\), and set

\[
P(t)=\sum_{b=1}^7Y_b(t),
\]

\[
Q_2(t)=
\sum_{b=1}^7\binom{Y_b(t)}2,
\]

\[
Z(t)=\#\{b:Y_b(t)>0\}.
\]

Expectations are taken using weights \(w_X(t)/S_0\).

The frozen working moment bounds are

\[
\liminf_{X\to\infty}\mathbb EP
\ge999999,
\]

\[
\limsup_{X\to\infty}\mathbb EQ_2
\le\frac{1700001700000}{7}.
\]

The exact margin is

\[
\boxed{
\frac{999999^2}{2}
-999999
-\frac{3400003400000}{7}
=
\frac{199965200021}{14}>0.
}
\]

The elementary moment inequality is

\[
(\mathbb EP)^2
\le
(\mathbb EZ)
(\mathbb EP+2\mathbb EQ_2).
\]

Therefore the strict margin forces a positive-weight parameter with at least three occupied blocks.

### Mandatory correction to the existing Lean framework

The old `SevenBlockMainTermDictionary` may require absolute closeness of the first and pair moments to frozen constants, with error controlled solely by the prime-distribution remainder.

That is potentially stronger than the physical analytic proof.

The physical source only provides one-sided first/pair-moment bounds, with independent \(o(1)\) model/Euler errors.

Construct a corrected interface of the form

\[
\mathbb EP\ge\mu_--e_1(X),
\]

\[
\mathbb EQ_2
\le
\nu_++e_2(X)
+\frac{|R_\Sigma^P(X)|}{\mathcal N_XI(F)},
\]

or the precise equivalent derived from the actual normalisation, where

\[
e_1(X),e_2(X)\to0.
\]

Do not require the model errors to vanish when \(R_\Sigma^P=0\).

Re-prove the strict moment consumer with this physically faithful interface.

Construct `SevenBlockTailFramework` using the actual fixed affine forms, actual Maynard weights, actual source scale and this corrected moment dictionary.

---

# PART IV — THE MISSING PHYSICAL PAIR PACKETS

## 8. Packet index

This section supplies the physical source data previously absent from the Lean repository.

For each designated coordinate pair

\[
1\le j<\ell\le k,
\]

expand the Maynard square using two labelled divisor vectors

\[
\mathbf d=(d_1,\ldots,d_k),
\qquad
\mathbf d'=(d'_1,\ldots,d'_k).
\]

For the pair term, impose

\[
d_j=d'_j=d_\ell=d'_\ell=1.
\]

For spectator coordinates \(i\notin\{j,\ell\}\), define

\[
q_i=[d_i,d'_i],
\qquad
q_0=\prod_{i\ne j,\ell}q_i.
\]

The physical packet index is the **labelled tuple**

\[
\boxed{
\xi=(j,\ell,\mathbf d,\mathbf d')
}
\]

restricted to the actual admissible/compatible support.

Define

\[
\boxed{
f_\xi=a_jWq_0,
}
\]

\[
\boxed{
\Gamma_\xi
=
\omega_{\mathbf d}\omega_{\mathbf d'}.
}
\]

The \(q_i\) are squarefree, pairwise coprime and coprime to \(W\) on the compatible physical source, and

\[
q_0\le X^{2\delta_s}.
\]

Do not collapse distinct labelled packets merely because they share the same numerical \(q_0\). Their coefficients and residue conditions may differ.

The number of labelled assignments over a fixed \(q_0\) is bounded using

\[
(3(k-2))^{\omega(q_0)}
\]

before the additional compatibility restrictions.

## 9. Physical prime and base residue

Let

\[
p=L_j(t)=a_jt+1
\]

with \(W\mid t\).

Then

\[
p\equiv1\pmod{a_jW}.
\]

For spectator coordinate \(i\), the condition

\[
q_i\mid L_i(t)
\]

implies

\[
a_ip\equiv a_i-a_j\pmod{q_i}
\]

and hence, when the inverse exists,

\[
\boxed{
p\equiv1-a_ja_i^{-1}\pmod{q_i}.
}
\]

Justify every inverse using the actual presieve/coprimality hypotheses.

Define \(c_\xi\) as the unique compatible CRT residue modulo

\[
f_\xi=a_jWq_0
\]

combining

\[
p\equiv1\pmod{a_jW}
\]

with all spectator congruences modulo \(q_i\).

Prove

\[
(c_\xi,f_\xi)=1.
\]

## 10. Additional scalar divisor and affine residue

For the other designated coordinate \(\ell\), the condition

\[
d\mid L_\ell(t)
\]

translates into

\[
\boxed{
a_\ell p\equiv a_\ell-a_j\pmod d.
}
\]

The actual scalar support requires

\[
(d,f_\xi)=1.
\]

Do not immediately set \(A=a_\ell\) and \(B=a_\ell-a_j\) and assume \((A,B)=1\).

Instead define

\[
g_{j\ell}=(a_j,a_\ell),
\]

\[
A_{j\ell}=\frac{a_\ell}{g_{j\ell}},
\qquad
B_{j\ell}=\frac{a_\ell-a_j}{g_{j\ell}}.
\]

Then

\[
(A_{j\ell},B_{j\ell})=1.
\]

In the complete prescribed-shape compiler, one may further derive \(B_{j\ell}=\pm1\); prove and use that simplification only where the compiler construction genuinely guarantees it.

Because \(g_{j\ell}\mid a_j\), its prime divisors eventually divide \(W\). The physical scalar divisor is coprime to \(W\), so

\[
(g_{j\ell},d)=1.
\]

Prove this before replacing the unreduced congruence with

\[
\boxed{
A_{j\ell}p\equiv B_{j\ell}\pmod d.
}
\]

Define the actual CRT residue \(b_{\xi,d}\) modulo \(f_\xi d\) by

\[
b_{\xi,d}\equiv c_\xi\pmod{f_\xi},
\]

\[
A_{j\ell}b_{\xi,d}
\equiv B_{j\ell}\pmod d.
\]

Prove existence, uniqueness and unit status under the actual source hypotheses.

## 11. Physical prime-counting functions

Define

\[
\mathcal J_j(X)
=
(a_jc_1X+1,\;a_jc_2X+1),
\]

\[
P_j(q,b)
=
\#\{p\in\mathcal J_j(X):
p\text{ prime},\ p\equiv b\pmod q\}.
\]

Let

\[
V_j(X)=
\operatorname{Li}(a_jc_2X+1)
-
\operatorname{Li}(a_jc_1X+1).
\]

Define

\[
E_j(q,b)
=
P_j(q,b)-\frac{V_j(X)}{\phi(q)}.
\]

When using the existing generic `TensorSource`, construct the physical sequence with the interval and designated coordinate attached to the packet. Do not silently replace prime counts by von-Mangoldt weighted counts; that is a separate analytic approximation.

## 12. The literal physical prime remainder

The physical sum is

\[
\boxed{
R_\Sigma^P(X)
=
\sum_{1\le j<\ell\le k}
\sum_{\xi\in\Xi_{j,\ell}}
\Gamma_\xi
\sum_{\substack{d\text{ in the actual scalar support}\\(d,f_\xi)=1}}
\ell_X(d)
E_j(f_\xi d,b_{\xi,d}).
}
\]

The large-smooth/squarefull pruning is a separately paid component and must not be silently erased from the original source definition.

### Critical packet-indexing issue

Existing generic Lean code may sum over \(j\) independently of \(\xi\).

But the genuine \(\xi\) already contains \((j,\ell)\).

Therefore do **not** instantiate the generic tensor source by introducing an additional unrestricted \(j\)-sum.

Either:

1. prove an exact selector/reindexing equality between the generic tensor and the physical pair-indexed sum; or
2. define the physical packet source directly with \(j=j(\xi)\) and use a proved adapter.

The exact equality of the original and formal remainder must be proved before declaring `physicalTailSource` constructed.

---

# PART V — COMPLETE PARITY-SENSITIVE SCALAR UPPER SIEVE

## 13. Internal and total levels

Choose a fixed small positive reciprocal integer parameter

\[
\epsilon_0=\frac1T,
\qquad
\tau=\epsilon_0^9.
\]

Define

\[
D_{\rm tot}=X^{59/100},
\]

\[
D_{\rm int}
=
D_{\rm tot}^{1/(1+\epsilon_0+\tau)},
\]

\[
u_0=D_{\rm int}^{\epsilon_0^2},
\]

\[
D_{\rm low}
=
D_{\rm int}^{\epsilon_0}
=
X^\beta.
\]

Distinguish \(D_{\rm int}\) from \(D_{\rm tot}\) throughout.

## 14. High-prime boxes

Use ordered nonincreasing high-prime boxes

\[
I_h=(P_h,P_h^{1+\tau}]
\]

with the odd-prefix conditions

\[
\left(\prod_{h<i}P_h\right)P_i^3
<D_{\rm int}
\]

for even total high-prime parity \(J\), and

\[
\left(\prod_{h<i}P_h\right)P_i^3
<
D_{\rm int}^{1/(1+\tau)}
\]

for odd \(J\), whenever \(i\le J\) is odd.

The empty high-prime vector \(J=0\) is included.

For a labelled box vector \(\mathbf P\), let

\[
T_{\mathbf P}(a)
\]

count tuples of pairwise distinct high primes in the prescribed boxes with product \(a\).

For a repeated box \(I\), let \(m_I\) be its multiplicity and define

\[
\gamma(\mathbf P)=\prod_I m_I!.
\]

Use the single canonical convention

\[
B_{\mathbf P}(a)
=
\frac{T_{\mathbf P}(a)}{\gamma(\mathbf P)}.
\]

This coefficient vanishes on nonsquarefree arguments.

Do not mix this labelled-tuple convention with a different convention for disjoint boxes.

## 15. Low-prime weights and full scalar coefficient

Let

\[
\lambda_{\rm low}^{+},
\qquad
\lambda_{\rm low}^{-}
\]

be the actual upper and lower fundamental-lemma low-prime weights at level \(D_{\rm low}\).

Set

\[
\kappa_J=
\begin{cases}
\lambda_{\rm low}^{+},&J\text{ even},\\
\lambda_{\rm low}^{-},&J\text{ odd}.
\end{cases}
\]

Then the complete coefficient is

\[
\boxed{
\ell_X(d)
=
\sum_{J,\mathbf P}
(-1)^J
\sum_{ba=d}
\kappa_J(b)B_{\mathbf P}(a).
}
\]

The \(J=0\) sector contributes the **entire low upper-sieve weight**, not merely \(1_{d=1}\).

The full scalar multiplier is

\[
U_X(v)=\sum_{d\mid v}\ell_X(d).
\]

The claimed pointwise property is that \(U_X\) is nonnegative and majorizes the relevant prime/rough event.

Prove it using the correct sign ordering:

- even high parity: upper low sieve;
- odd high parity: lower low sieve before multiplication by the negative outer sign.

Do not introduce a generic positive-completion hypothesis in place of this actual argument.

## 16. Correct scalar coefficient

The leading normalized pair coefficient is

\[
\boxed{
\frac{2\log X}{\log D_{\rm int}}
=
\frac{200}{59}(1+\epsilon_0+\tau).
}
\]

It is **not** exactly \(200/59\) at fixed \(\epsilon_0\).

The numerical safety certificate is

\[
\boxed{
\frac{200}{59}(1+10^{-3})
+\frac1{295}
=
\frac{17}{5}-\frac1{295}
<
\frac{17}{5}.
}
\]

Formalize the exact rational arithmetic.

Any error written \(O(\epsilon_0)\) without an explicit constant must remain asymptotic; do not fabricate a numerical coefficient.

Keep the correct order of parameter choices.

## 17. Three-colour squarefree tensorization

For each fixed high-prime box vector, partition its \(J\) labelled positions into three groups.

Let \(m_{I,h}\) be the number of positions from box \(I\) assigned to group \(h\in\{1,2,3\}\).

Set

\[
C_{\mathbf P}
=
\prod_I
\binom{m_I}{m_{I,1},m_{I,2},m_{I,3}}.
\]

Independently assign each allowed high prime one of three colours.

Let \(\gamma_{h,\chi}\) indicate squarefree products supported on primes of colour \(h\), with the prescribed box counts.

The exact identity is

\[
\boxed{
B_{\mathbf P}(a)
=
\frac{3^J}{C_{\mathbf P}}
\mathbb E_\chi
[
(\gamma_{1,\chi}*
\gamma_{2,\chi}*
\gamma_{3,\chi})(a)
].
}
\]

It holds for every positive integer \(a\), including nonsquarefree arguments, on which both sides vanish.

Set

\[
G_{1,J,\chi}
=
\kappa_J*\gamma_{1,\chi}.
\]

The unique low/high prime split gives

\[
|G_{1,J,\chi}|\le1.
\]

Thus

\[
\boxed{
\ell_X
=
\sum_{J,\mathbf P}
(-1)^J
\frac{3^J}{C_{\mathbf P}}
\mathbb E_\chi
[
G_{1,J,\chi}*
\gamma_{2,\chi}*
\gamma_{3,\chi}
].
}
\]

The total variation is independent of \(X\) after fixing the scalar parameters.

Apply this exact decomposition to the **linear centred source before Cauchy**.

Do not replace the square of a sum by the sum of its squares.

---

# PART VI — RANGE EXPORT AND NONCRITICAL BRANCHES

## 18. Structured support before numerical inequalities

Take

\[
0<\kappa<10^{-5},
\qquad
\beta<\kappa/100,
\qquad
\varepsilon=\kappa/2000.
\]

For a critical Type-II cell \(x=MN\), write

\[
N'=Nx^{-2\beta},
\qquad
D_*=x^{3/5-50\kappa}.
\]

The critical individual-variable range is

\[
x^{3\kappa}\le N\le x^{1/3+\kappa/2}.
\]

Thus

\[
x^{2\kappa}\le N'\le x^{1/3+\kappa}.
\]

For each high-box upper endpoint \(U_i=P_i^{1+\tau}\), the relevant odd-prefix inequalities imply

\[
\left(\prod_{h<i}U_h\right)U_i^3
<
D_{\rm int}^{1+\tau}
<
x^{59/100}
<
D_*.
\]

This is intended to establish the **structured support required by Pascadi Proposition 5.2**, not merely the total size bound \(d<D_*\).

Prove the support membership and factor allocation. Do not postulate them.

The claimed factor allocation after inserting the low factor \(b\le x^\beta\) into the common factor is

\[
Q_1\le Nx^{-\kappa-\beta},
\]

\[
N^2Q_2Q_3^2\le x^{1-\kappa+4\beta},
\]

\[
N^2Q_2^5Q_3^2
\le x^{2-\kappa+4\beta}.
\]

Under the identification

\[
Q=Q_1,\qquad R=Q_3,\qquad S=Q_2,
\]

prove

\[
\boxed{N^2R^2S\le x^{1-8\varepsilon}},
\]

\[
\boxed{
N^{71/50}RS^{93/50}
\le x^{1-16\varepsilon}
},
\]

\[
\boxed{
N^{39/25}Q^{11/25}R^2S^5
\le x^{2-32\varepsilon}.
}
\]

The claimed sector reserves are

\[
\kappa-4\beta,
\qquad
\frac{71}{100}(\kappa-4\beta),
\qquad
\frac{36\kappa-89\beta}{25}.
\]

The allocation must be made at actual box upper endpoints, fixed over each box.

Do not invoke the proposition for arbitrary integers merely satisfying \(d<D_*\).

## 19. Original large-smooth/squarefull pruning

Put

\[
z_0=X^{1/(\log\log X)^3},
\]

\[
y_0=X^{1/\log\log X}.
\]

The original bad smooth sector is

\[
\operatorname{sm}(f_\xi d;z_0)\ge y_0.
\]

The original moduli have fixed squarefull part eventually supported on the fixed slope, rather than an unrestricted growing squarefull factor.

The claimed Rankin estimate has decay of the form

\[
\exp\!\left(
-\frac12(\log\log X)^2
\right)(\log X)^{C}.
\]

Formalize exact support and Rankin arithmetic or isolate the smallest genuine analytic input.

Do not delete gcds created only after the quadratic dispersion expansion.

## 20. Repaired exhaustive noncritical routing

Use Heath–Brown's decomposition with three truncated Möbius variables and three smooth variables.

For each dyadic six-variable cell, prove the exhaustive classification:

1. at least one individual variable lies in the critical interval; or
2. there is exactly one large smooth variable; or
3. there are exactly two large smooth variables.

In the second case the complementary product satisfies

\[
U\ll x^{15\kappa}.
\]

In the third case

\[
U\ll x^{12\kappa},
\]

and

\[
N_1,N_2>x^{1/3+\kappa/2}.
\]

The older two-large estimate beginning only at \(x^{3/8}\) does **not** cover this whole range.

For the two-large branch, the actual required residue-uniform analytic estimate is

\[
\boxed{
|\mathscr D(Q,b)|
\ll
x^{o(1)}
\left(
\frac{x}{QN_1}+UQ^{1/2}
\right),
}
\]

where

\[
UN_1N_2\asymp x.
\]

The claimed aggregate bound is

\[
\boxed{
x^{2/3-\kappa/2+o(1)}
+
x^{17903/20000+o(1)}
=o(x).
}
\]

Prove the actual range substitution and the source-normalization conversion.

If the Maynard double-divisor analytic inequality is not formalized, retain only its precise statement as an external input.

The one-large rough progression estimate is used in the regime

\[
T\ge Qx^{\eta_0},
\]

with error of the form

\[
O_A\left(\frac{T}{Q(\log x)^A}\right)
\]

after the stated sieve conditions.

Handle roughness via genuine upper/lower fundamental-lemma sandwiches, not by pretending arbitrary residue restrictions preserve Siegel–Walfisz.

Proper prime powers must be removed from the original source before tensorization; the claimed source contribution is \(x^{1/2+o(1)}\).

---

# PART VII — EXACT RELATIVE CENTERING AND RELATIVE BDH

## 21. Base-relative discrepancy

For coprime \(f,d\), \(b\equiv c\pmod f\), define

\[
\Delta_{\rm rel}
=
P_j(fd,b)-\frac{P_j(f,c)}{\phi(d)}.
\]

The exact centering identity is

\[
\boxed{
E_j(fd,b)
=
\Delta_{\rm rel}
+
\frac{E_j(f,c)}{\phi(d)}.
}
\]

This gives the literal decomposition

\[
R_\Sigma^P=R_{\rm rel}+R_{\rm base}
\]

on the same packet and scalar-divisor support.

The base-only component is paid using ordinary below-half Bombieri–Vinogradov with correct packet multiplicities and reciprocal-density weighting.

It is not an algebraic zero term.

## 22. Exact relative BDH projection

For a coefficient sequence \(\alpha_n\), define

\[
\Delta_\alpha^{f,c}(q,a)
=
\sum_{\substack{n\sim N\\n\equiv c\pmod f}}
\alpha_n
\left(
\mathbf1_{n\equiv a\pmod q}
-
\frac{\mathbf1_{(n,q)=1}}{\phi(q)}
\right).
\]

Let \(b_{c,a}\) denote the CRT class modulo \(fq\).

Then

\[
\boxed{
\Delta_\alpha^{f,c}(q,a)
=
\Delta_\alpha(fq,b_{c,a})
-
\frac1{\phi(q)}
\sum_{a'\bmod q}^{*}
\Delta_\alpha(fq,b_{c,a'}).
}
\]

Subtracting the mean contracts the squared norm.

The intended analytic input is divisor-weighted ordinary BDH, after CRT and divisor-factor multiplicity accounting, within

\[
FQ\le\frac{N}{(\log N)^C}.
\]

Do not confuse this relative \(L^2\) statement with a packetwise \(L^1\) prime-distribution estimate.

The packet reciprocal norm is

\[
\boxed{
\sum_\xi
\frac{|\Gamma_\xi|\tau(f_\xi)^D}{\phi(f_\xi)}
\ll_{k,F,D}
(\log X)^{C_{k,F,D}}.
}
\]

Prove the combinatorial multiplicity/Euler-product part. Keep the deep analytic BDH statement explicit unless it is formally available.

---

# PART VIII — LITERAL ORDERING-B SOURCE AND POISSON TERMS

## 23. Type-II split

For coprime \(l,r\), define

\[
I_s(v)=\mathbf1_{Av\equiv B\pmod s},
\]

\[
U_s(v)=\frac{\mathbf1_{(v,s)=1}}{\phi(s)},
\]

\[
h_s=I_s-U_s.
\]

The exact identity is

\[
\boxed{
I_{lr}-U_{lr}
=
I_l(I_r-U_r)
+
(I_l-U_l)U_r.
}
\]

Reuse the already proved `typeII_split`.

The relative small-modulus centering branch is handled using the relative-BDH input above.

## 24. Ordering B preserves the physical base

For one separated Type-II cell, write

\[
x=MN,\qquad l\sim L,\qquad r\sim R.
\]

The source retains

\[
(f,lr)=1,
\qquad
(AB,lr)=1,
\qquad
(l,r)=1.
\]

A smooth profile \(\Psi\) must be nonnegative, compactly supported and satisfy

\[
\boxed{\Psi(u)\ge1\quad(1\le u\le2).}
\]

You may construct an explicit admissible smooth plateau as a new witness. It need not be the historical unspecified profile.

For example set

\[
\eta(t)=
\begin{cases}
e^{-1/t},&t>0,\\
0,&t\le0,
\end{cases}
\]

\[
\theta(t)=
\frac{\eta(t)}{\eta(t)+\eta(1-t)},
\]

and

\[
\Psi(u)=\theta(4u-2)\theta(10-4u).
\]

Prove smoothness, positivity, compact support and the required plateau. Do not assign a false normalization \(\int\Psi=1\).

The actual Ordering-B square is

\[
\boxed{
V_\xi=
\sum_{l\sim L}
\sum_{m\in\mathbb Z}
\Psi(m/M)
\left|
\sum_{r\sim R}c_{\xi,l,r}
\sum_{n\sim N}\alpha_n
\mathbf1_{mn\equiv c\pmod f}
I_l(mn)h_r(mn)
\right|^2.
}
\]

The first-Cauchy inequality is

\[
|T_\xi|^2\le\mathcal B_\xi V_\xi,
\]

with

\[
\boxed{\mathcal B_\xi\ll ML(\log x)^C.}
\]

Opening this square while retaining the physical base gives

\[
(n_1n_2,fl)=1,
\]

\[
\boxed{
n_1\equiv n_2\pmod{fl}.
}
\]

Do not use the retired character-first Ordering A.

## 25. Exact zero mode

Set

\[
g=(r_1,r_2),
\qquad
t=[r_1,r_2].
\]

The complete zero-mode covariance is

\[
\boxed{
\frac1{flt}
\left(
\mathbf1_{n_1\equiv n_2\pmod g}
-
\frac1{\phi(g)}
\right).
}
\]

For \(g=1\) it vanishes.

Do not treat overlapping \(r\)'s as automatically coprime before paying their actual source contribution.

## 26. Define the physical Poisson discrepancy

Use

\[
e_q(v)=\exp(2\pi i v/q),
\]

\[
\widehat\Psi(\xi)
=
\int_{\mathbb R}\Psi(u)e(-\xi u)\,du.
\]

Define the nonzero Poisson remainder for a valid residue \(\rho\bmod q\) by

\[
\mathscr P_M(q,\rho)
=
\frac Mq
\sum_{h\ne0}
\widehat\Psi(hM/q)e_q(h\rho).
\]

Prove the relevant Poisson identity from an applicable formal Poisson theorem.

Do not use the Poisson identity as an opaque source hypothesis merely because the finite-residue scaling is already proved.

## 27. Literal actual–actual and actual–model terms

Define

\[
C_{12}
=
c_{\xi,l,r_1}
\overline{c_{\xi,l,r_2}}
\alpha_{n_1}
\overline{\alpha_{n_2}}.
\]

For the actual–actual term let

\[
q_{\rm AA}=fl[r_1,r_2].
\]

The CRT residue \(\rho\bmod q_{\rm AA}\) satisfies

\[
n_1\rho\equiv c\pmod f,
\]

\[
An_1\rho\equiv B\pmod{lr_1},
\]

\[
An_2\rho\equiv B\pmod{r_2}.
\]

The raw nonzero actual–actual Fourier sum is

\[
\boxed{
F_{AA,\xi}
=
M
\sum_{l,r_1,r_2,n_1,n_2}
\frac{
C_{12}\,
\mathbf1_{n_1\equiv n_2\pmod{(r_1,r_2)}}
}{
fl[r_1,r_2]
}
\sum_{h\ne0}
\widehat\Psi\!\left(
\frac{hM}{fl[r_1,r_2]}
\right)
e_{fl[r_1,r_2]}(h\rho).
}
\]

All actual unit, support and physical Ordering-B conditions remain.

If the CRT system is incompatible, the summand is zero; do not manufacture a residue.

For the actual–model term, expand the retained coprimality condition by Möbius inversion over \(k\mid r_2\), retaining nonunit \(k>1\) residues.

For squarefree \(k\mid r_2\), \((k,r_1)=1\), the CRT residue \(\rho_k\bmod flr_1k\) satisfies

\[
\rho_k\equiv b_0\pmod{fl},
\]

\[
An_1\rho_k\equiv B\pmod{r_1},
\]

\[
\rho_k\equiv0\pmod k.
\]

The raw mixed term is

\[
\boxed{
F_{AB,\xi}
=
M\sum_{l,r_1,r_2,n_1,n_2}
\frac{C_{12}}{\phi(r_2)}
\sum_{\substack{k\mid r_2\\(k,r_1)=1}}
\frac{\mu(k)}{flr_1k}
\sum_{h\ne0}
\widehat\Psi\!\left(
\frac{hM}{flr_1k}
\right)
e_{flr_1k}(h\rho_k).
}
\]

The full decomposition is

\[
V_\xi=
Z_\xi
+
F_{AA,\xi}
-
2\Re F_{AB,\xi}
+
F_{BB,\xi}.
\]

These are literal physical quantities, not generic spectral-class placeholders.

## 28. Paid mixed and nonclean pieces

The actual mixed-family estimate claimed in the source is

\[
\boxed{
|F_{AB,\xi}|
\ll
(\log x)^C
\left(
\frac{RN^2}{f}+LRN
\right).
}
\]

It follows from a complete lattice-discrepancy treatment before taking termwise Fourier absolute values, including the \(k>1\) terms.

The nonclean actual–actual sectors to pay separately are:

- common \(r\)-factor;
- common \(n\)-factor under actual rough support;
- exact diagonal \(n_1=n_2\);
- near diagonal
  \[
  0<|n_1-n_2|\le N/(\log x)^J.
  \]

The cleaned survivor is

\[
\boxed{
F_{AA,\xi}^{\sharp}
=
\sum_{\substack{
l,r_1,r_2,n_1,n_2\\
\text{actual cleaned conditions}
}}
C_{12}
\mathscr P_M(flr_1r_2,\rho),
}
\]

with

\[
(r_1,r_2)=1,
\qquad
(n_1,n_2)=1,
\]

and the original CRT congruences and coefficient masks.

The exact recombination target is

\[
\boxed{
\left|
\sum_\xi\Gamma_\xi S_\xi
\right|
\le
R_{\rm paid}
+
\sum_\xi|\Gamma_\xi|
\sqrt{
\mathcal B_\xi
|F_{AA,\xi}^{\sharp}|
}.
}
\]

The prior source claims the paid pieces are \(o(\mathcal N_XI)\).

Formalise the exact splitting and normalisation; retain narrow analytic bounds as hypotheses when genuinely unavailable.

---

# PART IX — THE ACTUAL COLOURED ATOM AND POSITIVE \(W_4\)

## 29. Canonical atom

For the cleaned critical atom, use

\[
d=qrs
\]

with the full low-prime component included in the common \(q\)-sequence.

Let

\[
q\sim Q,\quad
r_1,r_2\sim R,\quad
s_1,s_2\sim S,\quad
n_1,n_2\sim N.
\]

Retain

\[
n_1\equiv n_2\pmod{fq},
\]

\[
(n_1,n_2)=1,
\]

\[
|n_1-n_2|>\frac{N}{(\log x)^J},
\]

\[
(n_1n_2,fqA)=1,
\]

\[
(n_1,r_1s_1)=(n_2,r_2s_2)=1,
\]

\[
(r_1s_1,r_2s_2)=1,
\]

and the global cross-coprime condition.

The factor sequences are independent one-bounded coefficients from the exact three-colour decomposition, not arbitrary coupled coefficients.

The actual Fourier modulus is

\[
\mathfrak L=fqr_1s_1r_2s_2.
\]

The CRT class \(\rho\pmod{\mathfrak L}\) satisfies

\[
n_1\rho\equiv c\pmod f,
\]

\[
An_1\rho\equiv B\pmod{qr_1s_1},
\]

\[
An_2\rho\equiv B\pmod{r_2s_2}.
\]

Define

\[
\boxed{
\begin{aligned}
\mathcal K_{A,f,c}
={}&
\sum_{\text{actual clean tuples}}
\frac{
a_q\gamma_{r_1}\overline{\gamma_{r_2}}
\lambda_{s_1}\overline{\lambda_{s_2}}
\alpha_{n_1}\overline{\alpha_{n_2}}
}{
qr_1r_2s_1s_2
}\\
&\times
\sum_{h\ne0}
\widehat\Psi(hM/\mathfrak L)
e_{\mathfrak L}(h\rho).
\end{aligned}
}
\]

Every source mask must be accounted for before claiming the actual packet instantiates this atom.

## 30. No-dilation affine phase

Write

\[
u=r_1s_1,\qquad v=r_2s_2.
\]

The intended exact identity is

\[
\boxed{
\begin{aligned}
e_{fquv}(h\rho)
={}&
e\!\left(
\frac{Bh}{An_1fquv}
\right)\\
&\times
e_{n_1v}\!\left(
Bh(n_1-n_2)
\overline{Afn_2qu}
\right)\\
&\times
e_{Af}\!\left(
h(Ac-B)
\overline{qun_1v}
\right).
\end{aligned}
}
\]

Here bars indicate modular inverses in the displayed modulus.

Prove every inverse is legitimate.

Do not assume

\[
(A,f)=1.
\]

The last phase is the full fixed-local colour. It must not be deleted.

## 31. Character separation modulo \(Af\)

Let

\[
D=Af,\qquad
C_*=n_1r_2s_2.
\]

For a unit \(t\bmod D\), finite-group character orthogonality gives

\[
\mathbf1_{qr_1C_*s_1\equiv t\pmod D}
=
\frac1{\phi(D)}
\sum_{\chi\bmod D}
\overline{\chi(t)}
\chi(qr_1C_*)\chi(s_1).
\]

This occurs after the Ordering-B physical square.

It fixes the \(h\)-phase

\[
e(h\omega_t),
\]

where

\[
\omega_t=\frac{(Ac-B)\overline t}{Af}.
\]

The total absolute colour coefficient mass is

\[
\boxed{\phi(D)\le Af}
\]

rather than \(\phi(D)^2\).

The phase parameter satisfies

\[
\boxed{T_H(\omega_t)\le Af.}
\]

Prove the character identity for the actual finite unit group, without assuming it is cyclic.

## 32. Complementary divisor and first Cauchy

Set

\[
k=\frac{n_1-n_2}{fq}\ne0.
\]

Its integrality follows from the actual Ordering-B congruence; prove this rather than postulating \(k\).

The reciprocal phase becomes

\[
e_{C_*}\!\left(
Bhk\overline{An_2r_1s_1}
\right).
\]

Take

\[
\Omega=(k,n_1,n_2,r_1,r_2,s_2),
\]

with

\[
q=\frac{n_1-n_2}{fk}.
\]

The required physical count is

\[
\boxed{
\#\Omega\ll\frac{N^2R^2S}{f}.
}
\]

Cauchy in exactly these outer variables gives

\[
\boxed{
|\mathcal K_{t,\chi,H}|^2
\ll
\frac{N^2}{fQ^2R^2S^3}
\mathscr W_3.
}
\]

Every factor of \(f,Q,R,S,N\) must be proved in the actual source normalization.

## 33. Positive \(W_4\) landing

Only after forming the nonnegative outer square set

\[
b'=An_2r_1,
\qquad
z=n_1r_2s_2.
\]

The actual source hypotheses imply

\[
(b',z)=1.
\]

The number of outer representations is bounded by

\[
\tau(b')\tau_3(z)=x^{o(1)}.
\]

At the positive-square stage the restriction \(A\mid b'\) may be removed by nonnegative domination.

The resulting positive expression is

\[
\boxed{
\mathscr W_4
=
\sum_{\substack{b',z,k\\(b',z)=1}}
w_1w_2w_3
\left|
\sum_{\substack{s\sim S\\(s,z)=1}}
\lambda'_s
\sum_h
\Phi(h/H)e(h\omega_t)
e_z(Bhk\overline{b's})
\right|^2.
}
\]

Prove that this is reached from the actual physical atom, not from arbitrary functions supplied as inputs to a generic Cauchy theorem.

Preserve the smooth Archimedean phase using fixed-dimensional Fourier separation.

## 34. Quantitative positive \(W_4\) estimate

The published analytic machinery used by the candidate proof is Pascadi's positive-square/exceptional-spectrum framework.

The three estimated components are:

\[
W_{\rm diag}(g)
\ll
x^{o(1)}SHFCB_0,
\]

\[
W_{\rm Ram}(g)
\ll
x^{o(1)}S^2H^2FB_0,
\]

and

\[
\boxed{
\begin{aligned}
W_{\rm spec}(g)
\ll{}&
T^{7/64}x^{o(1)}
\left(
1+\frac{C\sqrt F}{S^{3/2}H}
\right)^{7/32}\\
&\times
HS^2\sqrt F
\left(
FC^2+B_0CS^2+FCHS
\right)^{1/2}.
\end{aligned}
}
\]

**The correct third summand is \(FCHS\), not \(FHS\).**

Use this corrected form everywhere.

The actual proof claims

\[
\boxed{
\mathscr W_4
\ll
\Lambda^2
T_H(\omega)^{7/64}
N^2R^2S^3x^{-6\varepsilon}.
}
\]

The Fourier reference length is

\[
H_0=\frac{QR^2S^2}{M},
\]

with actual enlarged frequency range

\[
H\le\Lambda H_0,
\qquad
\Lambda\ll f x^{\varepsilon/100}.
\]

The phase \(T^{7/64}\) becomes \(T^{7/128}\) after the outer square root.

Do not assume the full analytic statement merely because an independent model audit reported PASS. Formalize it from available proved theorem(s), or keep the smallest genuine spectral analytic input explicit.

## 35. Short and degenerate cases

The source requires individual treatment of:

- \(H_{\max}<1\);
- bounded positive Fourier \(H\);
- \(H_0<1\) but actual \(H\ge1\);
- \(S=1\);
- \(R=1\);
- \(Q=1\);
- both high factors empty;
- short complementary or dual Poisson ranges.

Use actual Fourier decay or the actual positive-square estimates.

Do not claim that a factor equal to \(1\) automatically places the full modulus below the one-half barrier.

## 36. Final actual-atom estimate and normalization

The candidate stronger result is

\[
\boxed{
|\mathcal K_{A,f,c}|
\ll
f^{199/128}
\frac{N^2}{Qx^{2\varepsilon}}.
}
\]

A sufficient weaker bound is

\[
\boxed{
|\mathcal K_{A,f,c}|
\ll
f^{263/128}
\frac{N^2}{Qx^\varepsilon}.
}
\]

The physical reconstruction is

\[
\boxed{
F_{AA,\xi}^{\sharp}
=
\frac{M}{f_\xi}
\mathcal K_{A,f_\xi,c_\xi}.
}
\]

The first-Cauchy factor is

\[
\mathcal B_\xi\ll MQ(\log x)^C.
\]

Consequently the conservative bound yields

\[
\boxed{
\sqrt{
\mathcal B_\xi
|F_{AA,\xi}^{\sharp}|
}
\ll
\frac{x}{f_\xi}
f_\xi^{391/256}
x^{-\varepsilon/2}
(\log x)^C.
}
\]

Take

\[
f_\xi\le x^\sigma,
\qquad
\sigma\le\varepsilon/100,
\qquad
\frac{391}{256}\sigma<\frac{\varepsilon}{2}.
\]

Combined with the actual reciprocal packet norm, this is intended to give

\[
\sum_{\xi,\mathrm{cells}}
|\Gamma_\xi|
\sqrt{
\mathcal B_\xi|F_{AA,\xi}^{\sharp}|
}
=
o(\mathcal N_XI).
\]

Do not call this formally unconditional until the physical atom construction and the required analytic estimate have actual Lean proofs.

---

# PART X — FORMAL ANALYTIC IMPORTS

## 37. Investigate existing BV/SW Lean theorems

The public OpenAI mathematics repository includes the path

`lean/OAI/NumberTheory/PrimeGaps/Main.lean`

and declarations named

`OAI.LargePrimeGaps.siegelWalfisz`

and

`OAI.LargePrimeGaps.bombieriVinogradov`.

The source exhibits the latter as a consequence of the former.

Investigate those actual declarations:

1. pin the repository commit;
2. check compatible Lean/mathlib versions;
3. inspect their complete theorem types;
4. inspect transitive axioms;
5. construct the exact adapters for the physical #287 prime-progressions and interval counts.

Do not assume an imported theorem automatically matches the desired normalization, coefficient class or maximum-over-residues placement.

Do not confuse ordinary Bombieri–Vinogradov with divisor-weighted BDH or beyond-half Pascadi spectral estimates.

Do not use any alternate zero-free-zone declaration containing `sorry` as a proved theorem.

## 38. Separate the true analytic boundaries

The remaining external analytic statements may include:

- tiny-modulus Siegel–Walfisz;
- ordinary Bombieri–Vinogradov;
- divisor-weighted BDH;
- reciprocal/divisor-moment bounds;
- fundamental-lemma analytic mean estimates;
- Maynard's noncritical divisor-in-progressions bounds;
- the spectral \(Y\)/positive-\(W_4\) estimate;
- smooth Fourier decay and Poisson infrastructure;
- finite-tensor first/pair-moment asymptotics.

If these are already available in Lean, import and instantiate them.

If not, attempt genuine formal proofs where feasible.

Do not rename any of them as `VerifiedAnalyticInput` or another opaque instance.

---

# PART XI — REQUIRED FORMAL CONSTRUCTION ORDER

The intended work order is:

**A. Physical packet source**

Construct `PhysicalPacketIndex`, `physicalTailSource`, \(\Gamma_\xi\), \(f_\xi\), \(c_\xi\), \(b_{\xi,d}\), the exact scalar coefficient, and the literal pair-indexed remainder.

Prove the exact packet reindexing.

**B. Physical Ordering-B objects**

Construct `physicalOrderingBCells`, the actual Poisson profile, raw \(F_{AB}\), raw \(F_{AA}\), clean \(F_{AA}^{\sharp}\), and the correct zero-mode/mixed decomposition.

**C. Physical scale**

Construct `physicalFamilyScale` with \(X=M_*\) or the precisely proved physical scale relation and the actual main normalization \(\mathcal N_XI(F)\).

**D. Seven-block framework**

Specialize the already-proved prescribed-shape gcd compiler and construct the actual seven-block affine slopes and window.

Use the corrected one-sided moment interface.

**E. Physical actual-atom map**

Construct every real clean atom from the physical packet coefficients, not independently from arbitrary `CleanAtom` fields.

Prove exact source-to-positive-\(W_4\) mapping and the corrected quantitative ledger.

**F. Upstream source-specific obligations**

Eliminate remaining project-specific providers by proving the parity-sensitive full weight, support/range allocation, repaired six-variable routing, relative centering, packet multiplicity and cross-coprime partition placement.

**G. Deep analytic formalization**

Only after the physical constructions are established, discharge the remaining published analytic inputs where corresponding Lean proofs exist or can actually be constructed.

**H. Final theorem**

Attempt the concrete provider-free tail:

```lean
theorem Erdos287.SourceChain.Tail287 :
  Erdos287.CurrentTail.Tail287Statement := by
  ...
```

The exact existing canonical theorem type should be used.

No generic physical source, cell, framework, membership or analytic hypothesis may remain free.

---

# PART XII — TRUST AND STOP CONDITIONS

A successful compilation of

`Tail287_of_MinimalAnalyticProviders`

does not establish unconditional tail exclusion if the theorem still accepts mathematical hypotheses.

Likewise a clean `#print axioms` does not discharge local theorem arguments.

For the final declaration verify:

- the exact theorem statement;
- absence of free source/framework/analytic-provider hypotheses;
- absence of custom axioms;
- absence of `sorryAx`, `admit`, unsafe or native-evaluation trust assumptions;
- ordinary build;
- targeted kernel checking.

If a fresh aggregate checker is prohibitively memory-intensive, check changed modules individually and report that limitation accurately.

Re-run the previously interrupted negative controls.

The final output must distinguish:

**PHYSICAL SOURCE CONSTRUCTED**

The literal packet set, coefficients, residues, scalar weight, physical remainder, scale and cell structures have been constructed.

**PROJECT-SPECIFIC SOURCE CLOSED**

The seven-block framework, actual atom mapping, factor-range, parity, indexing and source routing have been proved, leaving only deep analytic inputs.

**DEEP ANALYTIC PROVIDERS REMAIN**

State their exact theorem types. Do not claim unconditionality.

**UNCONDITIONAL LEAN TAIL**

Use only when the actual physical theorem has no mathematical provider assumptions and passes the kernel checks.

If a formula genuinely remains absent from both this message and existing proved Lean declarations, identify that **exact missing mathematical formula** and the first theorem it blocks. Do not respond merely that a V-numbered document is absent.

The task is to construct and prove the actual mathematics now, not to prepare another inventory of unavailable manuscripts.

**Begin with the literal physical packet construction, its designated-pair indexing, and the true one-sided seven-block moment interface.**