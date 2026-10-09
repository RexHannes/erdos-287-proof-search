# The fixed-affine Chen transfer for W2.984

**Status line.** Erdős #287 remains open. This document proves the conditional asymptotic
statement W2.984 modulo the published analytic inputs listed in §0.3. The onset is
ineffective. No claim is made at the endpoint \(s = 2.984\). The referee verdict is not
claimed here; this is the text submitted for re-audit.

**Companion files.** `W2984_THEOREM.md` (statement), `MERIKOSKI_DICTIONARY.md` (line-by-line
dictionary), `W2984_FORMALIZATION_REPORT.md` (what Lean checks), `OPUS_REAUDIT_PACKET.md`
(what changed since the earlier `REPAIR` verdict). Lean: `RequestProject/Erdos287/W2984Publication/`.

**Primary sources used (read in full).**
* [M] J. Merikoski, *Limit points of normalized prime gaps*, arXiv:1811.03008v3. We use the
  v3 numbering: Lemma 13 = Chen's inequality, Lemma 14 = linear sieve, Lemmas 15/16/17 =
  \(S_1/S_2/S_3\), Proposition 8 = modified BV (BFM Thm 4.2), Proposition 11 = modified BV for
  almost-primes, Proposition 12 = the pair bound with constant \(3.99\), §6 = the correction
  (Lemmas 21–24).
* [BFM] W. Banks, T. Freiberg, J. Maynard, arXiv:1404.5094v2. Their v2 lemma numbers are
  Merikoski's minus one. In particular [BFM, Lemma 4.6(iii)] in v2 is the lemma Merikoski cites
  as "Lemma 4.7(iii)". Theorem 4.2 is the modified Bombieri–Vinogradov theorem.
* [PM] D.H.J. Polymath, arXiv:1407.4897v4, Lemma 4.1 (the Fourier evaluation of
  Maynard–Tao divisor sums).
* [FI] Friedlander–Iwaniec, *Opera de Cribro*, Chapters 11–12 (the linear sieve and the
  Buchstab function), and Tenenbaum, *Introduction to analytic and probabilistic number
  theory*, III.5, for \(\Psi(x,y) \ll x e^{-u/2}\).

---

## 0. Overview

### 0.1 What has to be shown

W3 (refereed `PASS`) runs the BFM/Maynard moment method on the *fixed affine* forms
\(L_i(t) = a_i t + 1\) produced by the #287 contact compiler. It uses the Selberg pair bound
[BFM, Lemma 4.6(iii)]: the constant \(4\), which gives width \(3\). W2.984 replaces \(4\) by
Merikoski's Chen-sieve constant \(\Omega_1-\Omega_2+\Omega_3 < 3.984\). The W3 downstream
machinery is reused unchanged, and the generic consumer in Lean shows that a per-pair constant
\(c_0\) gives every width \(s > c_0 - 1\). So the only new mathematics is:

> **Affine Proposition 12 (Theorem 11.1 below).** For the W3 framework data and every pair of
> distinct coordinates \(j \ne \ell\),
> \[ \sum_{t\in\mathcal T} w(t)\,1_{\mathbb P}(L_j(t))\,1_{\mathbb P}(L_\ell(t)) \le \bigl(\Omega_1-\Omega_2+\Omega_3 + C_{\rm err}\delta + o(1)\bigr)\,\mathfrak M .\]

### 0.2 Structure of the proof

| § | content | Merikoski v3 counterpart |
|---|---|---|
| 1 | setting, the inherited W3 inputs, the four admissibility facts | §5 set-up |
| 2 | affine Chen decomposition (corrected), with the square tail | Lemma 13 |
| 3 | the literal congruence system and CRT for the designated prime | inside Lemma 15 |
| 4 | small-prime square: exceptional set, smooth tail, overlap tail, Euler evaluation | §6 (Lemmas 21–24) |
| 5 | complete modulus ledger | (implicit in Lemmas 15–17) |
| 6 | Bombieri–Vinogradov inputs for the fixed non-squarefree base \(a_jW\) | Props 8, 11 |
| 7 | `AffineChenS1` | Lemma 15 + §6 |
| 8 | `AffineChenS2` (lower bound) | Lemma 16 + §6 |
| 9 | `AffineChenS3` (switched) | Lemma 17 |
| 10 | `AffineSquareTail` (new) | — |
| 11 | affine Proposition 12 | Prop 12 |
| 12 | the scalar constant \(< 3.984\) (kernel-checked) | numerics after Prop 12 |
| 13 | explicit \(O(\delta)\) budget | — |
| 14 | the W3 downstream and W2.984 | — |
| 15 | effectivity | — |

### 0.3 Classification of every input

* **Cited unchanged:** the linear sieve [FI, Thm 11.13 / M, Lemma 14]; the Buchstab asymptotic
  [FI, Lemma 12.1]; [BFM, Lemma 4.1] (the exceptional modulus); [BFM, Lemma 4.6(i),(ii)] and the
  pair normaliser (W3 inputs); the generalised Polymath lemma in [M, §6] (proved there by the
  argument of [PM, Lemma 4.1]); Shiu's divisor-moment bound in progressions; \(\Psi(x,y)\ll xe^{-u/2}\).
* **Cited, with the proof re-verified for our family of moduli:** [BFM, Thm 4.2] = [M, Prop 8], and
  [M, Prop 11]. The *statements* sum over all \(q\) with \(q_0\mid q\). Their published proofs
  factor the primitive conductor as \(q'=ab\) with \(a\mid q_0\), which is valid only when the
  \(q_0\)-part of \(q\) is squarefree. Our moduli \(a_jWm\) can be non-squarefree, so §6 rechecks
  every step with \(a\mid a_jW\) in place of \(a \mid q_0\). This is Lemma 6.1, which we
  classify as an **easy extension of the proof of a cited theorem**.
* **New in this document:** §2's correction of Lemma 13 together with the square tail (§10);
  the affine congruence system (§3); the affine forms of §6's four ingredients (§4); the
  switched source (§9); the bookkeeping that the affine main terms *equal* the shift main terms
  (Lemma 3.5); the treatment of the exceptional prime inside \(S_3\) (Remark 9.4); the ledger
  (§5); and the explicit \(\delta\)-budget (§13).

---

## 1. Setting

### 1.1 Parameters

Fix the W3 block geometry and a width \(s\). The W3 framework (W3 report; in Lean,
`W3FrameworkProvider`) provides, for each sufficiently large window, the following data.

* An integer \(K\) and slopes \(a_1,\dots,a_K\), which are **pairwise distinct** positive
  integers bounded by a constant \(H\) independent of the window (bounded-cofactor row rigidity).
* The size parameter \(X\to\infty\), and \(\mathcal T = \{t\in(T_1,T_2] : t\equiv t_0 \pmod W\}\)
  with \(T_2 \asymp T_2-T_1\) and \(\log L_i(t) = \log X + O_H(1)\) for \(t\in\mathcal T\).
* \(\epsilon>0\) small; the exceptional prime \(Z_{\rm exc}=Z_{X^{4\epsilon}}\) of [BFM, (4.8)]
  (equal to \(1\) if there is none). Here
  \(W=\prod_{p\le \epsilon\log X,\ p\ne Z_{\rm exc}}p\), so \(W = X^{\epsilon(1+o(1))}\), and
  \(B = \frac{\phi(W)}{W}\log X\).
* A residue \(t_0\) with \(\bigl(\prod_i (a_it_0+1), W\bigr)=1\). In W3, \(t_0=0\), and then
  \(L_i(t)\equiv 1 \pmod W\).
* Maynard weights \(\lambda_{d_1,\dots,d_K}\) of support \(\delta\) as in [M, (l1),(l2)]:
  \(\lambda_{\mathbf d} = \prod\mu(d_i)\sum_{J}\prod F_{\ell,J}(\log d_\ell/\log X)\). These are
  supported on \(\prod d_i \le X^\delta\) and \((d_1\cdots d_K, Z_{\rm exc})=1\), with
  \(|\lambda_{\mathbf d}|\ll 1\). Set \(w(t) = (\sum_{d_i\mid L_i(t)}\lambda_{\mathbf d})^2\).
* The **pair normaliser** \(\mathfrak M = \#\mathcal T\cdot B^{-K}L_K(F)\). In the shift setting
  this is Merikoski's \(\frac NW B^{-K}L_K(F)\).

Throughout, \(j\ne\ell\) are the designated coordinates. \(L_j\) is the *prime* coordinate and
\(L_\ell\) the *sifted* coordinate. Chen parameters:
\[ \alpha=\tfrac17,\quad \beta=\tfrac3{14},\quad Y = X^{\alpha},\quad Z=X^{\beta}, \qquad y=\exp((\log X)^{1/3}),\quad z_0 = X^{\delta^2}. \]
Fixed smallness: \(0<\delta\le \delta_{\max}\le 1/16\) and \(\epsilon\le\delta/8\). The
"sufficiently small \(\epsilon\)" of Lemma 6.1 is chosen after \(\delta\).

### 1.2 The spectator weight

\[ \nu(t) = \nu_{j\ell}(t) := \Bigl(\sum_{\substack{d_i\mid L_i(t)\ \forall i\\ d_j=d_\ell=1}}\lambda_{d_1,\dots,d_K}\Bigr)^2 \ \ge 0 . \]
Unlike [M], we do **not** put the factor \(1_{((n+h_j)(n+h_\ell),Z)=1}\) into \(\nu\). It is never
needed, and leaving it out avoids an inconsistency in the lower bound for \(S_2\) (Remark 8.3).

**Lemma 1.1 (replacement).** If \(L_j(t)\) and \(L_\ell(t)\) are both primes \(>X^{\delta}\), then \(w(t)=\nu(t)\).

*Proof.* If \(d_j\mid L_j(t)\) and \(d_j\le X^\delta<L_j(t)\), then \(d_j=1\). The same holds for
\(\ell\). ∎ (In Lean, this is the agreement field of `FrameworkWindowData`, used in
`pairExpect_eq_chenS`.)

So the W3 pair functional is
\(\mathcal S := \sum_{t\in\mathcal T}\nu(t)1_{\mathbb P}(L_j(t))1_{\mathbb P}(L_\ell(t))\), up to
\(O(X^{\delta})\) terms with a small prime value.

### 1.3 Admissibility facts (all elementary; kernel-checked in `AffineCRT.lean`)

Let \(q\) be a prime with \(q\nmid WZ_{\rm exc}\). Then \(q>\epsilon\log X > H\) for large \(X\).

* **(A1)** \(q\nmid a_i\) and \(q\nmid a_i-a_k\) for \(i\ne k\), since \(0<|a_i-a_k|<H<q\).
* **(A2) Distinct roots.** The roots \(-\bar a_i \bmod q\) of the \(L_i\) are pairwise distinct
  (`roots_distinct`). Hence **no prime \(q\nmid W\) divides two of the forms at the same \(t\)**:
  \(q\mid L_i(t), L_k(t) \Rightarrow q \mid a_kL_i(t)-a_iL_k(t) = a_k-a_i\) (`prime_dvd_two_forms`).
* **(A3)** If \(q\mid L_i(t)\), then \(q\nmid a_i\) (`prime_not_dvd_slope`).
* **(A4) Coprimality of divisors.** If \(d_i\mid L_i(t)\) and \(d_k\mid L_k(t)\) with \(i\ne k\)
  and \((d_id_k,W)=1\), then \((d_i,d_k)=1\) (`coprime_of_dvd_forms`). Also \(L_i(t)\) is coprime
  to \(W\) when \(t\equiv t_0\), so every divisor of \(L_i(t)\) is coprime to \(W\).

**Why these replace Merikoski's smoothness hypothesis.** [M, Prop 12] assumes
\(P^+(\prod(h_j-h_i))\le\epsilon\log N\). In the affine case the analogous quantity is
\(\prod_i a_i\prod_{i<k}(a_i-a_k)\). Its prime factors are \(\le H < \epsilon\log X\), so all of
them divide \(W\) (or equal \(Z_{\rm exc}\), which is impossible once \(Z_{\rm exc}>H\); this holds
for large \(X\) because \(Z_{\rm exc}\gg\log\log X\) by [BFM, Lemma 4.1]). Every later use of
"pairwise coprime" in [M] and [BFM] relies only on (A2)–(A4).

---

## 2. Affine Chen decomposition (Merikoski Lemma 13)

### 2.1 The literal pointwise inequality is false

Merikoski's proof of Lemma 13 reduces to the pointwise inequality [M, (sieve)]: for
\((n,P(Y))=1\),
\[ 1_{(n,P(Z))=1}\ \le\ 1 - \tfrac12 k(n) + \tfrac12 T(n),\qquad k(n)=\#\{Y<p\le Z: p\mid n\},\quad T(n)=\#\{Y<p<q<r\le Z,\ n=pqrs,\ (s,P(q))=1\}. \]
The proof says "there are \(k-2\) ways to choose \(r\)". This is correct for **squarefree**
\(n\), but fails when a band prime divides \(n\) to a higher power.

**Counterexample (kernel-checked, `merikoski_pointwise_fails`).** Take the sifting primes
\(\{2,\dots,19\}\), \(Y=4\), \(Z=20\), and \(n=1925=5^2\cdot7\cdot11\). Then \(n\) is
\(4\)-rough and \(k=3\). The only triple is \((5,7,11)\), with \(s=5\), and \((5,P(7))\ne 1\), so
\(T=0\). The right-hand side is \(1-\frac32+0=-\frac12<0=\) left-hand side. Positivity of the
weight does not rescue the summed form either: with weight \(1\), \(L_j=2\), \(L_\ell=1925\), the
literal Chen combination is \(-\frac12<0=S\) (`merikoski_weighted_fails`).

This is an *expository* gap with a trivial repair. In the actual range, the band primes exceed
\(X^{1/7}\), and \(p^2\mid L_\ell(t)\) for such \(p\) is very rare (§10).

### 2.2 The corrected pointwise inequality

Let \(\mathcal P\) be any finite set of primes; we use \(\mathcal P = \{p : p\ne Z_{\rm exc}\}\),
truncated at \(Z\), which gives Merikoski's \(P_0\). Write \(P_{\mathcal P}(w)=\prod_{p\in\mathcal P,\,p\le w}p\). Let
\[ \mathrm{band}(n) = \{p\in\mathcal P: Y<p\le Z,\ p\mid n\},\ k(n)=\#\mathrm{band}(n),\ \ \mathrm{sq}(n) := k(n)\cdot\#\{p\in\mathrm{band}(n): p^2\mid n\},\]
\[ T(n) = \#\{(p,q,r)\in\mathcal P^3: Y<p<q<r\le Z,\ pqr\mid n,\ (n/pqr, P_{\mathcal P}(q))=1\}. \]

**Lemma 2.1 (`chen_pointwise`).** For all \(n\ge1\) and \(Y\le Z\),
\[ 1_{(n,P_{\mathcal P}(Z))=1} \le 1_{(n,P_{\mathcal P}(Y))=1} - \tfrac12\,1_{(n,P_{\mathcal P}(Y))=1}\,k(n) + \tfrac12 T(n) + \tfrac12\,\mathrm{sq}(n). \]

*Proof.* If \((n,P_{\mathcal P}(Y))>1\), both sides are \(\ge 0\) and the left side is \(0\). So
assume \(n\) is \(\mathcal P\)-\(Y\)-rough.
* \(k=0\): \(n\) is \(Z\)-rough and both sides equal \(1\) (plus nonnegative terms).
* \(k\ge1\): the left side is \(0\).
  * If some band prime divides \(n\) squared, then \(\mathrm{sq}(n)\ge k\), and the right side is
    \(\ge 1-\frac k2+\frac k2>0\).
  * Otherwise every band prime divides \(n\) exactly once. If \(k\le2\), the right side is
    \(\ge 1-\frac k2\ge0\). If \(k\ge3\), let \(p_1<p_2\) be the two smallest band primes. For
    each of the \(k-2\) other band primes \(r\), the triple \((p_1,p_2,r)\) is counted. Indeed,
    \(s=n/(p_1p_2r)\) has no prime factor in \(\mathcal P\) that is \(\le p_2\): there are none
    \(\le Y\) by roughness, \(p_1,p_2\) divide \(n\) only once, and every other band prime exceeds
    \(p_2\). So \(T\ge k-2\) (`card_triples_ge`), and the right side is \(\ge 1-\frac k2+\frac{k-2}2=0\). ∎

The combinatorics never mentions shifts, slopes, or the residue class of \(n\). It is a statement
about one integer \(n\) and a set of primes. This is **exactly why Lemma 13 is independent of the
shift/affine setting**. It is applied to \(n=L_\ell(t)\) for each \(t\).

### 2.3 The weighted decomposition

Define, with \(\mathcal P\) as above (`chenS`, `chenS1`, `chenS2`, `chenS3`, `chenSsq`):
\[ \begin{aligned}
S &= \textstyle\sum_{t\in\mathcal T}\nu(t)1_{\mathbb P}(L_j(t))1_{\mathbb P}(L_\ell(t)),\\
S_1 &= \textstyle\sum_{t}\nu(t)1_{\mathbb P}(L_j(t))\,1_{(L_\ell(t),P_{\mathcal P}(Y))=1},\\
S_2 &= \textstyle\sum_{Y<p\le Z,\ p\in\mathcal P}\ \sum_{t:\ p\mid L_\ell(t)}\nu(t)1_{\mathbb P}(L_j(t))\,1_{(L_\ell(t),P_{\mathcal P}(Y))=1},\\
S_3 &= \textstyle\sum_{t}\nu(t)1_{\mathbb P}(L_j(t))\,T(L_\ell(t)),\qquad
S_{\rm sq} = \textstyle\sum_{t}\nu(t)1_{\mathbb P}(L_j(t))\,\mathrm{sq}(L_\ell(t)).
\end{aligned}\]

**Lemma 2.2 (affine Chen decomposition; `chen_weighted`, `affine_chen_weighted`).** If
\(\nu\ge0\) on \(\mathcal T\) and \(L_\ell(t)>Z\) on \(\mathcal T\), then
\[ S\le S_1-\tfrac12S_2+\tfrac12S_3+\tfrac12S_{\rm sq}. \]

*Proof.* For each \(t\): if \(L_\ell(t)\) is prime and \(>Z\), then it is \(\mathcal P\)-\(Z\)-rough,
so \(1_{\mathbb P}(L_\ell(t))\le 1_{(L_\ell(t),P_{\mathcal P}(Z))=1}\). Apply Lemma 2.1 with
\(n=L_\ell(t)\). **Positivity is used exactly here and only here:** we multiply the pointwise
inequality by \(\nu(t)1_{\mathbb P}(L_j(t))\ge0\). Then sum over \(t\). ∎

Ranges: \(Y=X^{1/7}\), \(Z=X^{3/14}\), and \(\beta<1/4\). So in \(S_3\),
\(s\gg X/(pqr)\ge X^{5/14}>q\), as in [M, Remark after Lemma 13]. Moreover \(k(n)\le 7\) for
\(n\le X^{1+o(1)}\), because band primes exceed \(X^{1/7}\). This bound is used in §8 and §10.

---

## 3. The literal congruence system for the designated prime

Fix \(t\in\mathcal T\) and write \(p=L_j(t)=a_jt+1\).

**Lemma 3.1 (transfer identity; `transfer_identity`, `dvd_form_iff`).**
\(a_jL_i(t) = a_ip + (a_j-a_i)\). Hence for any \(e\) with \((e,a_j)=1\):
\(e\mid L_i(t) \iff a_ip\equiv a_i-a_j \pmod e\). If also \((e,a_i)=1\), this is equivalent to
\(p\equiv 1-a_j\bar a_i \pmod e\).

**Lemma 3.2 (units; `coprime_of_dvd_form`, `base_residue_unit`).** For \(e\) coprime to
\(a_ia_j(a_i-a_j)\), the residue \(1-a_j\bar a_i\equiv (a_i-a_j)\bar a_i\) is a unit mod \(e\). The
base residue \(a_jt_0+1\) is a unit mod \(a_jW\). In particular, every residue arising below is
reduced. All moduli we use are built from primes \(q\nmid W\) and so satisfy the hypothesis by
(A1).

**Lemma 3.3 (complete modulus; `progression_iff`, `progression_surj`).**
\(t\equiv t_0\pmod W\iff p\equiv a_jt_0+1 \pmod{a_jW}\), and \(t\mapsto a_jt+1\) is a bijection
from \(\mathcal T\) onto \(\{p\in I_j: p\equiv a_jt_0+1 \ (a_jW)\}\), where
\(I_j=(a_jT_1+1,a_jT_2+1]\).

Consequently, fix a sieve divisor \(d\) (acting on \(L_\ell\)), spectator lcms
\(m_i=[d_i,d_i']\) for \(i\ne j,\ell\), and the small-prime-square divisor \(m_\ell'=[e,e']\)
(acting on \(L_\ell\)). If \(d\), \(m_\ell'\) and the \(m_i\) are pairwise coprime and coprime to
\(W\), the conditions
\[ t\in\mathcal T,\quad d\,m'_\ell\mid L_\ell(t),\quad m_i\mid L_i(t)\ (i\ne j,\ell) \]
are, **literally**, the system
\[ p\equiv a_jt_0+1 \ (\mathrm{mod}\ a_jW),\qquad p\equiv 1-a_j\bar a_\ell \ (\mathrm{mod}\ d\,m_\ell'),\qquad p\equiv 1-a_j\bar a_i\ (\mathrm{mod}\ m_i), \]
with \(p\in I_j\). By CRT this is **one** reduced class \(c\) modulo
\[ Q = a_jW\cdot d\cdot m_\ell'\cdot\textstyle\prod_{i\ne j,\ell}m_i . \]
If the moduli are **not** pairwise coprime, the system is **empty** for every \(t\) by (A2): a
common prime would divide two different forms.

**Lemma 3.4 (normalisation; `totient_mul_of_primeFactors_subset`).** Since
\(\mathrm{rad}(a_j)\mid W\) (all primes \(\le H<\epsilon\log X\) divide \(W\)),
\[ \phi(a_jW)=a_j\phi(W),\qquad \phi(Q)=a_j\phi(W)\phi(d)\phi(m'_\ell)\textstyle\prod\phi(m_i). \]
The hypothesis \(\mathrm{rad}(a_j)\mid W\) is necessary: \(\phi(3\cdot2)\ne3\phi(2)\)
(`totient_normalisation_needs_radical`).

**Lemma 3.5 (affine main terms equal shift main terms).** Let \(\pi(I_j)\) be the number of primes
in \(I_j\). By the prime number theorem, \(\pi(I_j)=(1+o(1))\,a_j(T_2-T_1)/\log X\). Hence
\[ \frac{\pi(I_j)}{\phi(Q)} = (1+o(1))\frac{T_2-T_1}{\phi(W)\log X}\cdot\frac1{\phi(d)\phi(m'_\ell)\prod\phi(m_i)} = (1+o(1))\,\#\mathcal T\cdot B^{-1}\cdot\frac1{\phi(d)\phi(m'_\ell)\prod\phi(m_i)}. \]
The slope \(a_j\) cancels exactly. This is Merikoski's expression
\(\frac{\pi(2N)-\pi(N)}{\phi(d)\phi(W)\prod\phi([d_i,d_i'])}\), with \(\frac NW\) replaced by
\(\#\mathcal T\). From here on, every main term in [M] is reproduced with \(\frac NW\mapsto\#\mathcal T\).

**Lemma 3.6 (local densities; `local_density_designated`, `overlap_empty`, `card_root_one`).** For a
prime \(q\nmid WZ_{\rm exc}\), among the \(q-1\) residues \(t \bmod q\) with \(L_j(t)\not\equiv0\),
exactly one has \(L_i(t)\equiv0\) (for \(i\ne j\)). None has \(L_i\equiv L_k\equiv0\) for
\(i\ne k\). So the conditional density of \(q\mid L_i\), given that \(L_j\) is prime, is exactly
\(1/(q-1)=1/\phi(q)\), the same as for shifts.

**Remark 3.7 (the inference that is *not* made).** The W2.99 argument failed by assigning
\(g(d)=1/\phi(d)\) to the sieve variable *after* conditioning on spectator divisors, including
the case where \(d\) shares primes with them. In that case the true conditional count is
\(0\), not \(1/\phi(d)\) times the unconditioned count. We never use a density: every main term
above is the exact CRT count of Lemma 3.3, and Lemma 3.6 is only the statement that this count
factorises. The non-coprime configurations are handled separately: they are empty (A2), or, for
the sieve variable against spectators, they are bounded by the overlap tail of §4.3. In Lean,
`reg1_spectator_density` exhibits a concrete case where the density inference gives a nonzero
value but the literal count is \(0\).

---

## 4. The small-prime square (affine version of Merikoski §6)

Define \(P_0(w)=\prod_{p\le w,\ p\ne Z_{\rm exc}}p\) and \(P_0(y,Y)=\prod_{y<p\le Y,\ p\ne Z_{\rm exc}}p\).
Let \(H:[0,\infty)\to[0,1]\) be smooth, with \(H=1\) on \([0,\delta^2]\) and support in
\([0,2\delta^2]\). Put \(\delta_e=\mu(e)H(\log e/\log X)\) and
\[ \rho(v) = \Bigl(\sum_{e\mid (v,P_0(y))}\delta_e\Bigr)^2\ \ge 0 . \]
Every \(e\) with \(\delta_e\ne0\) satisfies \(e\le X^{2\delta^2}\), so \([e,e']\le X^{4\delta^2}\).
Since \(L_\ell(t)\) is coprime to \(W\), only \(e\) coprime to \(W\) occur.

### 4.1 Exceptional-set lemma

**Lemma 4.1.** For every \(v\ge1\),
\[ 0\ \le\ \rho(v) - 1_{(v,P_0(y))=1}\ \le\ \tau(v)^2\,\psi(v),\qquad \psi(v) = 1_{\exists\, e\mid v:\ e\mid P_0(y),\ z_0\le e\le yz_0}. \]

*Proof.* Let \(g=(v,P_0(y))\). If \(g=1\), then \(\rho(v)=H(0)^2=1\). Suppose \(g>1\), so the
indicator is \(0\) and \(\rho(v)\ge0\).
* If every divisor \(e\mid g\) has \(e\le z_0\), then \(H(\log e/\log X)=1\) for all of them, and
  \(\rho(v)=(\sum_{e\mid g}\mu(e))^2=0\).
* Otherwise some divisor of \(g\) exceeds \(z_0\). Multiply the prime factors of \(g\) (all
  \(\le y\)) together one at a time until the product first exceeds \(z_0\). The result is a
  divisor of \(g\) in \([z_0, yz_0]\), so \(\psi(v)=1\). In this case
  \(\rho(v)\le(\sum_{e\mid v}1)^2=\tau(v)^2\). ∎

So the **exceptional configurations** are exactly those \(v\) whose \(y\)-smooth part (excluding
\(Z_{\rm exc}\)) exceeds \(z_0\); they force a \(y\)-smooth divisor in \([z_0,yz_0]\). For upper
bounds we only use \(1_{(v,P_0(y))=1}\le\rho(v)\). For the lower bound (\(S_2\)) we use the
two-sided statement.

### 4.2 Smooth-divisor tail

**Lemma 4.2.** Uniformly for the framework data,
\[ \mathcal E := \sum_{t\in\mathcal T}\psi(L_\ell(t))\,\tau(L_\ell(t))^2\,\nu(t) \ \ll_{K,\delta,H}\ \#\mathcal T\,(\log X)^{O_K(1)}\exp\Bigl(-\tfrac{\delta^2}{6}(\log X)^{2/3}\Bigr). \]

*Proof.* By Hölder,
\(\mathcal E^3\le\bigl(\sum_t\tau(L_\ell(t))^6\bigr)\bigl(\sum_t\nu(t)^3\bigr)\bigl(\sum_t\psi(L_\ell(t))\bigr)\).

* We have \(\nu(t)\ll\prod_{i}\tau(L_i(t))^2\), since \(|\lambda|\ll1\) and the number of divisor
  tuples is \(\le\prod\tau(L_i(t))\).
* Shiu's theorem for divisor moments in progressions (modulus \(a_iW\le X^{2\epsilon}\)),
  combined with Hölder over the \(K\) forms, gives \(\sum_t\tau(L_\ell(t))^6\) and
  \(\sum_t\nu(t)^3\) both \(\ll\#\mathcal T(\log X)^{O_K(1)}\).
* For the last factor:
  \[\sum_t\psi(L_\ell(t))\le\sum_{\substack{z_0\le e\le yz_0\\ e\mid P_0(y),\,(e,W)=1}}\#\{t\in\mathcal T: e\mid L_\ell(t)\}.\]
  For \((e,a_\ell W)=1\), the condition \(e\mid a_\ell t+1\) is one class mod \(e\), compatible
  with \(t\equiv t_0 \ (W)\) by CRT. So the count is \(\le\#\mathcal T/e+1\). Hence
  \[\sum_t\psi\le\#\mathcal T\sum_{\substack{z_0\le e\le yz_0\\ P^+(e)\le y}}\frac1e+yz_0.\]
* Split \(e\) dyadically, \(e\sim u\) with \(u\in[z_0,yz_0]\), into \(O((\log X)^{1/3})\) ranges.
  On each range use \(\Psi(u,y)\ll u\,e^{-v/2}\) with \(v=\log u/\log y\ge \delta^2\log X/(\log X)^{1/3}=\delta^2(\log X)^{2/3}\)
  (Tenenbaum III.5, Thm 1). This gives
  \[\sum_t\psi\ll\#\mathcal T(\log X)^{1/3}e^{-\delta^2(\log X)^{2/3}/2}+X^{\delta^2+o(1)}.\]
* The second term is \(\le\#\mathcal T X^{-1/2}\).

Taking cube roots gives the claim. ∎

This is \(\ll_C\mathfrak M(\log X)^{-C}\) for every \(C\), since
\(\mathfrak M\gg\#\mathcal T(\log X)^{-K}\). The exponent is
\(\exp(-c\delta^2(\log X)^{2/3})\). Merikoski writes \(\exp(-\log^{1/2}N)\); either is negligible.
The exponent we actually use is the displayed one.

### 4.3 Spectator-overlap tail

The linear-sieve remainder for \(S_1\) (and \(S_2\)) contains, for each sieve divisor
\(d\mid P_0(y,Y)\), the terms
\(g(d)\cdot\#\{t: [e,e']\mid L_\ell(t),\ [d_i,d_i']\mid L_i(t)\}\) in which
\(c:=(d,\prod_i[d_i,d_i'])>1\). For these terms the first count in \(r_d\) is empty but the second
is not; this is the Benatar issue [M, §6].

**Lemma 4.3.** Every prime factor of such a \(c\) exceeds \(y\), and the total contribution of
these configurations satisfies
\[ \mathcal O := \sum_{\substack{d<D_0\\ d\mid P_0(y,Y)}}g(d)\sum_{\substack{c\mid d\\ c>1}}\sum_{i\ne j,\ell}\ \sum_{\substack{t\in\mathcal T\\ c\mid L_i(t)}}\tau(L_\ell(t))^2\Bigl(\sum_{d_i\mid L_i(t)}|\lambda_{\mathbf d}|\Bigr)^2\ \ll\ \frac{\#\mathcal T\,(\log X)^{O_K(1)}}{y^{1/2}} . \]

*Proof.* Since \(d\mid P_0(y,Y)\), every prime of \(d\), and so of \(c\), lies in \((y,Y]\); hence
\(c>y\). For a single \(c\), Cauchy–Schwarz gives
\[\sum_{t:\,c\mid L_i(t)}\Lambda^*(t)\le\Bigl(\sum_t\Lambda^*(t)^2\Bigr)^{1/2}\#\{t\in\mathcal T:c\mid L_i(t)\}^{1/2},\qquad \Lambda^*(t)=\tau(L_\ell(t))^2\Bigl(\sum_{d_i\mid L_i(t)}|\lambda|\Bigr)^2 .\]
* As in §4.2, \(\sum\Lambda^{*2}\ll\#\mathcal T(\log X)^{O(1)}\).
* By (A1), \((c,a_iW)=1\), so the count is \(\le\#\mathcal T/c+1\le 2\#\mathcal T/c\), using \(c\le D_0<\#\mathcal T\).

Hence the inner sum is \(\ll\#\mathcal T(\log X)^{O(1)}c^{-1/2}\). Now
\[\sum_{d\mid P_0(y,Y)}g(d)\sum_{c\mid d,\ c>1}c^{-1/2}\le\prod_{y<q\le Y}(1+g(q))\cdot\sum_{\substack{c>1\\ P^-(c)>y,\ \mu^2(c)=1}}g(c)c^{-1/2}.\]
The first factor is \(\ll\log X\) by Mertens. For the second, \(g(c)c^{-1/2}\le\prod_{q\mid c}2q^{-3/2}\), so
\[\sum_{c}\ \le\ \exp\Bigl(\sum_{q>y}2q^{-3/2}\Bigr)-1\ \ll\ y^{-1/2}. \]
∎

So the exponent is \(y^{-1/2}=\exp(-\frac12(\log X)^{1/3})\), as in Merikoski's
\(N\log^{O(1)}N/(Wy_1^{1/2})\). It is **not changed**. It is
\(\ll_C\mathfrak M(\log X)^{-C}\).

(Overlap of the sieve divisor with \([e,e']\) is impossible, since \(d\mid P_0(y,Y)\) and
\(e\mid P_0(y)\). Overlap of \([e,e']\) with a spectator \([d_i,d_i']\), \(i\ne\ell\), makes both
counts empty by (A2), because \(d_\ell=1\) in \(\nu\) and \(e\mid L_\ell\). Overlap of two
spectators makes both counts empty by (A2). So Lemma 4.3 covers the **only** asymmetric case.)

### 4.4 Euler evaluation

**Lemma 4.4.** Uniformly for the framework data,
\[ \mathcal X := \sum_{t\in\mathcal T}1_{\mathbb P}(L_j(t))\,\rho(L_\ell(t))\,\nu(t) = (1+o(1))\prod_{\substack{\epsilon\log X<q\le y\\ q\ne Z_{\rm exc}}}\Bigl(1-\frac1q\Bigr)\cdot\#\mathcal T\,B^{-K+1}L_K(F). \]

*Proof.* Expand both squares:
\[\mathcal X=\sum_{e,e'}\delta_e\delta_{e'}\sum_{\substack{\mathbf d,\mathbf d'\\ d_j=d_j'=d_\ell=d_\ell'=1}}\lambda_{\mathbf d}\lambda_{\mathbf d'}\ \#\{t\in\mathcal T: L_j(t)\in\mathbb P,\ [e,e']\mid L_\ell(t),\ [d_i,d_i']\mid L_i(t)\}.\]
**The pairwise-coprimality restriction comes for free.** The moduli \([e,e']\) (on coordinate
\(\ell\)) and \([d_i,d_i']\) (on coordinates \(i\ne j,\ell\)) all sit on *different* affine forms,
and all of them are coprime to \(WZ_{\rm exc}\). So by (A2), if two of them share a prime, the
count is \(0\). The sum therefore equals the restricted sum \(\sum'\) of [M, §6, generalised
Polymath lemma], with the restriction "\([e,e'],[d_1,d_1'],\dots,WZ\) pairwise coprime".

On \(\sum'\), Lemmas 3.3–3.5 give
\[\#\{\cdots\}=\frac{\pi(I_j)}{\phi(a_jW)}\cdot\frac1{\phi([e,e'])\prod_i\phi([d_i,d_i'])}+O(E_j(m)),\qquad m=[e,e']\prod_i[d_i,d_i'],\]
where \(E_j\) is the error of §6. **Local factors.** For each prime \(q\nmid WZ_{\rm exc}\), the
weight of the configuration "\(q\) divides the modulus of coordinate \(i\)" is \(1/\phi(q)\)
(Lemma 3.6). At most one coordinate can carry \(q\). The roots of the two designated forms play
these roles:
* the root of \(L_j\) is excluded by the primality of \(L_j(t)\);
* the root of \(L_\ell\) carries only the \(e\)-variable (since \(d_\ell=1\)).

So the Euler product is precisely the one in the generalised Polymath lemma with
\(k=K-2\) spectator coordinates and one extra coordinate \(e\mid P_0(y)\), in its \(\phi\)-version.
That lemma (with \(F_0=G_0=H\), \(H(0)=1\)) gives
\[(c+o(1))B^{-(K-2)}\prod_{\epsilon\log X<q\le y,\ q\ne Z}(1-1/q),\]
with \(c\) the same product of one-dimensional integrals as in [BFM, Lemma 4.6]. Combining
this with \(\pi(I_j)/\phi(a_jW)=(1+o(1))\#\mathcal TB^{-1}\) (Lemma 3.5) gives the main term, as
in [M, (mainevaluation)], with \(\frac NW\mapsto\#\mathcal T\).

**Error.** The total error is \(\ll\sum_{m}\tau_{2K+2}(m)E_j(m)\), with \(m\le X^{2\delta+4\delta^2}\).
This is \(\ll\mathfrak M(\log X)^{-C}\) by Cauchy–Schwarz and Lemma 6.1, exactly as in §7.3. ∎

---

## 5. Complete modulus ledger

The modulus seen by Bombieri–Vinogradov in the \(S_1\) remainder is
\(Q=a_jW\cdot d\cdot[e,e']\cdot\prod_{i\ne j,\ell}[d_i,d_i']\). In \(S_2\), \(d\) is replaced by
\(pd\) with \(pd\le D_0\). Each divisor coordinate appears **exactly once**:

| source | variable | bound | exponent of \(X\) |
|---|---|---|---:|
| linear-sieve divisor (\(S_1\)); \(p\cdot d\) (\(S_2\)) | \(d\) | \(d<D_0=X^{1/2-4\delta}\) | \(1/2-4\delta\) |
| spectator lcms | \(\prod_{i\ne j,\ell}[d_i,d_i']\) | \(\le\prod d_i\prod d'_i\le X^{2\delta}\) | \(2\delta\) |
| small-prime-square divisor 1 | \(e\) | \(e\le X^{2\delta^2}\) | \(2\delta^2\) |
| small-prime-square divisor 2 | \(e'\) | \(e'\le X^{2\delta^2}\) | \(2\delta^2\) |
| fixed base | \(a_jW\) | \(\le HX^{\epsilon(1+o(1))}\) | \(\epsilon_W\le\epsilon+o(1)\) |
| **total** | | | \(1/2-2\delta+4\delta^2+\epsilon_W\) |

(`ModulusLedger.lean`: `ledger_card` (five sources), `totalS1_eq`.) Moreover:

* \(\frac12-2\delta+4\delta^2<\frac12\) for \(0<\delta<\frac12\) (`v92_core_lt_half`).
* For \(0<\delta\le\frac18\) and \(\epsilon_W\le\delta/2\), the total is \(\le\frac12-\delta\)
  (`totalS1_le`). Bombieri–Vinogradov is therefore applied at level \(\theta=\frac12-\delta\), with
  room to spare.
* Dropping the two square divisors does **not** give the same exponent (`totalS1_ne_without_square`).
  So the two new populations are really charged.
* \(S_3\) ledger: \([e,e']\le X^{1/2-4\delta}\) (Selberg support \(\frac14-2\delta\) each),
  spectators \(X^{2\delta}\), base \(a_\ell W\). The total is \(\frac12-2\delta+\epsilon_W\le\frac12-\delta\)
  (`totalS3_eq`, `totalS3_le`).
* In the \(S_2\) Cauchy–Schwarz step Merikoski uses \(q\le N^{1/2-2\delta}\) (sieve and spectators
  only). Our version is \(q\le X^{1/2-2\delta+4\delta^2}\), times the base. This is the V92 budget
  \(D_0X^{2\delta+4\delta^2}=X^{1/2-2\delta+4\delta^2}\).

---

## 6. Bombieri–Vinogradov for the fixed base \(a_jW\)

For a fixed index \(j\) and squarefree \(m\) with \((m,WZ_{\rm exc})=1\), define
\[ E_j(m)=\max_{(c,a_jWm)=1}\Bigl|\pi(I_j;a_jWm,c)-\frac{\pi(I_j)}{\phi(a_jWm)}\Bigr|. \]
Define \(\widetilde E_\ell(m)\) in the same way, for a sequence \((\mathfrak a_x)\) of the shape in
[M, Prop 11], on the interval \(I_\ell\) with base \(a_\ell W\).

**Lemma 6.1 (BV with bounded non-squarefree base).** Fix \(C>0\), \(H\) and \(\delta>0\). If
\(\epsilon\) is small enough in terms of \(C,\delta\) and the constant of [BFM, Lemma 4.1], then
uniformly in \(1\le a\le H\):
\[ \sum_{\substack{m\le X^{1/2-\delta}/(aW)\\ \mu^2(m)=1,\ (m,WZ_{\rm exc})=1}}\ \max_{(c,aWm)=1}\Bigl|\psi(x;aWm,c)-\frac{\psi(x)}{\phi(aWm)}\Bigr|\ \ll_{C,\delta,H}\ \frac{x}{\phi(W)(\log x)^C}\qquad(x\asymp X). \]
The same holds with \(\Lambda\) replaced by \(\Lambda_0=f\ast g\) of [M, (p0)], with fixed
\(0<\alpha_0<\frac12\), \(f(m)=1_{\mathbb P}(m)\log m\,1_{m\le A_1}\), \(|g|\ll1\),
\(g(n)\ne0\Rightarrow P^-(n)\ge X^{\alpha_0},\ n\asymp X/A_1\), and
\(X^{\alpha_0}\ll A_1\ll X^{1-\alpha_0}\). The maximum over residues is **inside** the sum over
\(m\).

*Status.* The *statements* of [BFM, Thm 4.2] and [M, Prop 11], with \(q_0=W\) (squarefree,
\(W<X^{2\epsilon}\), \(P^+(W)\le\epsilon\log X\)), sum over **all** \(q\le x^{1/2-\delta}\) with
\(W\mid q\) and \((q,Z)=1\), squarefree or not. Our moduli \(q=aWm\) are of this kind: distinct
\(m\) give distinct \(q\), and all terms are nonnegative, so our sum is a subsum
(`reindex_fixed_base`). Lemma 6.1 would therefore follow from the statements as printed. However,
both published proofs write the primitive conductor as \(q'=ab\) with \(a\mid q_0\) "(we are
supposing \(q_0\) is squarefree)", and this factorisation can fail when \(p^2\mid q\) for some
\(p\mid q_0\). For example, \(a_j=4\), \(2\mid W\) and a character of conductor \(8\) mod
\(4W\) (`switched_modulus_not_squarefree`, `reg5_nonsquarefree`). We therefore **re-verify the proof
for our family**. This is the only modification.

*Proof (modifications to [BFM, proof of Thm 4.2], line by line).* Let \(\chi\) mod \(q=aWm\) be
induced by the primitive \(\chi'\) mod \(q'\). Write \(q'=a'b\), where \(a'\) is the
\(W\)-smooth part of \(q'\) and \((b,W)=1\). Since \((m,W)=1\), we have \(a'\mid aW\) and
\(b\mid m\).

1. *Imprimitive correction.* Replacing \(\chi\) by \(\chi'\) costs
   \(\sum_q\phi(q)^{-1}\sum_\chi\sum_{(n,q)>1,\,n\le x}\Lambda(n)\ll x^{1/2}(\log x)^2\), unchanged.
2. *Principal character.* \(\psi(x,\chi_0')=\psi(x)\). This is the subtracted main term, unchanged.
3. *Extraction of \(1/\phi(W)\).*
   \(\sum_{q=aWm:\ q'\mid q}\frac1{\phi(q)}\le\frac1{\phi(aW)}\sum_{m:\ b\mid m}\frac1{\phi(m)}\ll\frac{\log x}{a\,\phi(W)\phi(b)}\),
   using \(\phi(aW)=a\phi(W)\) (Lemma 3.4). [BFM] has \(\frac{\log N}{\phi(q_0)}\sum_{a\mid q_0}\);
   we get \(\frac{\log x}{\phi(W)}\sum_{a'\mid aW}\). The only change is the range of the
   conductor's \(W\)-part: \(a'\le HW\) instead of \(a'\le W\).
4. *Large conductors (zero-density).* Montgomery's bound
   \(N^*(\sigma,A,B,T)\ll(A^2B^2T)^{3(1-\sigma)/(2-\sigma)}(\log ABT)^9\) counts zeros of
   **all** primitive characters of modulus \(\le4AB\). So it is unaffected by the restriction on
   \(a'\). The constraint \(\log(A^6B^2)\le(1-\delta)\log x\) becomes
   \(\log(H^6W^6B^2)\le(2\theta+12\epsilon)\log x+O(1)\le(1-\delta)\log x\) for \(\epsilon\le\delta/24\).
5. *Small conductors (Siegel–Walfisz-type region, [BFM, Lemma 4.1]).* The remaining range has
   \(B,n<(\log x)^{2C'}\). For \(q'=a'b\) we have \(q'\le HW(\log x)^{2C'}<x^{2\epsilon}\) and
   \(P^+(q')\le\max(\epsilon\log x,(\log x)^{2C'})<x^{2\epsilon/\log_2x^{2\epsilon}}\). Also
   \((q',Z_{\rm exc})=1\), because the primes of \(a'\) divide \(aW\), and \(Z_{\rm exc}\nmid W\),
   \(Z_{\rm exc}>H\). So the zero-free region applies verbatim. **This is the ineffective step**
   (Siegel's theorem enters through [BFM, Lemma 4.1]'s treatment of the excluded modulus).
6. *Roughness/almost-primes ([M, Prop 11]).* The terms \(h_2(n,d)=1_{(n,d)>1}\) use only
   \(P^-(n)\ge X^{\alpha_0}\) and \(f\) supported on primes. The case \(i=j=1\) uses Lemma `char`,
   which is step 3–5 above with \(a'\mid aW\). The large-\(B\) case uses the multiplicative large
   sieve (all moduli \(\le AB\)). The small-\(B\) case uses \(AB<x^{2\epsilon}<A_1^{1/2-\delta}\).
   None of these uses squarefreeness of \(a'\); only \(a'\le HW\) is used.
7. *Nonsquarefree modulus.* Only through \(a'\mid aW\). We never replace \(aW\) by its radical:
   the progression \(x\equiv1\ (a_\ell W)\) is not a union of classes mod \(\mathrm{rad}(a_\ell)W\)
   with the same weight. `reg5_nonsquarefree` records \(\phi(4\cdot2)\ne\phi(2\cdot2)\).
8. *Fixed base progression.* This is handled by the re-indexing \(q=aWm\) and step 3.
9. *Maximum over reduced residues.* As in [BFM], the maximum is taken inside, after the character
   expansion (\(|\bar\chi(c)|\le1\)).

Partial summation transfers the statement from \(\psi\) to \(\pi\) on the interval \(I_j\),
with \(\pi(I_j)/\phi(q)\) as main term. ∎

---

## 7. `AffineChenS1` (affine Merikoski Lemma 15, with the §6 repair)

**Lemma 7.1 (`AffineChenS1`).** There is \(C_1\ge0\), independent of \(X\), the window, \(K\),
\(\mu_0\), \(\eta_0\) and \(\delta\le\delta_{\max}\), such that for every \(\varepsilon>0\) and all
large \(X\):
\[ S_1\le\Bigl(\Omega_1+C_1\delta+\varepsilon\Bigr)\mathfrak M,\qquad \Omega_1=\frac{F_{\rm lin}(1/(2\alpha))}{\alpha e^\gamma}=\frac{7F_{\rm lin}(7/2)}{e^\gamma}. \]
One may take \(C_1=392/9\).

*Proof.*

**7.1 Small-prime split.** Write
\(1_{(n,P_0(Y))=1}=1_{(n,P_0(y))=1}1_{(n,P_0(y,Y))=1}\le\rho(n)1_{(n,P_0(y,Y))=1}\) (Lemma 4.1,
left inequality). So \(S_1\le S_1'\), where
\[S_1'=\sum_t a_t1_{(L_\ell(t),P_0(y,Y))=1},\qquad a_t=1_{\mathbb P}(L_j(t))\rho(L_\ell(t))\nu(t)\ \ge0.\]
**Positivity:** \(a_t\ge0\) because \(\nu\ge0\) and \(\rho\ge0\). This is required by the linear sieve.

**7.2 Linear sieve (upper bound).** Sift \(\{L_\ell(t)\}\) by the primes of \(P_0(y,Y)\). For
squarefree \(d\mid P_0(y,Y)\) define
\[\textstyle\sum_{t:\,d\mid L_\ell(t)}a_t=g(d)\mathcal X+r_d,\qquad g(q)=\frac1{q-1}\ (y<q\le Y,\ q\ne Z_{\rm exc}),\]
with \(g=0\) at other primes and \(\mathcal X\) as in Lemma 4.4. The dimension condition of
[M, Lemma 14] holds by Mertens, with \(L\ll1\). Take level \(D_0=X^{1/2-4\delta}\) and
\(s=\log D_0/\log Y=7/2-28\delta\). Then
\[S_1'\le\bigl(F_{\rm lin}(7/2-28\delta)+O(\log^{-1/6}D_0)\bigr)\,\mathcal X\,V+\sum_{d<D_0,\ d\mid P_0(y,Y)}|r_d|,\qquad V=\prod_{y<q\le Y,\ q\ne Z}\Bigl(1-\frac1{q-1}\Bigr).\]

**7.3 Main term.** By Lemma 4.4, using
\(\prod_{y<q\le Y}(1-\frac1{q-1})(1-\frac1q)^{-1}=1+O(1/y)\), and since excluding \(Z_{\rm exc}\)
changes products by \(1+O(1/Z_{\rm exc})=1+o(1)\),
\[\mathcal XV=(1+o(1))\prod_{\epsilon\log X<q\le Y}\Bigl(1-\frac1q\Bigr)\#\mathcal TB^{-K+1}L_K=(1+o(1))\frac{W}{\phi(W)}\frac{1}{e^\gamma\alpha\log X}\#\mathcal TB^{-K+1}L_K=\frac{1+o(1)}{\alpha e^\gamma}\mathfrak M.\]
The main term is therefore \(\frac{F_{\rm lin}(7/2-28\delta)+o(1)}{\alpha e^\gamma}\mathfrak M\). On
\([3,7/2]\) we have \(F_{\rm lin}'=(f_{\rm lin}(s-1)-F_{\rm lin}(s))/s\) with
\(0\le f_{\rm lin}\le F_{\rm lin}\le 2e^\gamma/3\), so \(|F_{\rm lin}'|\le 2e^\gamma/9\). Hence
\(\frac{7}{e^\gamma}F_{\rm lin}(7/2-28\delta)\le\Omega_1+\frac{7}{e^\gamma}\cdot28\delta\cdot\frac{2e^\gamma}9=\Omega_1+\frac{392}9\delta\).

**7.4 Remainder — all terms.** Expand \(\rho\) and \(\nu\) in \(r_d\):
\[r_d=\sum_{e,e'}\delta_e\delta_{e'}\sum_{\mathbf d,\mathbf d'}\lambda\lambda'\Bigl(\#\{t: L_j\in\mathbb P,\ d[e,e']\mid L_\ell,\ [d_i,d_i']\mid L_i\}-g(d)\#\{t: L_j\in\mathbb P,\ [e,e']\mid L_\ell,\ [d_i,d_i']\mid L_i\}\Bigr).\]
Classify the configurations \((d,e,e',\mathbf d,\mathbf d')\):

| configuration | first count | second count | treatment |
|---|---|---|---|
| (a) \(d,[e,e'],[d_i,d_i']\) pairwise coprime | CRT, Lemma 3.3 | CRT | \(\le E_j(m)+E_j(m/d)/\phi(d)\), with \(g(d)=1/\phi(d)\) exactly |
| (b) \((d,[e,e'])>1\) | — | — | impossible: \(d\mid P_0(y,Y)\), \(e\mid P_0(y)\) |
| (c) \(([e,e'],[d_i,d_i'])>1\) | 0 | 0 | (A2): one prime would divide \(L_\ell\) and \(L_i\) |
| (d) \((d,[d_i,d_i'])>1\) | 0 | \(\ne0\) | Lemma 4.3 (overlap tail) |
| (e) \(([d_i,d_i'],[d_k,d_k'])>1\) | 0 | 0 | (A2) |

In (a), \(m=d[e,e']\prod[d_i,d_i']\) is squarefree, coprime to \(WZ_{\rm exc}\), and
\(a_jWm\le X^{1/2-\delta}\) (§5). The number of representations of \(m\) is \(\le\tau_{2K+2}(m)\), and
\(|\delta_e|\le1\), \(|\lambda|\ll1\). So
\[\sum_d|r_d|\ll\sum_m\tau_{2K+2}(m)E_j(m)+\log X\sum_{m}\tau_{2K+2}(m)E_j(m)+\mathcal O.\]
Using the trivial bound \(E_j(m)\ll X/(a_jWm)+1\) and Cauchy–Schwarz,
\[\sum_m\tau E_j\le\Bigl(\sum_m\tau^2(X/\phi(a_jWm)+1)\Bigr)^{1/2}\Bigl(\sum_mE_j(m)\Bigr)^{1/2}\ll\Bigl(\frac{X(\log X)^{O(1)}}{\phi(W)}\Bigr)^{1/2}\Bigl(\frac{X}{\phi(W)(\log X)^{C'}}\Bigr)^{1/2}\]
by Lemma 6.1. With \(C'\) large this is \(\ll\mathfrak M(\log X)^{-C}\), since
\(X/\phi(W)\ll\#\mathcal T\,(\log X)\) and \(\mathfrak M\gg\#\mathcal T(\log X)^{-K}\). Lemma 4.3
gives \(\mathcal O\ll\mathfrak M(\log X)^{-C}\). ∎

---

## 8. `AffineChenS2` (affine Merikoski Lemma 16; lower bound)

**Lemma 8.1 (`AffineChenS2`).** There is \(C_2\ge0\) with the same uniformity such that for every
\(\varepsilon>0\) and all large \(X\):
\[ S_2\ \ge\ \Bigl(2\Omega_2-C_2\delta-\varepsilon\Bigr)\mathfrak M,\qquad 2\Omega_2=\frac1{\alpha e^\gamma}\int_\alpha^\beta f_{\rm lin}\Bigl(\frac{1/2-u}{\alpha}\Bigr)\frac{du}u . \]
One may take \(C_2=196\log(3/2)\).

*Proof.* **Every step is a lower bound, or an asymptotic used two-sidedly. No absolute value
replaces a signed quantity in the main term.**

**8.1 Definition.**
\(S_2=\sum_{Y<p\le Z,\ p\ne Z_{\rm exc}}S_{2,p}\), where
\(S_{2,p}=\sum_{t:\,p\mid L_\ell(t)}\nu(t)1_{\mathbb P}(L_j(t))1_{(L_\ell(t),P_0(Y))=1}\). (Since
\(Z_{\rm exc}\le X^{4\epsilon}<Y\), the restriction \(p\ne Z_{\rm exc}\) is vacuous.)

**8.2 Small-prime split, two-sided.** By Lemma 4.1,
\(1_{(n,P_0(y))=1}=\rho(n)-\bigl(\rho(n)-1_{(n,P_0(y))=1}\bigr)\), where the bracket lies in
\([0,\tau(n)^2\psi(n)]\). Hence
\[S_2\ \ge\ S_2'-\sum_t k(L_\ell(t))\,\tau(L_\ell(t))^2\psi(L_\ell(t))\,\nu(t)\ \ge\ S_2'-7\mathcal E,\]
using \(k\le7\) and \(1_{\mathbb P}\le1\). Here
\(S_2'=\sum_p\sum_{t:\,p\mid L_\ell}a_t1_{(L_\ell,P_0(y,Y))=1}\) with \(a_t\ge0\) as in §7. We
subtract a nonnegative quantity with an upper bound, so the direction is correct. Lemma 4.2 gives
\(7\mathcal E\ll\mathfrak M(\log X)^{-C}\).

**8.3 CRT source for fixed \(p\).** Since \(p>Y=X^{1/7}>X^\delta\), \(p\) divides no spectator
divisor. Since \(p>y\), \(p\nmid e\). Since \(p>Y\), \(p\nmid d\) for \(d\mid P_0(y,Y)\). And
\(p\nmid L_j(t)\) whenever \(p\mid L_\ell(t)\), by (A2). So \(p\) just adds one more coprime factor
to the CRT system of Lemma 3.3, with residue \(1-a_j\bar a_\ell\) mod \(p\). For \((d,p)=1\):
\[\textstyle\sum_{t:\,pd\mid L_\ell(t)}a_t=\frac{g(d)}{p-1}\mathcal X+r_{dp}.\]

**8.4 Linear sieve lower bound.** Take level \(D_0/p\) and
\(s_p=\log(D_0/p)/\log Y=7(1/2-u)-28\delta\), where \(p=X^u\). Then
\[S'_{2,p}\ge\bigl(f_{\rm lin}(s_p)-O(\log^{-1/6}X)\bigr)\frac{\mathcal XV}{p-1}-\sum_{d<D_0/p}|r_{dp}|.\]
By §7.3, \(\mathcal XV=\frac{1+o(1)}{\alpha e^\gamma}\mathfrak M\) (an asymptotic, valid in both
directions).

**8.5 Lipschitz loss.** On \([2,4]\), \(f_{\rm lin}(s)=2e^\gamma\log(s-1)/s\) and
\(0\le f'_{\rm lin}\le e^\gamma\). Indeed, \(f'=2e^\gamma(s/(s-1)-\log(s-1))/s^2\), whose numerator
decreases from \(2\) to \(4/3-\log3>0\) while \(s^2\ge4\). Also \(f_{\rm lin}=0\) on \((-\infty,2]\)
and \(f_{\rm lin}(s)\le e^\gamma(s-2)\) (kernel: `flin_le_lipschitz`). Hence
\(f_{\rm lin}(s-h)\ge f_{\rm lin}(s)-e^\gamma h\) for \(h\ge0\), \(s\in[2,7/2]\). With
\(h=28\delta\):
\[S_2'\ge\frac{1-o(1)}{\alpha e^\gamma}\sum_{Y<p\le Z}\frac{f_{\rm lin}(7(1/2-u_p))-28e^\gamma\delta}{p}\,\mathfrak M-\sum_p\sum_d|r_{dp}|.\]

**8.6 Summation over \(p\).** By the prime number theorem, for continuous \(\Phi\),
\(\sum_{Y<p\le Z}\Phi(\log p/\log X)/p\to\int_\alpha^\beta\Phi(u)\,du/u\). With
\(\int_\alpha^\beta du/u=\log(3/2)\):
\[S_2'\ge\Bigl(2\Omega_2-\frac{28e^\gamma\log(3/2)}{\alpha e^\gamma}\delta-o(1)\Bigr)\mathfrak M-\mathrm{Rem}=\bigl(2\Omega_2-196\log(3/2)\,\delta-o(1)\bigr)\mathfrak M-\mathrm{Rem}.\]

**8.7 Remainders.** \(\mathrm{Rem}=\sum_p\sum_{d<D_0/p}|r_{dp}|\). Classify exactly as in §7.4,
with \(d\) replaced by \(pd\). Configuration (d) now has \(c=(d,\prod[d_i,d_i'])\); \(p\) itself
never overlaps (8.3). Its contribution is bounded by Lemma 4.3 (the extra condition
\(p\mid L_\ell\) and the sum over \(p\) cost a factor \(\le k\le 7\)). In configuration (a),
\(m=pd[e,e']\prod[d_i,d_i']\) with \(pd<D_0\), so the ledger of §5 applies verbatim.
Representations of \(m\) are \(\le\tau_{2K+3}(m)\). Cauchy–Schwarz with Lemma 6.1 gives
\(\mathrm{Rem}\ll\mathfrak M(\log X)^{-C}\). ∎

**Remark 8.2 (normalisation).** Error terms are always measured in units of \(\mathfrak M\). The
factor \((1-o(1))\) multiplies only nonnegative main terms (\(f_{\rm lin}\ge0\)), so it does not
reverse the inequality.

**Remark 8.3 (why \(\nu\) has no \(Z_{\rm exc}\)-factor).** If \(\nu\) contained
\(1_{(L_\ell,Z_{\rm exc})=1}\), the \(S_2\) lower bound would need a lower bound for that
indicator. That indicator is a congruence condition modulo \(Z_{\rm exc}\), and
Bombieri–Vinogradov must avoid this modulus. With our \(\nu\) and sifting set \(P_0\), no such
condition arises. This is what [M, §6] intends by "replace \(P(\cdot)\) by \(P_0(\cdot)\)".

---

## 9. `AffineChenS3` (affine Merikoski Lemma 17, switched)

**Lemma 9.1 (`AffineChenS3`).** There is \(C_3\ge0\) with the same uniformity such that for every
\(\varepsilon>0\) and all large \(X\):
\[S_3\le\Bigl(2\Omega_3+C_3\delta+\varepsilon\Bigr)\mathfrak M,\qquad \Omega_3=2\int_{\alpha<u_1<u_2<u_3<\beta}\omega\Bigl(\frac{1-u_1-u_2-u_3}{u_2}\Bigr)\frac{du_1du_2du_3}{u_1u_2^2u_3}.\]
One may take \(C_3=5/2\) (for \(\delta\le1/16\)).

*Proof.* **9.1 The switch.** Put \(x=L_\ell(t)=a_\ell t+1\). Then \(t\in\mathcal T\iff x\in I_\ell\)
and \(x\equiv a_\ell t_0+1\pmod{a_\ell W}\), with \(I_\ell=(a_\ell T_1+1,a_\ell T_2+1]\) (Lemma 3.3
with \(\ell\) in place of \(j\)). The prime coordinate becomes (`switched_identity`)
\[L_j(t)=\frac{a_jx+a_\ell-a_j}{a_\ell}.\]
**The source retains \(x\equiv a_\ell t_0+1 \pmod{a_\ell W}\) (for W3, \(x\equiv1\)), and
\(a_\ell W\) may be non-squarefree.** For example, \(a_\ell=4\), \(2\mid W\)
(`switched_modulus_not_squarefree`). For a prime \(q\nmid a_\ell W\):
\(q\mid L_j(t)\iff x\equiv1-a_\ell\bar a_j \pmod q\) (a unit residue by Lemma 3.2), and
\(q\mid L_i(t)\iff x\equiv1-a_\ell\bar a_i\).

**9.2 Selberg upper bound on \(L_j\).** Let \(\mathfrak a_x=\sum_{Y<p<q<r\le Z}\sum_{(s,P_0(q))=1}1_{x=pqrs}\ge0\),
so that \(S_3=\sum_t\nu(t)1_{\mathbb P}(L_j(t))\mathfrak a_{L_\ell(t)}\). Let \(G\) be smooth,
supported on \([0,\theta]\) with \(\theta=\frac14-2\delta\), and \(G(0)=1\). Since
\(L_j(t)>X^{1/4}\) is prime, only \(e=1\) survives in
\(\sum_{e\mid L_j(t)}\mu(e)G(\log e/\log X)\). So
\[S_3\le\sum_{t}\mathfrak a_{L_\ell(t)}\nu(t)\Bigl(\sum_{e\mid L_j(t),\,(e,Z_{\rm exc})=1}\mu(e)G\Bigl(\frac{\log e}{\log X}\Bigr)\Bigr)^2,\]
using \(\mathfrak a\ge0\) and \(\nu\ge0\) (**positivity used here**). Expand. The configurations
with \([e,e']\) (on \(L_j\)) and the \([d_i,d_i']\) (on \(L_i\), \(i\ne j,\ell\)) not pairwise
coprime are empty by (A2). For the others, Lemma 3.3 in the variable \(x\) gives one reduced class
modulo \(a_\ell W\cdot m\), with \(m=[e,e']\prod[d_i,d_i']\) squarefree and coprime to
\(WZ_{\rm exc}\). Write
\[\textstyle\sum_{x\in I_\ell,\ x\equiv c\,(a_\ell Wm)}\mathfrak a_x=\frac1{\phi(a_\ell Wm)}\sum_{x\in I_\ell}\mathfrak a_x+O(\widetilde E_\ell(m)).\]

**9.3 Main term.**
\(\frac1{\phi(a_\ell Wm)}=\frac1{a_\ell\phi(W)\phi(m)}\) (Lemma 3.4). By [FI, Lemma 12.1], as in
[M, proof of Lemma 17],
\(\sum_{x\in I_\ell}\mathfrak a_x=(1+o(1))\frac{|I_\ell|}{\log X}\cdot\frac{\Omega_3}2\), with
\(|I_\ell|=a_\ell(T_2-T_1)\). The slope \(a_\ell\) cancels again:
\[\frac1{\phi(a_\ell W)}\sum_{x\in I_\ell}\mathfrak a_x=(1+o(1))\,\#\mathcal T\,B^{-1}\cdot\frac{\Omega_3}{2}.\]
The remaining divisor sum over \((e,e',\mathbf d,\mathbf d')\), with local factors
\(1/\phi(q)\) (Lemma 3.6), is literally the one in [BFM, Lemma 4.6(iii)]. Choosing \(G\) optimally
there gives the factor \(1/\theta\) in place of \(4\):
\[S_3\le\Bigl(\frac{1}{\theta}+o(1)\Bigr)\cdot\frac{\Omega_3}{2}\cdot\mathfrak M\cdot(\log X)\cdot\frac1{\log X}+O(\mathrm{Rem})=\Bigl(\frac{2\Omega_3}{1-8\delta}+o(1)\Bigr)\mathfrak M+O(\mathrm{Rem}).\]
Since \(\frac{2\Omega_3}{1-8\delta}-2\Omega_3=\frac{16\delta\Omega_3}{1-8\delta}\le32\Omega_3\delta\) for
\(\delta\le\frac1{16}\), and \(\Omega_3\le0.0765\) (§12), we may take \(C_3=5/2\).

**9.4 Remainder via Lemma 6.1.** By §5, \(a_\ell Wm\le X^{1/2-2\delta+\epsilon_W}\le X^{1/2-\delta}\).
Cauchy–Schwarz (as in §7.4) reduces matters to \(\sum_m\widetilde E_\ell(m)\ll X/(\phi(W)(\log X)^{C'})\).
Following [M, proof of Lemma 17] verbatim in the variable \(x\):
1. finer-than-dyadic decomposition with \(\lambda=1+\log^{-2C}X\);
2. removal of the cross-conditions \(Y<p<q\) at cost (error1)+(error2). These are bounded using
   \(m'=rs\gg X/(pq)\ge X^{4/7}>X^{1/2}\), which exceeds the modulus \(a_\ell Wm\le X^{1/2-\delta}\)
   (\(\beta<\frac14\) is used here);
3. replacement of \(1_{\mathbb P}(m)\) by \(1_{\mathbb P}(m)\log m/\log A_1\).

This writes \(\mathfrak a_x1_{x\in I_\ell}\) as \(O(\log^{4C+2}X)\) functions \(\Lambda_0=f\ast g\) with:
* \(f(m)=1_{\mathbb P}(m)\log m\,1_{m\le A}\), \(A\in[Y/\lambda^2,\lambda Z]\subset[X^{1/8},X^{7/8}]\);
* \(g(n)=\sum_{q<r\le Z,\ q\in(A_2,\lambda A_2]}\sum_{(s,P(q))=1}1_{n=qrs}\).

The **support and coefficient hypotheses** of Lemma 6.1 are checked explicitly (\(\alpha_0=\frac18\)):
* \(P^-(n)\ge\min(q,P^-(s))>A_2\ge Y/\lambda^2\ge X^{1/8}\);
* \(n\asymp X/A_1\);
* \(|g(n)|\le\binom72=21\), since \(n\le X^{1+o(1)}\) has at most \(7\) prime factors \(>X^{1/7}\)
  and \(g(n)\) counts pairs \((q,r)\) among them;
* \(X^{1/8}\ll A_1\ll X^{7/8}\).

(`reg7_support_lengths` records the corresponding range arithmetic at \(\alpha_0=\frac17\), namely \([\frac17,\frac3{14}]\subset[\alpha_0,1-\alpha_0]\). We take \(\alpha_0=\frac18\) to absorb the factors \(\lambda^{\pm2}\).) Lemma 6.1 then applies with the maximum
over residues inside the sum. ∎

**Remark 9.4 (exceptional prime inside \(S_3\)).** In \(\mathfrak a_x\) the condition is
\((s,P_0(q))=1\), so \(Z_{\rm exc}\) (which is \(<Y<q\)) may divide \(s\). Then \(P^-(n)\) could be
\(Z_{\rm exc}\), violating the support hypothesis. Write \(s=Z_{\rm exc}^ks'\) with
\(Z_{\rm exc}\nmid s'\), and split \(\mathfrak a=\mathfrak a^{(0)}+\mathfrak a^{(\ge1)}\).
* \(\mathfrak a^{(0)}\) has \((s,P(q))=1\) and satisfies the hypotheses.
* \(\mathfrak a^{(\ge1)}_x=\sum_{k\ge1}\mathfrak a^{(0)}_{x/Z_{\rm exc}^k}1_{Z_{\rm exc}^k\mid x}\). For moduli
  coprime to \(Z_{\rm exc}\), its distribution in progressions is that of
  \(\mathfrak a^{(0)}\) at scale \(X/Z_{\rm exc}^k\), with residue multiplied by
  \(\bar Z_{\rm exc}^k\). So Lemma 6.1 applies termwise (\(k\le\log X\)), and its main term is
  \(\ll\sum_{k\ge1}Z_{\rm exc}^{-k}\cdot\frac{X}{\log X}=o(X/\log X)\), because
  \(Z_{\rm exc}\to\infty\) when it exists.

So \(\mathfrak a^{(\ge1)}\) contributes \(o(\mathfrak M)\). (Merikoski leaves this implicit.)

---

## 10. `AffineSquareTail` (new; needed only because of §2)

**Lemma 10.1.** \(S_{\rm sq}\ll_\eta X^\eta(\#\mathcal T/Y+Z)\) for every \(\eta>0\). In particular
\(S_{\rm sq}\le\varepsilon\mathfrak M\) for large \(X\).

*Proof.* \(\nu(t)\ll\prod\tau(L_i(t))^2\ll_\eta X^{\eta/2}\) (divisor bound). Also
\(\mathrm{sq}(n)\le7\cdot\#\{p\in(Y,Z]: p^2\mid n\}\). For \(Y<p\le Z\), \((p,a_\ell W)=1\), so
\(p^2\mid a_\ell t+1\) is one class mod \(p^2\), compatible with \(t\equiv t_0\) (W). So
\[\#\{t\in\mathcal T: p^2\mid L_\ell(t)\}\le\#\mathcal T/p^2+1,\]
and
\[S_{\rm sq}\ll X^{\eta/2}\sum_{Y<p\le Z}(\#\mathcal T/p^2+1)\ll X^{\eta/2}(\#\mathcal T/Y+Z).\]
Since \(\mathfrak M\ge\#\mathcal T(\log X)^{-K-1}\) and \(\#\mathcal T\ge X^{1-2\epsilon}\), this is
\(\le\mathfrak M X^{-1/7+\eta+o(1)}+X^{3/14+\eta}=o(\mathfrak M)\). ∎

---

## 11. Affine Proposition 12

**Theorem 11.1.** Under the W3 framework, for \(\delta\le\delta_{\max}\), every \(\varepsilon>0\),
all large \(X\), and all \(j\ne\ell\):
\[\mathcal S\le\Bigl(\Omega_1-\Omega_2+\Omega_3+\bigl(C_1+\tfrac{C_2}2+\tfrac{C_3}2\bigr)\delta+\tfrac52\varepsilon\Bigr)\mathfrak M .\]

*Proof.* Combine Lemma 1.1, Lemma 2.2, and Lemmas 7.1, 8.1, 9.1, 10.1:
\[S\le S_1-\tfrac12S_2+\tfrac12S_3+\tfrac12S_{\rm sq}\le\bigl[(\Omega_1+C_1\delta+\varepsilon)-(\Omega_2-\tfrac{C_2}2\delta-\tfrac\varepsilon2)+(\Omega_3+\tfrac{C_3}2\delta+\tfrac\varepsilon2)+\tfrac\varepsilon2\bigr]\mathfrak M.\]
∎ In Lean: `pairExpect_le_chen`, which builds `PairBoundProvider` with
\(c_0=\)`chenCertificate` from the four providers (`pairBound_of_chen`). The only arithmetic is
the kernel-checked combination. The W3 *normalised* pair functional is
\(\mathcal S/\mathfrak M\), via the normaliser inequality \(\mathfrak M(rK)^2\le(1+\eta)\mu^2\)
(BFM Lemma 4.7, a W3 input).

We cite only the scalar identities of [M] after this point. The arithmetic sources have been
reduced to exactly Merikoski's one-dimensional integrals: \(\Omega_1\) via Lemma 7.1, \(\Omega_2\)
via 8.6, and \(\Omega_3\) via 9.3.

---

## 12. The scalar constant (kernel-checked; `ScalarFunctions.lean`, `ScalarOmega.lean`, `ScalarCertificate.lean`)

* **Faithful functions.** \(F_{\rm lin},f_{\rm lin}\) are defined by the closed forms on
  \([1,5]\), \([2,4]\). The Lean file proves they satisfy the delay-differential system and the
  initial conditions of [M, §5] (`Flin_initial`, `flin_dde`, `Flin_dde`). Likewise the Buchstab
  function \(\omega\) on \([1,4]\) (`buchstab_initial`, `buchstab_dde_mid`, `buchstab_dde_tail`).
* **\(\Omega_1-\Omega_2\)** (`Omega1_sub_Omega2`). From the definitions at \(\alpha=\frac17\),
  \(\beta=\frac3{14}\):
  \[\Omega_1-\Omega_2=4-2\int_1^{3/2}\log v\Bigl(\frac1{5/2-v}-\frac1{v+1}\Bigr)dv.\]
  (Substitute \(v=s-2\) in \(\Omega_1=4+4\int_3^{7/2}\frac{\log(s-2)}{s-1}ds\), and \(v=5/2-7u\) in
  \(\Omega_2\).)
* **Buchstab bound** (`buchstab_le`): \(\omega(t)\le\frac35\) for \(t\in[5/3,4]\). The arguments
  occurring in \(\Omega_3\), namely \((1-u_1-u_2-u_3)/u_2\) with \(\frac17\le u_1\le u_2\le u_3\le\frac3{14}\),
  lie in \([5/3,4]\) (`omega3_arg_mem`).
* **\(\Omega_3\le14\log(3/2)-\frac{28}5\)** (`Omega3_le`), by integrating the bound \(\frac35\) and
  computing the elementary iterated integral exactly.
* **Lower bound for the \(J\)-integral** (`J_lower`). This uses \(\log v\ge2\,\mathrm{artanh}\)-type
  rational bounds and exact antiderivatives. Rational bounds on \(\log(3/2)\) and \(\log(5/4)\)
  come from finite series (`log_three_halves_le`, `log_five_fourths_le`).
* **Certificate** (`pairConstant_le_certificate`, `chenCertificate_lt`, `pairConstant_lt`):
  \[\Omega_1-\Omega_2+\Omega_3\le\frac{796682507263}{200000000000}=3.983412536315<3.984.\]
  The room is \(3.984-c_{\rm cert}=\frac{117492737}{200000000000}\) (`certificate_room`).

All of this is real-analysis proofs in the Lean kernel, with axioms
`propext`, `Classical.choice`, `Quot.sound` only. There is no floating point and no `native_decide`.
(Merikoski's published numerics \(\Omega_1\le4.19\), \(\Omega_2\ge0.279\), \(\Omega_3\le0.076\)
are not used.)

---

## 13. The \(O(\delta)\) budget, explicitly

From §§7–9: \(C_1=\frac{392}9\), \(C_2=196\log\frac32\), \(C_3=\frac52\). So
\[C_{\rm err}:=C_1+\tfrac{C_2}2+\tfrac{C_3}2=\tfrac{392}9+98\log\tfrac32+\tfrac54<85\qquad(\texttt{explicit\_Cerr\_lt}),\]
and with \(\delta_0=6\cdot10^{-6}\):
\[C_{\rm err}\delta_0<85\cdot6\cdot10^{-6}=5.1\cdot10^{-4}<5.87\cdot10^{-4}<3.984-3.983412536315\qquad(\texttt{explicit\_delta0}).\]

**Precise status.** The *values* \(C_1,C_2,C_3\) come from identifying the \(\delta\)-dependence of
Lemmas 7.1, 8.1, 9.1 as pure level losses. These are \(F_{\rm lin}\) at \(s=7/2-28\delta\),
\(f_{\rm lin}\) at \(s_p-28\delta\), and the Selberg support \(\theta=\frac14-2\delta\). Every other
error is \(o(1)\) as \(X\to\infty\) for fixed \(\delta\). We have checked this by reading every
"\(O(\delta)\)" in [M, Lemmas 15–17] and [BFM, Lemma 4.6]. It remains a **paper-level
constant-extraction obligation**: the Lean providers only assert the existence of constants
\(C_i\) independent of \(X\) and \(\delta\), and the Lean proof of W2.984 chooses \(\delta\) from
whatever \(C_i\) the providers supply. The asymptotic theorem needs only that uniformity, which
the written lemmas state and prove. The explicit \(\delta_0\) is a bonus, conditional on the
identification above.

(The Lean statements \(F_{\rm lin}\)-Lipschitz and \(f_{\rm lin}\)-Lipschitz are not formalised,
except for the boundary inequality `flin_le_lipschitz`. They are elementary calculus, given in
§§7.3, 8.5.)

---

## 14. Downstream: W3 machinery and W2.984

Nothing below is new mathematics. It is the imported W3 consumer (`PostV87V90R`, frozen in
`W3Publication`), driven by the pair constant of Theorem 11.1 (`MainTheorem.lean`,
`width_of_pairBound`, kernel-checked).

Fix \(s>2.984\) (reduce to \(s\le7\) by monotonicity).
1. `exists_ratio`: choose integers \(1\le m\), \(2m\le r\) with
   \(c_{\rm cert}<\rho:=r/m\) and \((r-m)/m<s\). This is possible since
   \(c_{\rm cert}-1<2.984<s\). This gives \(3.984>c_{\rm cert}\) and \(c_{\rm cert}<r/m<s+1\).
2. Set \(\mathrm{room}=\rho-c_{\rm cert}\). Choose \(\delta=\min(\delta_{\max},\mathrm{room}/(8(C_{\rm err}+1)))\),
   \(\varepsilon=\mathrm{room}/8\), \(\eta_0=\mathrm{room}/(4\rho)\). Then
   \(C_{\max}=(c_{\rm cert}+\mathrm{room}/4)(1+\eta_0)<r/m\).
3. BFM functional rescaling (a W3 input) realises first moment \(\mu>\mu_0=\frac{mr}{r-mC_{\max}}\).
4. Theorem 11.1 and the pair-moment identity `E_Qcount_eq` give
   \(\mathbb EQ\le C_{\rm pair}\mu^2/(2r)\) with \(C_{\rm pair}\le C_{\max}<r/m\). Then the W3 consumer
   `WindowMomentData.false` gives: \(\mathbb E Z>m\) ⇒ some \(t\) has \(m+1\) occupied blocks ⇒
   useful edge ⇒ adjacent omissions ⇒ \(\bot\) (cyclic contact graph, affine gcd compiler,
   fixed relative interval, contact adjacency, bounded-cofactor row rigidity — all imported).
5. Conclusion (`W2984`, `W2984_counterexample_form`):
   \[\forall s>2.984\ \exists M_s\ \forall A:\ \bigl(A\ \text{a #287 counterexample},\ \max A\ge M_s\bigr)\Rightarrow\max A/\min A<s.\]

No endpoint: `reg9_endpoint_excluded`. The proof in fact gives every \(s>c_{\rm cert}-1\approx2.98341\),
but the theorem is deliberately stated only for \(s>2.984\).

**Consistency check.** The same consumer with \(c_0=4\) (Selberg, [BFM, Lemma 4.6(iii)]) re-derives
W3 (`W3_of_selbergPairBound`). So the refactored framework is the W3 framework.

---

## 15. Effectivity

**Tag: `ineffectiveExistential`** (`W2984_effectivity`, `reg12_tag`). The onset \(M_s\) is an
existential produced by the analytic inputs. Lemma 6.1, step 5, uses [BFM, Lemma 4.1] and the
exclusion of a possible exceptional modulus (Siegel). W3 has the same issue. No effective
treatment is supplied, and none is attempted here.

---

## 16. Summary of what this document establishes

* The affine analogues of Merikoski's Lemmas 13, 15, 16, 17 and §6 are written in full: §§2, 7,
  8, 9 and 4. Every source transformation is explicit:
  * the congruence system for \(p=L_j(t)\) (§3);
  * the switch \(x=L_\ell(t)\) (§9.1);
  * the fixed non-squarefree bases \(a_jW\), \(a_\ell W\) (§6);
  * the two small-prime-square divisors (§5).
* One expository gap in [M, Lemma 13] was found (non-squarefree \(n\)). It is repaired by
  Lemma 2.1 together with the negligible tail of §10. It does not affect the constant.
* One gap in the *published proofs* (not statements) of [BFM, Thm 4.2] and [M, Prop 11] for
  non-squarefree \(q_0\)-parts is closed by the line-by-line check in Lemma 6.1.
* The scalar bound \(<3.984\) is kernel-checked. The \(\delta\)-budget is explicit, with the
  identification of \(C_1,C_2,C_3\) recorded as a paper-level obligation.
* The W3 downstream is reused unchanged. The theorem is conditional on the analytic lemmas being
  accepted, asymptotic and ineffective. **Erdős #287 remains open.**
