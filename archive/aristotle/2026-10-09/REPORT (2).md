# Erdős #287 — a family-averaged repair of the false Urem provider

Date: 9 October 2026.

## Verdict and limits

**PAPER-LEVEL UREM REPAIR: a proved family theorem under explicitly stated, independently checkable source conditions.**

**LATEST LEAN INTEGRATION: NOT PERFORMED. UNCONDITIONAL TAIL287: NOT ESTABLISHED HERE.**

This document does not attempt to prove the proposition that Aristotle reportedly refuted. It replaces the unnecessarily strong packetwise analytic contract by the family-averaged estimate actually used in the supplied V100R Ordering-B proof. The replacement is proved below from a published BDH theorem, finite CRT/variance identities, and explicit coefficient and parameter accounting. It is not a newly named assumption that the desired remainder is small.

The proof applies to the source class specified in Section 2, not every tuple admitted by a generic `physUrem` declaration. Sections 6–8 explain how the physical definitions supply, or must be shown to supply, that source class. The existence of an appropriate generic theorem is not, by itself, a Lean instantiation of the latest project.

### Materials actually inspected

The available archive was `f3680730-21fd-4bc3-b8e9-fac9ae820a7d-aristotle (6).tar.gz`, together with the archive-6 reconciliation report and the supplied V100R source text. The archive contains `Physical/TypeII/SourceComposed.lean`, `RemainingProviders.lean`, `Cells.lean`, the factorization modules and presieve/packet definitions. It does **not** contain `UremCounterexample.lean` or the definition of `OrdinaryBVUremProviderScoped`.

The user supplied the signature

```lean
theorem not_ordinaryBVUremProviderScoped {κ : ℝ}
    (hκ : 0 < κ) (hκ' : κ < 1 / 100000) :
    ¬ OrdinaryBVUremProviderScoped κ
```

We retain that as a **reported formal refutation**. Its witness and complete proof have not been replayed here. No claim below identifies what that unseen witness exploits.

The local toolchain has no `lean` or `lake`. Thus this package is a mathematical proof and an implementation specification, not a fresh kernel certificate. The existing archive was not altered, and no remote repository was written to.

## 1. The erroneous inference to remove

The archive's old `OrdinaryBVUremProvider` asks for a bound of the form

\[
 |\mathrm{physUrem}_{\xi}|\le C_A B_\alpha B_\beta|\Gamma_\xi|\mathcal A_T
 \frac{x}{f_\xi(\log x)^A}
\]

uniformly over arbitrary bounded dyadic coefficient sequences, without the distribution hypotheses that would support it. A modulus being below a nominal half-level is not an equidistribution statement about its coefficients.

Even after correcting some binders, a packetwise statement can be substantially stronger than the estimate actually needed by the physical remainder. The valid architecture below is

\[
\boxed{
 \text{common arithmetic sequence}
 \longrightarrow \text{relative squared residue errors}
 \longrightarrow \text{packet-family Cauchy}
 \longrightarrow \text{BDH on complete moduli}.
}
\]

It never obtains a pointwise-in-packet logarithmic error and then multiplies it by the number of packets.

This distinction was already present in the supplied V100R text, Section 4. In particular its (4.6)–(4.7) are family estimates. Recovering that argument is a repair of the formal analytic interface, not a claim to have discovered a new distribution theorem.

## 2. Precisely admissible source

Use \(\mathcal L=\log x\) and let \(NM\asymp x\), with \(N\ge x^\eta\) for a fixed \(\eta>0\). Work first in one fixed designated-pair/HB/dyadic group. The finite number of designated pairs and the polylogarithmic number of dyadic groups will be charged at the end.

Let \(\Xi_x\) be a finite packet family. Each packet has a positive base \(f_\xi\le F\), a unit residue \((c_\xi,f_\xi)=1\), and a weight \(\Gamma_\xi\). The affine integers \(A,B\) are fixed for this group, with \(A>0\), \(B\ne0\), \((A,B)=1\). It is sufficient that they range over a fixed finite family.

Let \(\alpha_n\) be a **common sequence**, supported on a subinterval of \([N,2N)\), with uniformly controlled coprimality Siegel–Walfisz estimates. Explicitly, after division by a fixed power of \(\mathcal L\) if necessary, it is divisor bounded and there is a fixed exponent \(J_0\) such that, for every accuracy \(H>0\),

\[
\left|\sum_{\substack{n\in I\\ n\equiv a\pmod q\\(n,t)=1}}\alpha_n
-\frac1{\phi(q)}\sum_{\substack{n\in I\\(n,qt)=1}}\alpha_n\right|
\ll_H N\tau(t)^{J_0}\mathcal L^{-H},
\tag{2.1}
\]

for the intervals used here, every \((a,q)=1\), and every positive integer \(t\). The constants are uniform over the actual common-sequence groups after their fixed logarithmic normalizations. This is stronger and more explicit than an existentially chosen, possibly vacuous polylog-modulus test.

The complementary sequence \(\beta_{\xi,m}\) can depend on the packet; only the common bound

\[
\sum_{M\le m<2M}|\beta_{\xi,m}|^2\ll M\mathcal L^{B_\beta}
\tag{2.2}
\]

is needed. A pointwise polylogarithmic bound on \(\beta\) is not required.

For one normalized scalar atom let \(z_{\xi,l,r}\) be its coefficient. Assume

\[
|z_{\xi,l,r}|\le\mathcal L^{B_c},
\qquad l\in[L,2L),\quad 1\le r\le x^{C_r},
\tag{2.3}
\]

and that it vanishes unless

\[
(l,r)=1,\qquad(f_\xi,lr)=1,\qquad(AB,lr)=1.
\tag{2.4}
\]

It can contain arbitrary packet-, \(l\)- and \(r\)-dependent support restrictions under this envelope. It may not introduce unaccounted dependence on the physical variables \(m,n\). Product cutoffs such as \(lr<K\) are therefore allowed. Additional physical product windows or profiles must be separated or handled at their recorded source scope; they are not free consequences of this theorem.

Require

\[
M\ge 2FL,
\qquad 2FL<\frac{N}{(\log N)^{C(H)}}.
\tag{2.5}
\]

The second condition uses the logarithmic reserve required by the published BDH theorem at the eventual chosen precision. Section 7 obtains it from a fixed-power margin.

Finally assume the concrete packet multiplicity bound

\[
a_f:=\sum_{\xi:f_\xi=f}|\Gamma_\xi|\ll\tau(f)^K
\tag{2.6}
\]

with fixed \(K\). It implies

\[
\sum_\xi\frac{|\Gamma_\xi|}{f_\xi}\ll\mathcal L^{K_1}
\tag{2.7}
\]

for a fixed \(K_1\). Section 6 derives (2.6) for the stated bounded Maynard tensor construction.

Define the normalized Urem packet

\[
\begin{aligned}
C_\xi={}&\sum_{l,r}z_{\xi,l,r}\sum_{m,n}\beta_{\xi,m}\alpha_n
\mathbf1_{mn\equiv c_\xi\pmod{f_\xi}}\,
 h_l(mn)U_r(mn),\\
h_l(v)={}&\mathbf1_{Av\equiv B\pmod l}-\frac{\mathbf1_{(v,l)=1}}{\phi(l)},
\quad U_r(v)=\frac{\mathbf1_{(v,r)=1}}{\phi(r)}.
\end{aligned}
\tag{2.8}
\]

**Theorem (family Urem).** Under (2.1)–(2.6), for every fixed target \(A_*>0\), after taking the BDH precision sufficiently large,

\[
\boxed{\sum_{\xi\in\Xi_x}|\Gamma_\xi|\,|C_\xi|
\ll_{A_*}x\mathcal L^{-A_*}.}
\tag{2.9}
\]

The constant can depend on the fixed source data and the SW constants. No effective numerical onset is claimed. This suffices for pre-effectivity use.

## 3. Exact residue identity and variance contraction

Put \(\alpha^{(r)}_n=\alpha_n\mathbf1_{(n,r)=1}\). Define

\[
\Delta_{\alpha^{(r)}}^{f,c}(l,a)=
\sum_{\substack{n\sim N\\n\equiv c\pmod f}}\alpha_n^{(r)}
\left(\mathbf1_{n\equiv a\pmod l}-\frac{\mathbf1_{(n,l)=1}}{\phi(l)}\right).
\tag{3.1}
\]

Let \(E_\rho(q,a)\) denote the ordinary unit-class discrepancy for a sequence \(\rho\). If \((f,l)=1\) and \(c,a\) are units, CRT gives

\[
\Delta_\rho^{f,c}(l,a)=E_\rho(fl,\mathrm{CRT}(c,a))
-\frac1{\phi(l)}\sum_{a'\bmod l}^{*}E_\rho(fl,\mathrm{CRT}(c,a')).
\tag{3.2}
\]

To verify this, expand both terms. The global reference proportional to
\(\sum_{(n,fl)=1}\rho_n\) cancels. What remains is exactly the progression count in (3.1) minus its **base-relative** unit average. This identity includes all nonunit inputs through their zero indicators.

For fixed \(c\), subtraction of the mean is an orthogonal projection. Therefore

\[
\sum_{c\bmod f}^{*}\sum_{a\bmod l}^{*}|\Delta_\rho^{f,c}(l,a)|^2
\le\sum_{b\bmod fl}^{*}|E_\rho(fl,b)|^2.
\tag{3.3}
\]

No loss of \(\phi(f)\), no extra factor \(\phi(l)\), and no early restriction of \(\alpha\) to one residue class occur here.

Masking by \((n,r)=1\) preserves the coprimality SW class with the explicit normalization

\[
\widetilde\alpha^{(r)}_n=\frac{\alpha_n\mathbf1_{(n,r)=1}}{\tau(r)^{J_0}}.
\tag{3.4}
\]

Indeed, a further mask by \(t\) is a mask by \(rt\), and
\(\tau(rt)\le\tau(r)\tau(t)\). The constants in (2.1) remain uniform in \(r\). This argument does not apply to an arbitrary residue mask.

## 4. Published BDH input and the weighted family energy

The sole distribution theorem in this Urem repair is **Maynard I, arXiv:2006.06572v2, Lemma 13.8** [M1]. For a divisor-bounded SW sequence and any desired saving, it bounds the sum of squared unit-class discrepancies, with a fixed divisor weight on the modulus, up to \(Q<N/(\log N)^{C}\).

For fixed \(r\), set

\[
\mathscr R_r(f)=\sum_{\substack{L\le l<2L\\(l,frAB)=1}}
\sum_{c'\bmod f}^{*}\sum_{a'\bmod l}^{*}
|\Delta_{\alpha^{(r)}}^{f,c'}(l,a')|^2.
\tag{4.1}
\]

Apply (3.3), then group \(q=fl\). For every \(q\), at most \(\tau(q)\) pairs \((f,l)\) occur, and \(\tau(f)^K\le\tau(q)^K\). Dropping restrictions in this nonnegative upper bound yields

\[
\sum_{f\le F}\tau(f)^K\mathscr R_r(f)
\le\sum_{q\le2FL}\tau(q)^{K+1}
\sum_{b\bmod q}^{*}|E_{\alpha^{(r)}}(q,b)|^2.
\tag{4.2}
\]

Enlarge the fixed divisor exponent in [M1] to dominate both \(K+1\) and the pointwise divisor bound. Apply it to (3.4), and undo the normalization. For any \(H>0\),

\[
\boxed{\sum_{f\le F}\tau(f)^K\mathscr R_r(f)
\ll_H\tau(r)^{2J_0}N^2\mathcal L^{-H}.}
\tag{4.3}
\]

This step estimates a complete family of residue errors. It is neither a pointwise prime AP estimate nor an unjustified application of ordinary BV to arbitrary \(\alpha\).

## 5. Source-level Urem estimate, with the density in the right place

The conditions (2.4) and \((c_\xi,f_\xi)=1\) give the exact rearrangement

\[
C_\xi=\sum_r\frac1{\phi(r)}\sum_{l,m}
\beta_{\xi,m}z_{\xi,l,r}\mathbf1_{(m,f_\xi lr)=1}
\Delta_{\alpha^{(r)}}^{f_\xi,c_\xi\overline m}
(l,B\overline{Am}).
\tag{5.1}
\]

The inverse of \(m\) is taken modulo \(f_\xi\); the inverse of \(Am\) is taken modulo \(l\). No inverse of \(A\) modulo \(f_\xi\) is used.

Fix \(r,f=f_\xi\). The map

\[
m\pmod{fl}\mapsto
(c_\xi\overline m\pmod f, B\overline{Am}\pmod l)
\tag{5.2}
\]

is a bijection on unit classes. Each output pair is attained at most
\(M/(fl)+1\le2M/(fL)\) times in the physical \(m\)-interval. The extra mask \((m,r)=1\) can only decrease this population.

Cauchy in \((l,m)\), using (2.2)–(2.3), now gives

\[
\left|\sum_{l,m}\beta_{\xi,m}z_{\xi,l,r}
\mathbf1_{(m,flr)=1}\Delta_{\alpha^{(r)}}^{f,c_\xi\bar m}(l,B\overline{Am})\right|
\ll M\mathcal L^{C_1}\sqrt{\frac{\mathscr R_r(f)}f}.
\tag{5.3}
\]

Explicitly, the first squared Cauchy factor is at most
\(L\mathcal L^{2B_c}\sum_m|\beta_{\xi,m}|^2\ll LM\mathcal L^{2B_c+B_\beta}\).
The second is at most \(2M\mathscr R_r(f)/(fL)\).
Their product explains the **reciprocal base density**; it was not guessed from a modulus range.

Next sum packets using weighted Cauchy:

\[
\begin{aligned}
\sum_\xi |\Gamma_\xi|\sqrt{\mathscr R_r(f_\xi)/f_\xi}
&\le\left(\sum_\xi\frac{|\Gamma_\xi|}{f_\xi}\right)^{1/2}
\left(\sum_f a_f\mathscr R_r(f)\right)^{1/2}\\
&\ll_H\tau(r)^{J_0}N\mathcal L^{-H/2+C_2}.
\end{aligned}
\tag{5.4}
\]

Here (2.6), (2.7), and (4.3) are used. The same \(\mathscr R_r(f)\) is available for all packets in the group precisely because the original \(\alpha\) is common. No summation over a polynomial number of unrelated SW sequences is hidden here.

Finally,

\[
\sum_{r\le x^{C_r}}\frac{\tau(r)^{J_0}}{\phi(r)}\ll\mathcal L^{C_3}.
\tag{5.5}
\]

One elementary proof uses \(r/\phi(r)\le\tau(r)\), domination of a fixed divisor power by a fixed-order divisor function, and the harmonic convolution bound
\(\sum_{n\le y}d_k(n)/n\le(1+\log y)^k\).

Combining (5.1)–(5.5) proves (2.9) by taking
\(H>2(A_*+C_1+C_2+C_3+1)\).
All exponents governing the source norms are fixed first. This is not a circular choice of a modulus-cutoff exponent.

## 6. Actual sequence and packet checks; not arbitrary coefficients

### 6.1 The selected HB variable in the inspected code

`Physical/TypeII/Cells.lean` defines `alphaSeq` as one rough, dyadically restricted individual Heath–Brown variable. The possibilities are a rough constant sequence, a rough logarithm, or rough \(\mu(n)\mathbf1_{n\le z}\). Unused variables are the Dirichlet unit; on a genuine critical interval tending to infinity they give zero, not a new difficult coefficient class. `betaSeq` is the convolution of the other five variables.

The supplied pointwise bound
\(|\beta_m|\le(1+\log m)^5d_5(m)\) implies (2.2) by a fixed divisor moment. This avoids needing a new assertion that every individual beta coefficient is polylogarithmically bounded.

The following arguments supply the coprimality-SW class for these individual sequences. They are classical paper arguments, not Lean declarations in this package.

### 6.2 Rough constants and logarithms

Let \(z_0=x^{1/(\log\log x)^3}\), \(N\ge x^\eta\), and consider \(q\le(\log N)^D\). Eventually \(q<z_0\), so rough integers are automatically units modulo \(q\).

In a coprimality mask \((n,t)=1\), primes of \(t\) below \(z_0\) are redundant. Inclusion-exclusion over the remaining prime divisors of \(t\) writes the count as sums over \(k\mid\operatorname{rad}(t)\), all of whose prime factors are at least \(z_0\). For \(k\le\sqrt N\), apply the fundamental lemma to the rough integers in the interval divided by \(k\), in the residue \(a\bar k\pmod q\). The available sieve parameter is at least a fixed multiple of
\(\log N/\log z_0\asymp_\eta(\log\log x)^3\), so its error beats every fixed logarithmic power. The hypotheses of [M2, Lemma 5.4] hold with a sufficiently small fixed epsilon depending on eta.

For \(k>\sqrt N\), a direct count bounds both the actual and comparison contributions by \(O(\sqrt N+1)\) per divisor. Hence the total error is
\(O(\tau(t)\sqrt N)\), also smaller than \(N\tau(t)\mathcal L^{-H}\) eventually.

Summing the small-k errors costs at most \(\tau(t)\). This yields the requisite coprimality SW bound with a fixed divisor exponent. Partial summation supplies the rough logarithm; normalize by \(1+\log(2x)\) to restore one-boundedness. Truncation to the actual interval uses endpoint differences.

For larger \(q\), the trivial progression count and an elementary totient lower bound give the SW inequality once the small-modulus cutoff power D is chosen sufficiently large for the requested accuracy. This is a proof of the full SW property, not a claim that the test with q=1 suffices.

### 6.3 Rough Möbius variables

Let \(s_{z_0}(a)=1\) when all prime factors of \(a\) are strictly below \(z_0\), and zero otherwise. Euler factors, or finite divisor cancellation, give the exact identity

\[
\mu(n)\mathbf1_{P^-(n)\ge z_0}=(\mu*s_{z_0})(n).
\tag{6.1}
\]

For a unit-class discrepancy with the coprimality mask t, only convolution factors \(a\) coprime to \(qt\) contribute. The discrepancy becomes the sum of the ordinary coprimality-Möbius discrepancies on the intervals \(I/a\), with the unit residue replaced by \(b\bar a\). The classical SW property of mu, in the coprimality form stated in [M2, Definition 3], applies uniformly to \(a\le\sqrt N\). Their harmonic smooth-factor sum costs at most a fixed power of \(\log x\).

For \(a>\sqrt N\), use the elementary progression bound, discarding coprimality restrictions only in the positive majorant. Since \(a\le2N\), the error per a is \(O(N/a)\). With \(\delta=1/\log z_0\),

\[
\sum_{\substack{a>\sqrt N\\P^+(a)<z_0}}\frac1a
\le N^{-\delta/2}\prod_{p<z_0}(1-p^{-1+\delta})^{-1}
\ll(\log z_0)^{C}\exp\left(-\frac{\log N}{2\log z_0}\right).
\tag{6.2}
\]

For the Euler product, use \(p^\delta\le e\) and the prime harmonic bound, treating finitely many small primes separately. The exponential factor is
\(\exp[-c_\eta(\log\log x)^3]\), and therefore beats every fixed logarithmic power. This proves the needed uniform rough-Möbius SW property. The upper truncation \(n\le z\) is just another endpoint, not a packet residue selection.

These arguments do **not** prove SW for an arbitrary packet-dependent modification of alpha. Any such modification must be separately justified or removed before applying the family theorem.

### 6.4 Packet multiplicity

The actual code has \(f_\xi=a_jWq_0\), \(\Gamma_\xi=\omega_{\mathbf d}\omega_{\mathbf d'}\). Fix the finite tuple of slopes and a fixed bounded smooth tensor. Nonzero Möbius factors make the spectator entries squarefree. Pairwise spectator compatibility assigns each prime of q0 to one spectator coordinate, and to the first divisor vector, the second, or both.

Consequently each prime has at most \(3(k-2)\) choices. The smooth tensor coefficients are bounded by a constant depending on the fixed tensor. Thus

\[
a_f\ll_{k,\mathrm{tensor}}[3(k-2)]^{\omega(q_0)}
\ll_{k,\mathrm{tensor}}\tau(f)^K.
\tag{6.3}
\]

A fixed number of designated pairs changes only the constant. Support restrictions decrease the count. For k=2 the spectator product is empty and the conclusion is immediate.

The scalar atom colourings must not be counted by their enormous cardinality. The archive proves `total_variation_le` and `H_eq_of_T`; use their total weight, fixed in x once T is fixed, exactly once. Normalize each atom coefficient by \(\Gamma_\xi\) and its atom weight before applying (2.9).

## 7. Affine-unit and parameter repairs

### 7.1 Actual affine units are supplied by the presieve

`PhysData.WGood` requires every prime divisor of every slope and every nonzero slope difference to divide W. The archive's `wgood_eventually` establishes it for a fixed positive distinct tuple at the physical presieve.

For the designated pair,

\[
A=a_k/g,\quad B=(a_k-a_j)/g,\quad g=(a_j,a_k),\quad f=a_jWq_0.
\]

Every prime divisor of A divides a_k and thus W. Every prime divisor of B divides the slope difference and thus W. Hence

\[
(f,lr)=1\quad\Longrightarrow\quad(AB,lr)=1.
\tag{7.1}
\]

This is an actual source restriction inherited from the presieve, not an arbitrary new assumption chosen to eliminate a counterexample. Conversely it is not justified for the generic arbitrary A,B binders in the old provider.

### 7.2 Critical lengths

Fix \(0<\kappa<10^{-5}\), \(T=\lceil100/\kappa\rceil+2\), and use the proved actual scalar-factorization range

\[
x^{3\kappa}\le N\le x^{1/3+\kappa/2},\qquad l\le Nx^{-\kappa}.
\]

Take the conservative base-support exponent

\[
\sigma=\kappa/10^6,\qquad F=x^\sigma.
\]

For l-bands with nonzero coefficients,

\[
2FL\le2Nx^{-(\kappa-\sigma)}<N/(\log N)^C
\]

for every fixed C once x is large enough. Moreover, for \(NM\asymp x\),

\[
\frac{M}{FL}\gg x^{1/3-\sigma},
\]

so the occupancy condition is satisfied with a fixed-power reserve. Small fixed comparability constants do not alter these exponents. One must group or handle separately any cells for which the available code only knows \(NM\le x\) rather than the actual product-scale relation.

With the earlier spectral export \(\varepsilon=\kappa/2000\), the same conservative sigma obeys

\[
\sigma\le\varepsilon/100,\qquad
\frac\varepsilon2-\frac{391}{256}\sigma
=\frac{63609}{256000000}\kappa>0.
\tag{7.2}
\]

This repairs the numerical base-cap incompatibility in the older provider. It does not prove the spectral bound itself. The actual fixed slopes/presieve/spectator support must be fitted to this cap; their finite constants are allowed to affect the eventual onset.

## 8. Correct replacement in the proof graph

Preserve `not_ordinaryBVUremProviderScoped` and mark its target as unusable. Preserve all valid scalar/factorization/source identities.

For each actual HB/dyadic group, prove that the packet data and the normalized coefficient satisfy Sections 2, 6 and 7. Apply the family theorem (2.9) to the actual normalized Urem. Undo the scalar and log normalizations and sum the fixed total atom variation and the polylogarithmic group count.

Crucial code accounting:

- `physCoefAtom` and hence `physUrem` already contain Gamma. The final Lean inequality sums `|physUrem ... (Pd.Gamma ξ) ...|`; it must **not** multiply by `|Pd.Gamma ξ|` a second time.
- `packet_typeII_eq_cells` accepts arbitrary packet-dependent alpha and beta. The replacement theorem must specialize this to actual `alphaSeq` groups before using common-sequence BDH.
- The designated pair is part of the packet index. Group it once, not once outside and once inside the packet sum.
- Existing finite identities are valid with more general parameters than the analytic theorem. That does not force the analytic theorem to keep all of those universal quantifiers.

At the level of the paper proof, this supplies the centering branch estimate

\[
\sum_{\mathrm{actual\ groups},\xi}
|\mathrm{physUrem}_\xi|\ll_A x(\log x)^{-A},
\tag{8.1}
\]

with all fixed normalization costs included, provided the physical assembly uses exactly the source class documented here. If the main-term scale is \(\mathcal N_X I\gg x(\log x)^{-J}\), selecting \(A>J\) makes this branch \(o(\mathcal N_X I)\). The actual normalization lower bound must be proved by the main-term construction, not chosen to make this implication vacuous.

This restores a correct mathematical route around the **overstrong Urem provider**. It does not certify the newest missing counterexample witness, nor every remaining project branch.

## 9. What is not closed by this repair

The end-to-end target is still

\[
\exists M_0\;\forall M\ge M_0:\neg\operatorname{Counterexample}_{287}(M),
\]

with denominators greater than 1. No numerical M0 is required for this pre-effectivity claim.

A complete certificate still needs the actual normalized source integrated with the accepted noncritical branches, the true actual-atom W4 estimate, all Poisson/centering/cleanup steps, and the constructed seven-block main-term/window framework. These are not supplied by a theorem that bounds Urem.

The archive-6 reconciliation identifies these as distinct obligations. In particular a declaration of `W4SpecEstimate : Prop` and a theorem adding three assumed estimates are not a proof of the spectral theorem. Neither an earlier model's PASS nor the present repair discharges an absent paper argument.

The proper frontier after implementing this repair is: **the actual Urem family estimate no longer needs the false packetwise provider; verify its exact source instantiation, then reconcile and compose the remaining spectral and seven-block claims.** This is narrower than asking to invent a new arbitrary-sequence BV theorem. It is not an unconditional tail certificate yet.

The independent V103 effective arithmetic and the direct effectivity prime-supply programme are untouched. No finite-bank or global #287 assertion is made.

## 10. Verification and provenance

`verify_urem_family.py` checks finite rational instances of the CRT projection, variance contraction, literal h_l U_r expansion, unit-residue bijection, occupancy inequality, Cauchy with base density, packet weighted Cauchy, rough-Möbius convolution, affine-presieve units and parameter margins. It includes nonzero Urem values and cases where A is not a unit modulo f.

These tests do not prove SW, BDH or asymptotic decay. They do not replay the absent new Lean counterexample. The mathematical arguments in Sections 2–7 and the cited analytic theorem, not the test count, support the paper-level repair.

### Primary references

[M1] J. Maynard, *Primes in arithmetic progressions to large moduli I: Fixed residue classes*, arXiv:2006.06572v2, Definition (6.1), Lemma 13.8. https://arxiv.org/html/2006.06572v2

[M2] J. Maynard, *Primes in arithmetic progressions to large moduli II: Well-factorable estimates*, arXiv:2006.07088v1, Definition 3 (coprimality SW), Lemma 5.4 (rough-number distribution), the proof after Lemma 5.4, and the coefficient reduction in Section 6. https://arxiv.org/html/2006.07088v1

[P] A. Pascadi, *On the exponents of distribution of primes and smooth numbers*, arXiv:2505.00653v2. This paper is relevant to the remaining critical spectral branch, not an extra analytic input to the Urem theorem proved here. https://arxiv.org/html/2505.00653v2

[L] Lean Language Reference, *Validating a Lean Proof* and *Axioms*. The proof type and all binders must be inspected in addition to axiom dependencies. https://lean-lang.org/doc/reference/latest/Axioms/

### User-source provenance

- Latest locally inspected project: Aristotle archive (6); individual hashes and exact excerpts in `SOURCE_INSPECTION.md`.
- `ARISTOTLE_287_SOURCE_E3_V100R_ORDERING_B_PASTE.md`, Sections 1–4: the source and family proof architecture reconstructed above.
- `AUDIT_REPORT.md` and `SOURCE_EVIDENCE(1).md` in the archive-6 reconciliation: previous formal-interface and normalization findings.
- Latest `OrdinaryBVUremProviderScoped` refutation: user-provided theorem signature only; body unavailable in the inspected materials.
