# Erdős #287 — actual-modulus source-fit repair and effective-finisher audit

**8 October 2026 | Independent written mathematical audit — NOT a Lean kernel certificate**

## Scope and provenance

Examined the user's previously supplied Aristotle tar archive (`output-final_aristotle/RequestProject/Erdos287/SourceChain/Physical/`) and the user's later Aristotle completion report. The archive is **older** than that report: it contains `Factorization/Support.lean`, `ellX_tensor`, and `atom_factorization_clean`, but it does not contain the report's newly added `Erdos287/Effective/` modules or `physCoefAtom_reassemble`. Their build results are therefore **reported, not independently reproduced**. The environment has no `lean` or `lake` executable and lacks a complete `.lake` dependency tree. A search of the connected GitHub code index did not locate the later Aristotle repository by the relevant theorem name.

The main additional written result below is a *source-specific mixed-parity support lemma*. It has not been translated to a completed, compiled Lean proof.

## Theorem A — complete actual modulus lies in the upper Rosser–Iwaniec support

Fix a scalar sector `(J,P)` with `BoxAdm J P`, a labelled tuple of pairwise distinct high primes `q = (q_1,...,q_J)` from the assigned high boxes, and a nonzero low-sieve coefficient `κ_J(b)`. Assume `ScalarParams.Good` (in particular `X>1`, `T>=2`). Set

\[
D_{\rm hi}:=D_{\rm int}^{1+\tau},\quad
D_{\rm low}:=D_{\rm int}^{e_0},\quad
D_{\rm tot}=D_{\rm hi}D_{\rm low}=X^{59/100},\quad
d=b\prod_{i=1}^Jq_i.
\]

The high primes are all greater than `u_0` and the distinct low primes of `b` are all strictly less than `u_0`, so the two prime groups have disjoint supports. Let the high primes sorted decreasingly be `Q_1>...>Q_J`, and low primes be `r_1>...>r_t`. Since the box list is weakly decreasing and every actual prime is at most its box upper endpoint, the **sorted** high list is pointwise at most the weakly decreasing box upper endpoint list `U_1>=...>=U_J` (repeated boxes are permitted). This pointwise sorting lemma is a necessary separate Lean obligation.

- If a global odd index `k` satisfies `k<=J`, the existing `boxVec_vecHyp` gives

  \[
  Q_1\cdots Q_{k-1}Q_k^3\le U_1\cdots U_{k-1}U_k^3
  \le D_{\rm hi}\le D_{\rm tot}.
  \]

- If a global odd index `k=J+s` has `s>=1`, all high primes precede the low primes and the needed expression is

  \[
  \Bigl(\prod_{i=1}^JQ_i\Bigr)
  r_1\cdots r_{s-1}r_s^3.
  \]

  If `J` is even, `s` is odd and `kappa_sector` gives the low `DplusSet(D_low)` bound; if `J` is odd, `s` is even and `kappa_sector` gives the low `DminusSet(D_low)` bound. In either case, `VecHyp.prod_le` bounds the entire high product by `D_hi`, so this expression is `<= D_hi D_low = D_tot`.

Hence **for every actual nonzero scalar atom**

\[
\boxed{d\in\mathcal D^+(D_{\rm tot})=\mathcal D^+(X^{59/100}).}
\]

For `0<κ<10^{-5}`, `59/100 < 3/5 - 50κ`, so by monotonicity of the support threshold,

\[
\boxed{d\in\mathcal D^+(X^{3/5-50\kappa}).}
\]

For avoidance of doubt, the coarse inequality `d <= D_tot` alone is insufficient: e.g. `14 <= 100` but the largest-prime odd-prefix test fails because `7^3 > 100`. The extra parity-sensitive low/high structure is essential.

This establishes at the written-mathematics level the precise **actual-modulus membership** that the latest Aristotle report leaves unproved. It does **not** grant the convolutional factor independence needed by Proposition 4.4: for that one must retain the already proved **box-fixed** `atomColour`, signed `ellX_tensor`, low/high disjointness, and coefficient one-boundedness. One cannot freely use an independently chosen colouring for each `d` to create a factorized global coefficient.

### Suggested Lean interface (statements only; no kernel proof claimed)

- `actual_high_sorted_majorized`: the sorted list of prime factors of `∏q_i` is entrywise bounded by sorted `boxTop(P i)` (including repeated boxes).
- `Dplus_append_of_parity`: concatenating a high `Dplus` prime list of length `J` and a smaller low `Dplus` list when `Even J`, or a low `Dminus` list when `Odd J`, yields `Dplus` at product of support levels.
- `actual_modulus_Dplus_Dtot`: after `BoxAdm`, `kappa J b ≠ 0`, `q∈tuples J P`, prove `Factor.InDplus S.Dtot (b*∏q_i)`; alternatively first prove `Sieve.DplusSet S.Dtot (b*∏q_i).primeFactors` and convert via the ordered prime-factor list.
- `actual_modulus_Dplus_pascadi`: monotonicity to `X^(3/5-50κ)` for `0<κ<10^-5`.

These statements use the **exact** source index and weight predicates, not a new abstract sieve coefficient.

**Lean-efficient implementation:** work first with the `Finset` of actual high/low prime factors. For a high prime `p`, the `above` set in the full modulus contains precisely the larger high primes; for a low prime `p`, it is the disjoint union of *all* high primes and the larger low primes. Therefore

\[
\#\mathrm{above}_{d}(p)=J+\#\mathrm{above}_{b}(p)
\]

for low `p`, which translates the `Even J`/`Odd J` switch into the exact `DplusSet`/`DminusSet` split. This may be more robust than first proving complete `primeFactorsList` concatenation, especially with repeated high boxes. After the `Finset` theorem, transfer it to `Factor.InDplus` using squarefreeness and the sorted prime list.

**Uniform-in-X variation safeguard:** the number of high boxes is mathematically independent of `X` once `T` is fixed, since

\[
D_j=D_{m int}^{e_0^2(1+	au)^j},\quad
D_j\le\sqrt{D_{m int}}\iff e_0^2(1+	au)^j\le	frac12
\]

for `D_int>1`. The right-hand side depends on `T` only. A Lean theorem `H_eq_H_of_same_T` should precede treating the claimed variation bound `∑_{J≤T²} H^J 3^J` as an `X`-independent constant.

## Theorem B — discharge of actual atom parameters

Define

\[
e_0=1/T,\quad\tau=e_0^9,\quad
\beta=\frac{59e_0}{100(1+e_0+e_0^9)},\quad
D_{\rm low}=X^\beta.
\]

For fixed `0<κ<10^-5`, choose any integer `T>max(2,100/κ)` (the choice depends on the fixed κ, not on X). Then

\[
0<\beta<\frac{59}{100T}<\frac{\kappa}{100},\qquad
4\beta<\kappa.
\]

Take the factorization parameter `δ=κ`. For `X>1`,

\[
D_{\rm low}^2=X^{2\beta}\le X^{\kappa/2}=X^{\delta/2}.
\]

For any actual critical cell satisfying `X^(3κ) <= N <= X^(1/3+κ/2)`, we also have

\[
X^{2\delta}\le N/D_{\rm low},\qquad
N\le X^{1/3+\delta}.
\]

The first inequality follows from `N/Dlow >= X^(3κ-β) >= X^(2κ)` because `β<κ`. The second is immediate.

Thus `AtomParams S κ N` and the additional premise of `atom_factorization_clean` are **mathematically discharged by a fixed parameter choice**, provided the actual source parameter-selection theorem is constructed in Lean. Existing `ScalarParams.Good` by itself (`T>=2`, `X>1`) does not imply these claims.

**Analytic exponent translation:** `atom_factorization_clean` yields `Sys53` with parameter `κ/2`. Pascadi Proposition 4.4 needs `Q1<=N x^-ε`, `N²Q2Q3²<=x^(1-15ε)`, `N²Q2^5 Q3²<=x^(2-40ε)`. Taking the original paper's `ε=κ/2000` leaves strict margins: `κ/2>40κ/2000`, hence also `κ/2>15κ/2000`. Dyadic constants require the usual fixed power reserve.

## Source-to-provider dictionary: what was and was not discharged

Pascadi [arXiv:2505.00653v2, Proposition 4.4] is **not** conditional on `Dplus` membership. It applies to three **one-bounded unary convolution coefficients** at legal lengths, with a rough/Siegel–Walfisz `alpha_n`, the full original congruence and its fixed residue `a`, and all listed modulus/range conditions. `Dplus` is used by Proposition 5.2 to guarantee allocation, not to license arbitrary correlated coefficients.

The user's reported `ellX_tensor`, `physCoefAtom_reassemble`, `typeII_source_decomp`, `physOB_source_eq_T` should therefore be used to show, in that order:

1. signed scalar source `ellX` equals a fixed finite-variation sum of box-fixed, one-bounded 3-fold atoms;
2. the actual pre-Cauchy Type-II/Ordering-B source equals the reconstructed atom-indexed source, with no duplicated designated-coordinate pair summation;
3. each cell's coefficient, coprimality, residue and dyadic length contracts match the **specific** cited analytic theorem;
4. the SW/roughness condition on the variable `alpha_n` holds at that source, not just on a generic coefficient;
5. the physical **growing base `f` and residue `c`** are not present in Pascadi Proposition 4.4's printed fixed-`a` theorem. They require the separate base-conditioned actual-atom W4 proof/provider described in the user's `Final proof.pdf` or another legitimate theorem. A source factorization alone does not close that extension.

Current remaining deep analytic hypotheses (no claim of discharge): provider for the actual varying-base nonzero Fourier/Poisson remainder; any missing BV/BDH source adaptation, remainders, fundamental-lemma comparisons, `Lambda` to primes and powers, and the seven-block asymptotic consumer. The precise final list depends on the latest actual `Tail287` theorem signature, which was **not** present in the supplied older archive.

## Effective track: universally quantified arithmetic vs prime supply

For `L_h=lcm(1,...,h)`, one can prove the classical explicit inequality `L_h<=4^(h-1)` for every integer `h>=1` by induction using

\[
L_{2n}\mid L_n\binom{2n}n,\qquad
L_{2n+1}\mid L_{n+1}\binom{2n+1}n.
\]

The binomial factors satisfy `C(2n,n)<=4^n`, `C(2n+1,n)<=4^n`. The existing (latest reported, not in archive) Lean hypothesis `L_h<=3^h` is **not** discharged by testing only `h<=40`. Replace it by an actually proved `4^(h-1)` estimate and adjust the exponent budget.

For the much narrower reported `onset_exp : M>=exp 12 -> H_*(M)>=10`, a separate short proof does **not** need the full lcm exponential theorem: `L_10=2520`, `B_10=7381`, so `10 B_10=73810<exp 12`; monotonicity of `h B_h` yields `H_*(M)>=10` whenever `M>=exp 12`. This is a shortcut for that result only; it does not establish the growing-height `h=floor(log M/2)` theorem.

The exact V103 one-draw object is

\[
\nu_p=\sum_{q\mid p-1}\frac{v_q(p-1)\log q}{\log(p-1)}\delta_{\log q/\log(p-1)},\quad
\nu_M=\frac1{\#\{p:M/2<p\le M\}}\sum_{M/2<p\le M,\ p\text{ prime}}\nu_p,
\]

\[
\eta_M=\frac{\log(K_*(M)+1)}{\log M},\qquad
T_M=\int_{[0,1]}(u-1+\eta_M)_+\,d\nu_M(u).
\]

All occurrences `v_q` (prime multiplicity), odd-prime window, `log(p-1)>0`, `0<eta<1/2` and the strict positivity threshold must appear literally in the Lean predicates. `T_M>0 => not Counterexample287(M)` is an implication; `T_M>0` for all large M, the explicit one-hinge estimate, and finite-bank verification remain **unproved**.

## Delivery and status

| Item | Status |
|---|---|
| Actual-modulus `Dplus` | New written proof above, **not kernel-proved** |
| `Dlow²` and critical atom parameters | Discharged at written-mathematics level; needs parameter-instance Lean theorem |
| Pascadi greedy/3-colour, `ellX_tensor` | Reported kernel PASS (latest report); no independent rebuild |
| Atom-indexed Type-II split removal | Reported kernel PASS (latest report); old archive contains only free `SplitRule` |
| Full physical Ordering-B and spectral estimate | OPEN pending exact theorem dictionary and analytic proof audit |
| `one_prime_finisher`, `hingeT_pos` implication | Reported formal PASS; not present in inspected old tar |
| universal LCM/large-height lemma | OPEN in formal code; valid classical inequality supplied |
| effective uniform hinge positivity, finite bank | OPEN |
| provider-free infinite `Tail287` | OPEN |

**No new Lean theorem was declared proved in this note.** No fresh `lake build` or `#print axioms` was possible in the current environment. To certify the missing results, feed these statements into the latest Aristotle checkout and require kernel-compiled proofs with the intended theorem signatures and only standard axiom dependencies.

## Primary references

- A. Pascadi, *On the exponents of distribution of primes and smooth numbers*, arXiv:2505.00653v2, Definition 5.1, Proposition 4.4, Proposition 5.2, §5.1: https://arxiv.org/html/2505.00653v2
- Previously supplied V103, *An effective logarithmic-row certificate and a one-draw endpoint reduction*, 8 October 2026, §3–9.
