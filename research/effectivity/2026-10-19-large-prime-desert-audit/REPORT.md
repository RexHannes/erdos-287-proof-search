# Erdős #287 — hostile audit of the large-prime-row desert

Date: 19 October 2026. Scope: effective/post-effective research only.

## Verdict

**REPAIR -> PASS at the stated scoped-theorem level.** The numerator lemma, large-prime-row desert, 30/47 adjacent-cofactor implication, effective first moment, and conditional AC-287 consumer all survive. Their written proofs are supplied below with explicit published inputs and exact numerical gates. AC-287 itself, original prime-output lower bounds, effective infinite-tail exclusion, and Global #287 remain **OPEN**.

This is a fresh mathematical derivation and separately written implementation, not an independent human referee's report or a Lean proof. Published Dusart and BMOR theorems are imported at their printed unconditional scope. Their internal analytic arguments and external computations are not re-proved by this checker. No finite-bank certificate, pre-effectivity module, original comparison, or prior closing contract is modified or re-certified.

## 1. Source recovery and audit decisions

The immediate source is `erdos287_large_prime_desert_20261019/REPORT.md`, file id `file_00000000113c81f7a625eb28968eeab0`. Its Section 3 stated the numerator lemma without reproducing its proof. Its SOURCE_RECORD was a 19-line path list, not a self-contained dependency archive. The actual proof was recovered from Section 5.1 of `erdos287_effectivity_20261017/REPORT.md`, independently located also inside `erdos287_endpoint_audit_repair_20261017/SOURCE_RECORD.md`.

| Claim | Verdict | Exact interpretation |
|---|---|---|
| Numerator lemma for all real L>=1154 | PASS after source recovery | Direct consequence of two explicit Dusart propositions and a decreasing envelope; NOT an assumed certificate |
| Large-prime-row desert | PASS, hypotheses made explicit | Integer reciprocal mass implies every selected denominator has the stated prime-factor cutoff |
| Physical window and adjacent obstruction | PASS with endpoint clarification | The window starts **above** every possible a<=floor(M/2), not below a |
| Unique prime-cofactor representation | PASS | Includes a proof that the represented prime is the largest prime factor |
| Counterexample => zero adjacent correlation | PASS | Necessary consequence; positivity has not been proved |
| First moment | PASS with an explicit nonnegative lower-boundary atom | Ceil(30M/47) and the strict Chebyshev subtraction are not silently identified |
| First moment => adjacency | FAIL as a proposed inference | Never claimed as a theorem here; exact capacity gap is about 87.97 at L=1154 |
| “Strictly weaker global theorem” language | REPAIR | Witness class is larger; both-composite examples do not prove separation of the universally quantified supply statements |
| Historical J_* >= -MH_B/8 arithmetic | PASS for the coefficient calculation only | 479/100000 is correct; its inherited comparison hypotheses are not independently re-audited here |
| AC-287 / effective tail / Global #287 | OPEN | No new universal existence theorem or counterexample contradiction |

The numerator lemma does not use the 663 support certificates. Those certificates belong to a different consumer estimate. Replaying them would neither be necessary nor sufficient for this lemma.

## 2. Definitions and complete original hypothesis

Let A be a finite set of distinct positive integer denominators, with A subset {2,...,M}, min A=a, max A=M, |A|>=2, and

    sum_(n in A) 1/n = 1.

For a Gap2CE additionally require every consecutive selected gap to be at most two, equivalently no consecutive omitted pair inside [a,M]. Write

    L=log M >=1154,
    B=floor(3L/10), C=2B,
    alpha=30/47, gamma=47/50,
    N=ceil(alpha M),
    L_h=lcm(1,...,h), H_h=sum_(j<=h)1/j, T_h=L_h H_h.

All logs are natural. P^+(n) denotes the largest prime factor for n>=2. The integer 1 is not an allowed selected denominator. From distinctness and |A|>=2,

    1=sum 1/n < |A|/a <= (M-a+1)/a,

hence 2a<M+1 and a<=floor(M/2). Since alpha>1/2, N>a and [N,M] is entirely inside the physical selected-endpoint interval. Omission of M is itself a contradiction.

## 3. Independent proof of the effective numerator lemma

**Theorem N.** For every real L>=1154, M=e^L, and integer 1<=h<=47L/50,

    h T_h < M/2.

### Published inputs, checked in the primary PDF

Dusart [D], printed page 4, Proposition 3.2 states, for x>0,

    psi(x)-theta(x) < (100007/100000) sqrt(x)+(89/50) x^(1/3).

On the same page Proposition 5.1 states theta(x)-x<x/36260 for x>0. Thus

    psi(x) < (36261/36260)x+(100007/100000)sqrt(x)+(89/50)x^(1/3).

No RH assumption or unspecified starting point is inserted. These are imported published theorems, not outputs of our code.

Since log L_h=psi(h) and H_h<=1+log h,

    log(h T_h) <= psi(h)+log h+log(1+log h) <= g(L),

where

    g(L)=(36261/36260)(47L/50)
         +(100007/100000)sqrt(47L/50)
         +(89/50)(47L/50)^(1/3)
         +log L+log(1+log L).

Every nonconstant summand of (g(L)+1)/L decreases on L>=1154. For the log terms, the derivative numerators are 1-log L and 1/(1+log L)-log(1+log L), both negative. The power terms are positive constants times L^(-1/2), L^(-2/3), or L^(-1). This proves decrease on the **entire real interval**, not a finite mesh.

At L0=1154:

    47L0/50 <33^2, 47L0/50 <11^3,
    log1154 <71/10, log(81/10)<21/10.

Consequently

    g(1154) < (36261/36260)(47*1154/50)
              +(100007/100000)*33+(89/50)*11+71/10+21/10
            =207873544603/181300000
            =1146.572226161059... <1153.

Therefore (g(L)+1)/L<1 for every L>=1154. Hence log(hT_h)<L-1 and

    hT_h < M/e < M/2.

This proves N without appealing to an unproved inherited analytic provider.

### Independent exact onset computation, not the infinite proof

At L0, h_max=floor(47L0/50)=1084. The checker constructs L_1084 both by multiplying maximal prime powers and by the gcd/lcm recurrence, verifies equality, and computes T_1084=sum_j L_1084/j as an exact integer. Certified log enclosures give

    log(1084*T_1084) =1089.726557762719482...,
    1154-log2-log(1084*T_1084)=63.580295056720572... .

This is consistent with the user's numerical check. The all-L proof remains the preceding monotonic-envelope argument. The certificate records the actual integer LCM, numerator, and rational enclosures.

## 4. Full p-adic row argument

**Theorem LPD.** Under the reciprocal-sum hypothesis of Section 2, for every selected n,

    P^+(n) < 50M/(47log M).

Gap two is not needed for this theorem; it is needed in Section 5.

Proof. Suppose a prime p>=50M/(47L) divides a selected n. Necessarily p<=M. Let h=floor(M/p)>=1. Then h<=47L/50. Also p>sqrt M: it suffices that e^(L/2)>47L/50, which follows already from the first three terms 1+L/2+L^2/8 of the positive exponential series on this range. Thus h<p and p^2>M.

For a denominator-clearing proof with no undefined modular rational, set W=lcm(1,...,M)=p Q. Its p-adic valuation is exactly one, so Q is a unit modulo p. Multiplying the reciprocal identity by W, terms with p not dividing n vanish modulo p. For n=pj, j<=h<p, the remaining term is congruent to Q j^(-1). Dividing by Q modulo p gives

    sum_(j in J_p) j^(-1)=0 mod p,
    J_p={j<=h:pj in A}.

The row is nonempty because the chosen selected n is divisible by p. Since p>h, L_h is a unit modulo p. Its cleared numerator

    N_p=sum_(j in J_p)L_h/j

is an integer satisfying p|N_p and 0<N_p<=T_h. But by the floor identity and Theorem N,

    p>M/(h+1)>=M/(2h)>T_h.

This is impossible. This establishes the strict conclusion, including equality in the excluded threshold p>=50M/(47L). Empty rows have numerator zero and are not contradictions. QED.

## 5. Adjacent cofactor implication with exact endpoints

For n>=2 put c(n)=n/P^+(n). If N<=n<=M and c(n)<=C=2B, then

    P^+(n)>=alpha M/C >= alpha M/((3/5)L)=50M/(47L).

By Theorem LPD, n is omitted. Therefore under Gap2CE the set

    G_M={n integer:N<=n<=M, c(n)<=2B}

has no consecutive pair and cannot contain M. In particular c(M)>47L/50>2B.

The predecessor/successor prime-centred statements follow pointwise: a prime in the window has c(p)=1, and a qualifying neighbour is also omitted. For p-1 use p>=N+1; for p+1 use p<M so p+1<=M. The top endpoint p+1=M yields an endpoint contradiction, not an out-of-range exception.

The wording in the proposed audit prompt that the physical interval should start “below” the upper bound for a is reversed: it starts above floor(M/2), so certainly after a and before/equal to M.

### Unique representation

Define the original nonnegative weight

    F_M(n)=sum_(1<=c<=C, n=cp, p prime) log p.

On n>=N, we have n>C^2. One proof is e^L>L^3/6 and alpha L^3/6>(9/25)L^2 for L>=1154. If cp=c'q with p!=q and c,c'<=C, Euclid's lemma implies p|c' and q|c, hence n<=C^2, contradiction. Thus at most one representation exists.

Moreover, in a representation p=n/c>C. Every prime divisor of c is <=C<p, so p=P^+(n). Conversely c(n)<=C supplies this representation. Consequently F_M(n)>0 iff n in G_M, and 0<=F_M(n)<=L.

### Conditional closing consumer, not existence

For every Gap2CE in the range,

    S_AC(M):=sum_(n=N)^(M-1) F_M(n)F_M(n+1)=0.              (AC-consumer)

Both factors are nonnegative; a positive term would force adjacent omitted positions inside [a,M]. Thus a theorem S_AC(M)>0 for **every integer M>U_fin** would exclude the tail. There is no replacement of the original P_M source: this is a separate counterexample-exclusion route.

A positive term is equivalent to n=ap, n+1=bq, with a,b<=C and p,q genuine primes, satisfying bq-ap=1. Necessarily gcd(a,b)=1, p!=q, and a,b have opposite parity (both large primes are odd). These exact restrictions are retained in the tests.

Both-composite witnesses, such as 668=4*167 and 669=3*223, demonstrate a larger **individual witness class** than witnesses requiring one position to be prime. They do not prove that the universal AC theorem is logically strictly weaker than the universal earlier prime-centred existence statement.

## 6. Exact effective first moment

### BMOR q=3 -> ordinary theta

BMOR [B], Theorems 1.1-1.2 and (1.10)-(1.11), printed pages 4-5, give for a=1,2 and x>=8*10^9:

    |theta(x;3,a)-x/2| < x/(840log x).

Since theta(x)=theta(x;3,1)+theta(x;3,2)+log3,

    |theta(x)-x|<x/(420log x)+log3<x/(400log x).

For the last step 1/400-1/420=1/8400. The function x/log x increases for x>e, and the checker verifies log3 < x/(8400log x) at x=8*10^9. This explicitly derives the q=1 corollary; it is not attributed as the literal statement of BMOR at q=1.

### Endpoints and floors

For c<=C, put x_c=M/c, y_c=alpha M/c. Exactly,

    sum_(N<=cp<=M, p prime)log p
      =theta(x_c)-theta(y_c)+eta_c,

where eta_c=log(y_c) if alpha M is an integer and y_c is prime, and eta_c=0 otherwise. Thus eta_c>=0. Equivalently, theta subtraction counts the strict lower interval alpha M<cp<=M, a subset of the intended closed integer interval. It is legitimate to discard eta_c for a lower bound, but not to call the two sums identical.

All endpoints are above 8*10^9. Indeed C<=3L/5 and

    log y_c >= L-log(47L/50) > .99L > log(8*10^9).

The first strict bound holds at 1154 and thereafter because log(47L/50)/L decreases. The BMOR corollary therefore gives

    theta(x_c)-theta(y_c)
      > (M/c)[17/47-(1+30/47)/(400*.99L)]
      > (M/c)[17/47-1/(198L)]
      > M/(3c).

Summing the finite sums over every c<=C proves, with no missing endpoint,

    sum_(n=N)^M F_M(n) > (M/3) H_C,  C=2B.                 (FM)

Only one-prime distribution is used. This does not prove two-point correlation.

### Exact capacity boundary

The number of integers in the window is m=M-N+1. Any subset with no consecutive pair has at most ceil(m/2) elements. Under Gap2CE, since M is also absent, the stronger bound ceil((m-1)/2) is available. By uniqueness and F_M<=L, (FM) only guarantees |G_M|>M H_C/(3L).

At L=1154, C=692, the guaranteed fraction is 0.002055899477137168..., while the leading independent-set capacity is 17/94=0.1808510638.... Their ratio is 87.966880599445292.... These are comparisons of the guaranteed lower bound with capacity, not estimates of the true number of adjacent pairs. Finite tests of actual F_M do not establish an every-scale result.

## 7. Effective splice and its un-replayed dependency

The exact inherited U_fin is copied from the controlling consumer verifier and checked bytewise. Its decimal SHA-256 is

    9528aa36b33895dd9827b831036734d23b4a1a853468ebde6eeb7330ace3c61e.

It has 502 digits and exceeds 2^1665. Certified rational logs give 1665log2>1154; hence every integer M>=U_fin+1 lies in the theorem domain. This checks the **onset connection**, not the finite exclusion theorem. The original finite proof is neither edited nor replayed.

If AC-287 is eventually proved at every such M, then [2,U_fin] from a valid finite certificate and [U_fin+1,infinity) from the new tail argument meet with no gap. That final inference remains conditional on AC positivity and the preserved finite-bank theorem. It is not a global proof now.

## 8. Current external arithmetic scope audit

No inspected theorem supplies S_AC(M)>0 at every specified post-bank scale. This is a statement about this audit, not an exhaustive impossibility claim.

* Tao-Teravainen [TT], Theorem 1.8, gives a quantitative joint smooth-number law on a set of scales of logarithmic density one, with an exceptional set and absolute logarithmic error. It states parameter uniformity, so it should not be dismissed as merely a fixed-parameter theorem. However its exceptional-scale qualification alone prevents the required every-M conclusion. The logarithmic-cofactor endpoint and the very small upper-tail intersection additionally need a source-specific error budget.
* The retrieved Lu-Wang-Wu [HLC] preprint's Theorem 1 concerns sum_(p<=x)mu(p+2)=o(pi(x)). It neither asserts two-prime counts bq-ap=1 with a,b<=.6log M nor an explicit onset for AC. No analytic result from that manuscript is used in the present proof.
* A fixed-parameter joint Dickman limit, even if established, cannot on its own supply positivity in a moving endpoint window with normalized exponent 1-O(loglog M/log M). No unchecked model-generated 2026 manuscript is imported as a theorem here.

The same-source prime-output and signed J_* routes remain valid parallel OPEN goals. We do not rename the determinant incidence as proved prime supply, optimize the 30/47 window, or count another first-moment rearrangement as terminal progress.

## 9. Verification and repository boundary

Run from this directory:

    python -S verify_desert.py --output normal.json
    python -S -O verify_desert.py --output optimized.json
    cmp normal.json optimized.json

All acceptance gates use explicit exceptions and integers/rationals. log_bounds uses the atanh series after binary range reduction, dyadic outward enclosures of its argument, a positive geometric tail, and final outward rounding. Decimal strings are display only. The certificate records exact enclosures.

Tests include independent LCM construction, the universal lemma's scalar gates, 8,178 nonempty small row subsets, 126,128 exact physical denominator-clearing identities, 9,848 unique cofactor records, 1,920 actual small adjacent determinant records, and 20 endpoint-decomposition checks. Small literal fixtures use their verified original logarithmic B but do not satisfy the post-bank domain and are not counted as new finite exclusions.

Eight deliberately false mathematical variants are tested in normal and optimized Python. They are specific regression/negative controls, not evidence that every possible proof or implementation defect has been excluded. The run receipt states what actually executed.

The research branch adds only this audit packet. No README/finite-bank/pre-effectivity/original-contract change is authorized by this packet. A PR is for scoped audit review, not acceptance of a proof of #287. All source inputs relevant to these scoped deductions are preserved in SOURCE_RECORD.md; the full frozen consumer certificate is not a dependency of the direct numerator proof.

## References and exact use

[D] Pierre Dusart, Estimates of Some Functions Over Primes without R.H., arXiv:1002.0442v1, Propositions 3.2 and 5.1, printed p.4. https://arxiv.org/pdf/1002.0442 . The primary page image was inspected; the two explicit global bounds are the only imported ingredients for N.

[B] Michael A. Bennett, Greg Martin, Kevin O'Bryant, Andrew Rechnitzer, Explicit bounds for primes in arithmetic progressions, arXiv:1802.00085v3, Theorems 1.1-1.2, equations (1.10)-(1.12), printed pp.4-5. https://arxiv.org/pdf/1802.00085 . Primary page images inspected. Only the q=3 specialization is needed.

[TT] Terence Tao, Joni Teravainen, Quantitative correlations and some problems on prime factors of consecutive integers, arXiv:2512.01739v2, Theorem 1.8. https://arxiv.org/html/2512.01739v2 . Scope audit only; no theorem used to establish AC.

[HLC] Guangshi Lu, Zhiwei Wang, Jie Wu, On the Hardy-Littlewood-Chowla Conjecture, arXiv:2610.20242v1, Theorem 1 and Remark 1. https://arxiv.org/html/2610.20242v1 . Scope audit only; no claimed proof verification.

## Status ledger

**What done — BANK at explicit paper-proof scope:** numerator lemma independently derived from published estimates with all-real-L proof; exact p-adic row clearing, large-prime desert, complete 30/47 adjacent implication, corrected first-moment endpoint formula, and conditional AC consumer verified. Source provenance and exact checker are repaired. No terminal PAY.

**What remains — OPEN:** every-scale AC-287 two-prime existence, original prime-output lower bound or equivalent signed theorem, effective infinite-tail exclusion, and Global #287. Finite-bank exclusion is preserved, not re-certified in this audit.

**Next frontier:** investigate genuine two-point arithmetic for bq-ap=1 in the exact window and cofactor range, or a complete reciprocal-row/carry incompatibility. One-point mass and a necessary omission condition cannot substitute for the remaining theorem.
