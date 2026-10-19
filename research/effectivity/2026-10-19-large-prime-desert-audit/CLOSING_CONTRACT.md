# Erdős #287 — scoped desert audit contract

Date: 19 October 2026. **AC-287 / effective tail / Global #287: OPEN.**

## Audited inputs

For L=log M>=1154, B=floor(3L/10), N=ceil(30M/47):

1. The numerator lemma h T_h<M/2 for every integer 1<=h<=47L/50 is proved
   directly from Dusart's explicit global estimates and a decreasing envelope.
2. Under the original reciprocal-sum-one hypothesis, selected n must satisfy
   P^+(n)<50M/(47L). The proof includes p^2>M, exact denominator clearing,
   nonempty-row positivity, the unit LCM and strict threshold inequalities.
3. Under Gap2CE, every n in [N,M] with n/P^+(n)<=2B is omitted. M cannot belong
   to that set; no consecutive pair can belong to it.
4. F_M(n)=sum_(c<=2B,n=cp,p prime)log p has at most one representation in the
   window, detects exactly this cofactor set, and has effective first moment
   sum_(N<=n<=M)F_M(n)>(M/3)H_(2B). The closed lower endpoint is included.

The published inputs retain their printed scopes. The new verifier checks exact
scalar gates and finite algebra, not the external analytic proofs or AC existence.
No finite exclusion or pre-effectivity proof is changed or re-run.

## Exact terminal alternative — still unpaid

Prove for every integer M>=U_fin+1 that

    S_AC(M)=sum_(n=N)^(M-1) F_M(n)F_M(n+1)>0.

This would contradict the audited zero-correlation implication of Gap2CE(M).
A positive term is a genuine two-prime determinant solution bq-ap=1, with
1<=a,b<=2B, N<=ap<M, and bq=ap+1<=M. Both-composite positions are allowed.
The coefficients necessarily are coprime and of opposite parity at these scales.

The exact inherited U_fin has 502 digits and SHA-256
9528aa36b33895dd9827b831036734d23b4a1a853468ebde6eeb7330ace3c61e.
Its bytes and log-domain connection are checked. Its exclusion certificate is NOT
replayed here. A final global theorem still needs the valid finite exclusion on
[2,U_fin] and an effective tail on [U_fin+1,infinity), without any gap.

## Research continuation

Use this audit as a scoped bank, not as a new prime-supply theorem. Investigate
source-matched two-point arithmetic for bq-ap=1, or a genuinely complete
reciprocal-row/carry contradiction. Do not spend the next run optimizing the
30/47 coefficient or treating a one-point mass estimate as adjacency.

Keep all existing source-exact prime-output and signed J_* routes as parallel
OPEN alternatives. This file does not replace or edit the repository's original
closing contracts, finite-bank proofs, or pre-effectivity sources.

**What done** — Numerator dependency, p-adic desert, adjacent implication,
first-moment endpoints and conditional consumer audited with complete proofs.

**What remains** — Every-scale AC-287 positivity, effective infinite-tail exclusion,
original prime-output closure or an equivalent full contradiction. Global #287 OPEN.

**Next frontier** — Genuine two-prime correlation or a complete counterexample-dependent
contradiction; not another reformulation or isolated finite example.
