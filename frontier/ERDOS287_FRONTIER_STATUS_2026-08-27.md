# Erdős Problem #287 — Current Research Frontier (27 Aug 2026)

**Status: OPEN. This repository does not claim a proof of Erdős #287 or twin-prime infinitude.**

## Latest controlling correction

The earlier generic determinant-one label

`AFFINE287-DET1-HYBRID-MQ45`

is now **superseded as the controlling source**. The reason is source provenance: the actual #287 prime term must first be decomposed literally from `Lambda(2mn+s)`, not inferred from historical shifted-Möbius Gate notation.

The exact Vaughan decomposition is now recorded as a source PASS, proper prime-power outer terms are negligible with relative margin `X^(-1/6+o(1))`, and the first true analytic open is

`AFFINE287-PRIME-MODULUS-MU-TWOOUTER45`.

## Literal prime-outer packet

For `s = +/-1`, after the exact affine Vaughan decomposition with `U=V=X^(1/3)`, the hard prime-outer cell is

```text
V_{pi,s}(D,P,R)
 = sum_{d p r = 2mn+s}
   xi_pi(m) kappa_pi(n) mu(d) log(p) W_{pi,s}
   - source-matched main term,
```

with

```text
MN ~ X,
X^(sigma/3) < M <= X^sigma < X^(1/6),
D,P > X^(1/3-o(1)),
D P R ~ X,
R < X^(1/3+o(1)).
```

Keeping `p` as prime modulus gives the source-exact two-outer packet

```text
R^{(2)}_{pi,s}(P;D,R)
 = sum_{p~P} log p
   sum_{2mn == -s (mod p)}
   xi_pi(m) kappa_pi(n)
   Delta^{mu,1}_{D,R}((2mn+s)/p)
   - M_{pi,s},
```

where

```text
Delta^{mu,1}_{D,R}(u)
 = sum_{dr=u, d~D, r~R} mu(d) W_D(d) W_R(r).
```

Required saving: `o(X/log X)` or a sufficiently small fixed constant multiple preserving the fixed-certificate margin.

## Exact no-go / source firewalls

- `VAUGHAN-COFACTOR-WELLFACTORABLE45: FALSE` for the literal truncated-Möbius cofactor weight.
- `SINGLETON-TO-GATE1A-COMMONWEIGHT: DIRECT LITERAL ADAPTER FAILS` because the canonical Gate-1A determinant is `2k`, while the affine Vaughan determinant is `+/-1`.
- Direct native QK56 identification remains unproved.
- Vaughan Type-I siblings still carry generated `kappa`; `VAUGHAN-TYPEI-GENERATED-KAPPA45` remains a source/standard adapter pin.

## Current ledger

| Node | Status |
|---|---|
| `FORD-GENERATED-DEPTH-N0-287` | PASS, safe `N0=112` |
| fixed-`g_*` depth | `N0=76` |
| `k=0` depth | `40` |
| `AFFINE287-DET1-HYBRID-MQ45` | SUPERSEDED AS CONTROLLING SOURCE |
| exact Vaughan affine-prime source | PASS |
| proper prime-power outer | PASS / negligible |
| comparison Vaughan matching | OPEN source pin |
| Vaughan Type-I generated-`kappa` | OPEN adapter |
| literal cofactor well-factorability | FALSE |
| direct Gate-1A canonical map | FAIL |
| direct native QK56 map | NOT ESTABLISHED |
| prime-modulus Möbius two-outer structural map | PASS |
| `AFFINE287-PRIME-MODULUS-MU-TWOOUTER45` | **FIRST TRUE ANALYTIC OPEN** |
| `k=0` smooth packet | OPEN |
| remaining fixed-`g_*` census | OPEN |
| FCL | OPEN |
| Erdős #287 | OPEN |

## Current files

- [`ERDOS287_PENDING_PRIME_MODULUS_MU_TWOOUTER_FRONTIER_2026-08-27.md`](ERDOS287_PENDING_PRIME_MODULUS_MU_TWOOUTER_FRONTIER_2026-08-27.md)
- [`ERDOS287_LATEST_SOURCE_UPDATE_V14.tex`](ERDOS287_LATEST_SOURCE_UPDATE_V14.tex)

## Firewall

All of the above is research-level source analysis unless separately identified as part of the trusted finite Lean bank. The finite Lean result remains unchanged.
