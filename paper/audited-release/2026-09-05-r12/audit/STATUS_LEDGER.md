# Authoritative Status and Capacity Ledger — R12

**Cut-off:** 5 September 2026
**Scope:** Erdős #287 effectivity programme only
**Global verdict:** **OPEN — no solution claimed**

## 1. Exact directed ledger

The current target is

\[
C_{\mathrm{target}}=\frac{177213}{200000000000}=8.86065\times10^{-7}.
\]

The old incremental subtotal and old `V<50` edge were

\[
C_{\mathrm{old}}=\frac{5495943872}{10^{16}},\qquad
C_{V<50}=\frac{2459}{10^{11}}.
\]

The certified replacement edge is banked conservatively as

\[
C_{V<1000}=\frac{722}{10^{12}},
\]

with the sharper deterministic value

\[
\frac{1571209497}{2182000000000000000}
 =7.200776796516957\times10^{-10}.
\]

Consequently,

\[
C_{\mathrm{cert}}
=C_{\mathrm{old}}-C_{V<50}+C_{V<1000}
=\frac{20536187}{39062500000000}
=5.257263872\times10^{-7},
\]

and

\[
C_{\mathrm{rem}}
=C_{\mathrm{target}}-C_{\mathrm{cert}}
=\frac{225211633}{625000000000000}
=3.603386128\times10^{-7}.
\]

The exact identity `C_cert + C_rem = C_target` has been replayed.

## 2. Physical aggregate criterion

For the physical `lambda(b)`-weighted long-fibre source, the exact-rational replay gives the conservative normalisation coefficient

\[
\kappa_{\mathrm{phys}}
 < 3.0650024384947045\times10^{-6}.
\]

It follows that the bankable sufficient target is

\[
C_{\mathrm{agg}}\le \frac{69}{5000}=0.0138,
\]

whose normalised charge is

\[
3.6005626127419187\times10^{-7}<C_{\mathrm{rem}}.
\]

The replayed critical constant satisfies

\[
C_{\mathrm{crit}}>0.013821652054200405.
\]

**Status:** the implication from the aggregate square-function estimate to medium-`k` closure is **ANALYTICALLY-PROVED / CONDITIONAL**. The aggregate estimate is **OPEN**.

## 3. Complete-period endpoint and residual allowance

The complete-period endpoint main is certified by the Farey covariance identity and the physical Euler product:

\[
C_{\mathrm{endpoint}}<\frac{469}{75000}=0.006253333\ldots.
\]

The separately replayed components are

\[
C_{\mathrm{diag}}<0.004598361975495641,
\qquad
C_{\mathrm{off}}<0.0015591715849480388.
\]

Therefore the exact remaining covariance allowance is

\[
\frac{69}{5000}-\frac{469}{75000}
=\frac{283}{37500}
=0.007546666\ldots.
\]

The live theorem must retain the physical outer coefficient `lambda(b)` and prove, in the same quadratic norm,

\[
C_F+2C_{ED}+C_{DD}+C_S<\frac{283}{37500}.
\]

Here `F` is the finite-period endpoint remainder, `ED` is endpoint–derivative covariance, `DD` is derivative–derivative covariance, and `S` is the no-lattice splice. The factor `2` on `ED` is mandatory.

**Status:** complete-period main **KERNEL-PROVED / FINITE-CERTIFIED / AUDITED**; residual covariance **OPEN**.

## 4. Exact edge certificate

For `T=1000`, the fixed-point enumerator gives

\[
A_1(1000)<2619.379769810346<2620,
\qquad
A_2(1000)<2817.138890836101<2818.
\]

Together with `|K^\perp|<=3/2`, the physical outer factor, the summatory `lambda` bound, and the frozen slab, this closes every fibre with `V_{b,c}<1000`.

**Status:** **FINITE-CERTIFIED / AUDITED / CLOSED**.

## 5. Retired statements and ledger firewalls

1. The unweighted per-fibre statement `C_joint <= 0.09` is false. A one-point physical fibre gives `C_joint >= 9/64`.
2. The per-prime insertion of the global singular-series factor is source-mismatched. The physical factor occurs once.
3. The old `V<50` charge is removed before inserting the `V<1000` replacement; both may not coexist.
4. The full half-divisor replacement chart and the incremental medium chart are alternatives. Their charges may not be combined.
5. `Z(s,s)=0` controls the diagonal Euler algebra only; it does not by itself bound the directed anti-diagonal Perron truncation.
6. The complete-period endpoint main is not the complete joined covariance.

## 6. Downstream status

| Stage | Authoritative status | Entry condition |
|---|---|---|
| Medium-`k` | **OPEN; strictly reduced** | Prove the physical weighted covariance or equivalent all-`q` discrepancy within the exact allowance. |
| Two-high | **OPEN; not entered** | Medium-`k` must close first. |
| Signed floor | **OPEN** | Structural compiler exists, but no banked physical numerical boundary certificate exists. |
| Maynard | **OPEN; not entered** | Upstream source and floor guards must close before effectivisation. |
| Erdős #287 | **OPEN** | No upstream stage may be skipped. |
