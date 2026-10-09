# Re-audit packet: W2.984

**Previous verdicts:** `W3: PASS`; `W2.984: REPAIR — expository, not mathematical`.

The previous referee found no mathematical error, but asked for the affine Chen decomposition
and affine analogues of the \(S_1,S_2,S_3\) estimates to be written in full. These are now in
`AFFINE_CHEN_TRANSFER_W2984.md`, Sections 2–11. We do not claim a verdict.

## What to read, in order

1. **§1.3 (A1)–(A4)**: the four elementary admissibility facts that replace Merikoski's
   smoothness hypothesis. They are kernel-checked in `AffineCRT.lean`.
2. **§2 (Lemma 13)**: the pointwise Chen inequality as printed is **false** for non-squarefree
   \(n\) (kernel counterexample \(n=1925\)). It is repaired by adding \(\frac12\mathrm{sq}(n)\);
   the resulting tail is negligible (§10). The constant is unaffected. Please check that this
   repair is acceptable.
3. **§3**: the literal congruence system for \(p=L_j(t)\) (base \(a_jW\), unit residues, CRT,
   \(\phi(a_jW)=a_j\phi(W)\)). Lemma 3.5 shows that the slope cancels in every main term.
   Remark 3.7 explains how the W2.99 density inference is avoided.
4. **§4**: the affine §6 repair: exceptional set (two-sided), smooth tail, overlap tail (same
   exponent \(y^{-1/2}\)), and Euler evaluation (pairwise coprimality from distinct affine roots).
5. **§5**: the modulus ledger. Total exponent \(\frac12-2\delta+4\delta^2+\epsilon_W\le\frac12-\delta\).
6. **§6 (Lemma 6.1)**: the one place where a *published proof* (not statement) is modified.
   BFM Thm 4.2 / Merikoski Prop 11 factor the conductor as \(ab\) with \(a\mid q_0\). Our bases
   \(a_jW\) may be non-squarefree, so the proof is rechecked step by step with \(a\mid a_jW\).
   **Please check steps 3–6.**
7. **§§7–9**: `AffineChenS1`, `AffineChenS2` (lower bound; sign discipline in §8.2, §8.4–8.6),
   and `AffineChenS3` (switch, support-length checks in §9.4, exceptional prime in Remark 9.4).
8. **§11–13**: the combination, the kernel-checked scalar certificate
   \(\le3.983412536315<3.984\), and the explicit \(\delta\)-budget. The identification of the
   constants is flagged as a paper-level obligation.

## What changed since the `REPAIR` verdict

* New: full written proofs for every affine source transformation, in §§2–11.
* New: a correction to Merikoski's Lemma 13 (§2), with the square tail (§10).
* New: a re-verification of the BV proofs for non-squarefree fixed bases (§6).
* New: Remark 8.3 (the \(Z_{\rm exc}\)-factor is not placed in \(\nu\)) and Remark 9.4
  (exceptional prime in \(S_3\)).
* New: a kernel-checked rational certificate (no floating point) and the \(\delta\)-budget arithmetic.
* Unchanged: the W3 downstream (imported, not rebuilt).

## Lean boundary

The Lean statement is
`W2984 : AffineChenS1Provider P → AffineChenS2Provider P → AffineChenS3Provider P →
AffineChenSquareTailProvider P → ∀ s > 2.984, W3Statement s`,
where `P : W3FrameworkProvider`. Each provider corresponds to exactly one lemma of the paper.
The firewall (statement-level, checked at build time) excludes W2.984, occupancy and contact
conclusions from every provider. No provider is constructed.

**Erdős #287 remains open. W2.984 is asymptotic and ineffective.**
