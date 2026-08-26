# Audit: the Fable SFT / follower-graph proposal for Erdős #287

This is an audit only. It does **not** claim #287 is solved. Every claim below that is
machine-checked is a theorem in `RequestProject/Erdos287/SFTAudit.lean` (plus the existing
kernel); the file builds and uses no `sorry`, `axiom`, `unsafe`, or `native_decide`, and
every cited theorem reduces to the allowed axioms `propext`, `Classical.choice`,
`Quot.sound`.

## Verdict

**Fable's SFT schema matches the certified kernel only partially.** The kernel splits into:

* a **local, genuinely SFT-style** *gap layer* (`holes_isolated`,
  `blockerPair_contradiction`); and
* an **essentially non-local** *arithmetic layer* (`topLayer_congruence`,
  `primePower_window_exclusion`, `Gap2CE.primeFree`) that depends on the global parameters
  `N`, `M`, `q = pᵉ`, `⌊M/q⌋`, and the top-layer maximum.

A single finite alphabet with a fixed-radius local transition rule captures the gap layer
but **not** the arithmetic layer, so the literal SFT schema is not valid as a
representation of the whole kernel.

## Task 1 — are the kernel facts bounded-window local constraints over a finite alphabet?

| Kernel fact | Local / SFT after fixing a scale? | Why |
|---|---|---|
| `Gap2CE.holes_isolated` | **Yes** (radius-1 SFT) | forbids the single 2-block `(hole, hole)` in the membership word |
| `Gap2CE.blockerPair_contradiction` | **Yes** | same forbidden block, restated |
| `topLayer_congruence` | **No** | a congruence mod `p` over the *top layer* — needs the global top-layer maximum `e = maxₐ vₚ(a)` and the global relation `∑ 1/a = 1`; the modulus `p` is unbounded |
| `primePower_window_exclusion` | **No** | threshold `p > C(⌊M/q⌋)` depends on the global scale `⌊M/q⌋`; `p` unbounded |
| `Gap2CE.primeFree` | **No** | uses the global size bounds `M ≥ 8152` and `N > M/8`, plus the window count |

### The local part is a true SFT (machine-checked)

Over the alphabet `Cell = {inA, hole}`, define the membership word
`Gap2CE.word ce n = if n ∈ ce.A then inA else hole`. Then:

* `Gap2CE.word_locallyAdmissible` — on every window position `n ∈ [N, M-1]` the block
  `(word n, word (n+1))` is **not** `(hole, hole)`. This is exactly `holes_isolated` in
  symbolic form: the gap constraint *is* a nearest-neighbour subshift of finite type.

### The arithmetic part is not a fixed finite local rule (machine-checked obstructions)

* `modulus_alphabet_unbounded : ∀ B, ∃ p, B < p ∧ p.Prime` — the residue modulus ranges
  over all primes, so there is no fixed finite residue alphabet `ℤ/p`.
* Scale-dependence of the exclusion rule:
  * `excludedPP_three_two : ExcludedPP 3 2` (`⌊3/2⌋ = 1`, `C 1 = 1 < 2`), but
  * `not_excludedPP_four_two : ¬ ExcludedPP 4 2` (`⌊4/2⌋ = 2`, `C 2 = 3 ≥ 2`).

  The *same* prime power `q = 2` is excluded in the window `[1,3]` and not in `[1,4]`: the
  rule flips as the scale grows, so it is not a scale-invariant local constraint.
  `ExcludedPP.mono_M` (in `Chain.lean`) records the one-directional dependence
  (`M' ≤ M → ExcludedPP M q → ExcludedPP M' q`) that a truly local rule would not have.

**First mismatch.** The alphabet is not finite and the rule is not scale-invariant: the
exclusion threshold `C(⌊M/q⌋)` grows with the window and the modulus `p` is unbounded.
Concretely, `excludedPP_three_two` together with `not_excludedPP_four_two` exhibit one
prime power whose admissibility changes with the global scale `M` — the first place where a
fixed finite-window rule fails.

## Task 2 — the dichotomy, for the (valid) local subshift

Because only the gap layer is a genuine SFT, the dichotomy is proved for that subshift.

* **(A) No cycle through a hole-state ⇒ boundedly many holes.**
  `Gap2CE.holes_card_le_A : ce.holes.card ≤ ce.A.card` and
  `Gap2CE.two_mul_holes_le : 2 * ce.holes.card ≤ M + 1 - N`. Since `(hole,hole)` is
  forbidden, every window hole `n` forces `n+1 ∈ A` (`forced_right`), so holes inject into
  `A` and occupy at most half of `[N, M]`.

* **(B) A cycle gives a periodic symbolic fake satisfying the local rules.**
  `altWord n = if n % 2 = 0 then inA else hole` is `2`-periodic
  (`altWord_periodic`), satisfies the local rule everywhere
  (`altWord_locallyAdmissible`), and genuinely contains holes (`altWord_has_hole`).

Consequence: the local subshift is **nonempty and has periodic points**. Local rules alone
therefore cannot refute a counterexample — the arithmetic (non-local) layer is essential.
This is the honest content of (B): a follower-graph cycle for the local SFT is only a
symbolic fake, not a genuine reciprocal-sum counterexample.

## Task 3 — the correct replacement

Since the literal SFT schema is not valid, the sound replacement is the
**interval / blocker-pair-chain certificate graph**, already formalized in `Chain.lean`:

* `ChainLink` — one certified blocker pair `(x, q₁, q₂)` plus the top `Mmax` of the
  `M`-range `[x+2, Mmax]` it covers, with `Mmax ≤ ⌊e·x⌋` and `ExcludedPP Mmax qᵢ`.
* `chainFrom` / `BlockerChain` — a list of links whose covered ranges *chain* (overlap) to
  cover an interval `[lo, hi]`.
* `BlockerChain.refutes` — any valid chain certificate refutes every `Gap2CE` with
  `M ∈ [lo, hi]`.

This keeps the local gap constraint (used through `blockerPair_covers_range`/
`excludedPP_blockerPair`) but attaches a *per-interval arithmetic certificate*
(`ExcludedPP`) instead of pretending the arithmetic is a single finite local alphabet. It
is the "blocker-pair-chain certificate graph" option, and it is the honest, sound object.
(The "scale-normalized wheel state" idea would fix a modulus and thereby only capture one
residue slice; `modulus_alphabet_unbounded` shows a single modulus cannot suffice.)

## Task 4 — required output

* **Does Fable's schema match the certified kernel?** Only partially. The gap layer is a
  genuine radius-1 SFT; the arithmetic layer is not representable over a fixed finite
  alphabet with a scale-invariant local rule.
* **First mismatch.** The exclusion rule is not scale-invariant and the alphabet is not
  finite: `excludedPP_three_two` vs `not_excludedPP_four_two` (same `q=2`, different `M`),
  and `modulus_alphabet_unbounded` (unbounded prime modulus).
* **Theorems formalized (in `SFTAudit.lean`).** `Cell`, `LocallyAdmissible`, `Gap2CE.word`,
  `word_eq_hole_iff`, `Gap2CE.word_locallyAdmissible`, `Gap2CE.holes`,
  `Gap2CE.holes_card_le_A`, `Gap2CE.two_mul_holes_le`, `altWord`, `altWord_periodic`,
  `altWord_locallyAdmissible`, `altWord_has_hole`, `modulus_alphabet_unbounded`,
  `excludedPP_three_two`, `not_excludedPP_four_two`. (Replacement graph: `ChainLink`,
  `chainFrom`, `BlockerChain`, `BlockerChain.refutes` in `Chain.lean`.)
* **Build.** Succeeds (`RequestProject.Main` and all modules).
* **Placeholders.** None: no `sorry`, `axiom`, `unsafe`, or `native_decide`; only the
  allowed axioms `propext`, `Classical.choice`, `Quot.sound` are used.
