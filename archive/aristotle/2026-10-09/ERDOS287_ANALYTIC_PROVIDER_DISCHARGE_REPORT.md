# Erdős #287: attempt to discharge the analytic providers

**Verdict: REPAIR / TAIL OPEN.**

Erdős #287 is still open. I did not construct a theorem of type
`Erdos287.CurrentTail.Tail287Statement`, and no conditional theorem is being presented as one.

## What was proved this round

New file: `RequestProject/Erdos287/SourceChain/Physical/TypeII/UremCounterexample.lean`.
It contains no `sorry`, `axiom`, `native_decide`, `unsafe` or `implemented_by`. Every theorem
uses only `propext`, `Classical.choice` and `Quot.sound` (see `RepairAudit.lean`).

### Main result: the remainder provider, as stated, is false

```lean
theorem not_ordinaryBVUremProviderScoped {κ : ℝ} (hκ : 0 < κ) (hκ' : κ < 1 / 100000) :
    ¬ OrdinaryBVUremProviderScoped κ
```

This holds for every κ in the critical regime. It has two corollaries:

- `not_ordinaryBVUremProvider`: the older, broader provider is false too.
- `scopedProviders_inconsistent`: `PascadiCriticalCellProviderScoped κ ∧ OrdinaryBVUremProviderScoped κ` is false.

So the conditional theorem `scalarTypeII_bound_of_scopedProviders` gives no information in the
critical regime, because its hypotheses can never all hold there.

**Two independent defects in the statement**

1. **The distribution hypothesis is empty.** In `OrdinaryBVUremProviderScoped` the caller chooses
   the Siegel–Walfisz parameters `A'` and `B` (they are universally quantified). Taking `B = 0`
   leaves only the modulus `q = 1` to check in `SWSeqMasked α N A' 0 _`, and there the difference
   is exactly `0`. (The Pascadi provider gets this right: there `A'` and `B` are chosen by the
   provider.)
2. **A modulus can share a prime with the affine residue.** Nothing in the statement forces
   `(l, A·B) = 1`. Take `A = 1`, `B = 3`. On odd multiples `v` of 3 we get
   `h_3(v) = I_3(v) − U_3(v) = 1 − 0 = 1`, so nothing cancels.

**The witness.** Choose `f = 2`, `c = 1`, `K = 4`, roughness `ρ = 3κ`, `Aexp = 3`. Then take:

- `X = 2^{6r}`;
- `N = 2^i`, a dyadic block that is rich in primes;
- `M = 2^{6r−i−1}`;
- `α` = the indicator of the primes in `[N, 2N)`;
- `β` = the indicator of `m ≡ 3 (mod 6)` in `[M, 2M)`.

**Lemmas used, all proved:**

- `ellX_three`: `ℓ_X(3) = −1` once `3 < u` and `27 ≤ D_low`.
- `colProd_three_eq_zero` and `sum_coefAtom_three_one`: summed over all atoms, the coefficient at `(l, r) = (3, 1)` is `−Γ`.
- `physUrem_eq_three`: with `K = 4` and `f = 2`, the whole `h_l U_r` part reduces to the single modulus `l = 3`.
- `weight_eq_one` and `inner_sum_eq`: the inner sum equals `π[N,2N) · #{m ∈ [M,2M) : m ≡ 3 (6)}`.
- `two_pow_le_primes`: the elementary Chebyshev bound `2^m ≤ m(π(2^m)+1)`, derived from the central binomial coefficient.
- `exists_prime_block`: a dyadic pigeonhole giving a block `[2^i, 2^{i+1})` with `r ≤ i < 2r` and at least `≈ 2^{2r}/(2r²)` primes.
- `mod6_count_ge`: at least `M/6 − 3` admissible values of `m`.
- `uremCE_final_ineq`: the resulting lower bound `≫ X/log² X` beats `C·W·X/(2 log³ X)` once `r > max(C,0)·W`.

**The actual source avoids defect 2.** `PhysData.prime_dvd_f_of_dvd_AB` shows that for a physical
packet with `j ≠ ℓ`, every prime dividing `A_{jℓ}·|B_{jℓ}|` divides `f_ξ = a_j W q₀`. The
condition `(f, lr) = 1` inside `physCoefAtom` then removes every such modulus.

**What a correct remainder statement would need.** At minimum, the provider must choose `A'` and
`B` itself, and the statement must require every prime of `A·B` to divide `f`. Even with defect 1
fixed, defect 2 alone still makes the statement false. In that case `α` = primes satisfies the real
Siegel–Walfisz theorem, but that step is informal: Siegel–Walfisz is not formalized here. Following
your instruction not to rename gaps as new providers, I have **not** added a repaired provider
definition. Proving a repaired version would still need a Bombieri–Vinogradov theorem for bilinear
forms (multiplicative large sieve plus the SW hypothesis), which is neither in Mathlib nor in this
project.

## Priority 1: `PascadiCriticalCellProviderScoped` is not proved

Its source sum is `(physCell S κ N Γ f c A B K (2^i) (2^{i'}) N M J P χ α β).T`, that is,

  `∑_{l∼L} ∑_{m∼M} β_m ∑_{r∼R} c_{ξ,l,r} ∑_{n∼N} α_n 1_{mn≡c (f)} I_l(mn) h_r(mn)`.

It must be shown to be at most `C·Bα·Bβ·|Γ|·w(J,P)·X / (f log^A X)`, with moduli `lr` up to
`X^{59/100}`, beyond `X^{1/2}`. **This is the first inequality in the critical path with no proof.**

It needs Pascadi's dispersion and spectral estimate, which rests on Deshouillers–Iwaniec bounds
for sums of Kloosterman sums. Neither those bounds nor the spectral theory of automorphic forms
behind them exist in Mathlib or in this project. I did not find any reduction to elementary
facts, and I have not replaced it with a citation. In this regime, refuting the statement the
same way as the remainder provider does not work. There the provider chooses `A'` and `B`, so
`α` must be genuinely equidistributed. The moduli `r` are made of high primes, which eventually
do not divide `A·B`, so `h_r` is centred.

**Hypotheses for the actual source:**

- *Proved earlier:* supports, coefficient bounds, coprimality of the colour factors, the boxed range conditions (`physAtom_provider_contract`, `physCell_contract`) and the FCHS algebra.
- *Not proved:* roughness and masked Siegel–Walfisz for the actual Heath–Brown `α`, which needs the Siegel–Walfisz theorem and so Siegel's theorem; and `f ≤ X^{κ/10⁶}` for the constructed family.

## Priorities 3 and 4, and the final validation

These depend on Priorities 1–2 and were not reached:

- the W4 diagonal, Ramanujan and spectral estimates;
- the Type I, one-large, two-large and boundary contributions;
- partial summation;
- `IsLittleOTarget`;
- `OneSidedFrameworkFor`.

No `example : Erdos287.CurrentTail.Tail287Statement` was compiled.

## Strongest completed theorem and remaining dependencies

**Strongest new result:** `not_ordinaryBVUremProviderScoped` (kernel-checked).

All earlier results are kept and still build, including the FCHS algebra, the parameter margins
and the conditional theorems. The conditional theorem `scalarTypeII_bound_of_scopedProviders` is
now known to give no information in the critical regime.

**Still needed for the tail:**

1. Pascadi's beyond-half estimate for `physCell`.
2. A correctly scoped, provable remainder statement and its BV-type proof.
3. Roughness and masked SW for the actual Heath–Brown sequences.
4. The bound `f ≤ X^{κ/10⁶}` for the constructed family.
5. The W4 / non-critical routing, partial summation and both little-o statements.
6. The seven-block framework.

## Files and build

- **New:** `RequestProject/Erdos287/SourceChain/Physical/TypeII/UremCounterexample.lean`.
- **Edited:** `RequestProject/Erdos287/SourceChain/Physical.lean` (import) and `RequestProject/Erdos287/SourceChain/RepairAudit.lean` (axiom prints).
- **Build:** `lake build RequestProject.Erdos287.SourceChain` succeeds (8149 jobs), and so does `lake build RequestProject.Erdos287.SourceChain.RepairAudit`.
