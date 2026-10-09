# Archive (6) review: elementary re-audit, actual source progress, and the unproved tail boundary

## 0. Disposition and evidence level

**Verdict: FORMAL SOURCE CONSTRUCTION ADVANCED; UNCONDITIONAL TAIL NOT ESTABLISHED BY THIS ARCHIVE.**

This is a review of the supplied `f3680730-21fd-4bc3-b8e9-fac9ae820a7d-aristotle (6).tar.gz`, together with the current conditional manuscript and FCHS-patched actual-atom supplement. It is not a replacement proof of every analytic theorem in the programme.

The archive contains 1,069 Lean files in total and 65 Lean files under `RequestProject/Erdos287/SourceChain/`. Those counts are inventory data, not proof strength. The source sets Lean/mathlib to v4.28.0. The archive reports successful builds; this review did NOT rerun them because Lean/lake is unavailable in the review environment. No source file in the input archive was changed.

The quoted latest response accurately describes a *top-layer re-audit*. It does not claim to prove the tail. More advanced physical-source work is already present elsewhere in the same archive; it must not be discarded or confused with the scope of that last response.

## 1. What the latest top-layer result really supplies

`ERDOS287_TOPLAYER_PACKAGE_REAUDIT.md` explicitly limits itself to `Defs`, `TopLayer`, `Cnum`, `Window`, `Counterexample`, `PrimeFree`, and `Blocker`. It states that no Lean source was modified.

Its algebraic and structural results are useful: top-layer congruences, small-cardinality obstructions, exact reciprocal-subset numerator maxima C(j), prime-power window exclusion, harmonic window constraints, eventual prime-freeness, and the contradiction from two adjacent blocked positions.

Independent exact rational enumeration in the companion checker reproduces

    C(1..9) = 1,3,11,25,137,137,1019,2143,7129

and the witness

    sum_{s in {1,2,3,4,5,7}} 1/s = 1019/420.

This is not an independent Lean rebuild and not a proof of any asymptotic prime supply. In particular, `Gap2CE.excludedPP_blockerPair` assumes the two excluded prime powers and their divisibility into adjacent positions. It does not construct those witnesses for every sufficiently large source.

## 2. Important progress that must be retained

The newer `ERDOS287_PARAMETER_SOURCEFIT_JUNCTION_REPORT.md` and the matching code go beyond the elementary report:

- `Physical/Factorization/ActualParams.lean`: an actual fixed scalar-parameter choice, the small-prime exponent bound, and `atom_factorization_actual` on `CritRegime`/`CritCell`.
- `Physical/TypeII/ProviderDictionary.lean`: exact `physCoefAtom_eq_dict`, one-boundedness, disjoint/coprime supports, and all three boxed kernel ranges, with epsilon = kappa/2000.
- `Physical/TypeII/SourceComposed.lean`: `scalarTypeII_eq_cells`, `packet_typeII_eq_cells`, and `physCell_contract`. The source is actually constructed. The designated pair is already part of the packet index; it must not be counted a second time.
- `SourceChain/W4Route.lean`: finite source-to-positive-square Cauchy, a generic fixed-A positive domination, the corrected FCHS expression, square-root exponent propagation, and packet arithmetic.
- `Physical/Tail.lean`: the exact physical remainder is connected to the existing conditional tail boundary.

Thus the earlier description “the physical source has not been defined at all” is stale. The remaining difficulty is instantiating and proving the analytic estimates and main-term framework for that actual source.

## 3. The canonical conclusion is already defined, but not proved without hypotheses

`CurrentTail/TailBoundary.lean:33-34` defines

    def Tail287Statement : Prop :=
      ∃ M0 : ℕ, ∀ A : Finset ℕ, ∀ hA : Erdos287Counterexample A,
        A.max' hA.nonempty < M0

This is the requested pre-effectivity target. No numerical M0 is required.

`Physical/Tail.lean:121-125` proves only

    Tail287_of_physical
      (Fw : OneSidedFrameworkFor F.R F.target)
      (hgood : eventually physical/sieve good)
      (hrel : IsLittleOTarget F.Rrel F.target)
      (hbase : IsLittleOTarget F.Rbase F.target) : Tail287Statement

All four inputs remain arguments. Moreover, F itself is an arbitrary `PhysicalFamily`; a final application needs one actually constructed family whose target is the intended normalization and whose coefficients, presieve and prime counts are the literal source.

The `OneSidedFrameworkFor` argument is substantial. It includes a scale selection, actual finite weights, a seven-block moment dictionary and simultaneous contact-window control for every sufficiently large exact word. Proving Cauchy's numerical consumer is not the same as constructing this framework.

The exact counterexample predicate in `ProblemStatement.lean` requires every denominator to exceed 1. The historical `Gap2CE` only requires positivity and admits `{1}`. The final theorem must use `Tail287Statement`/`Erdos287Counterexample`, not an unconditional nonexistence claim about the broader type.

## 4. Definitions of estimates are not estimates

`Physical/TypeII/RemainingProviders.lean` states at its beginning that its provider declarations are unproved analytic inputs. It defines:

- `PascadiCriticalCellProvider kappa`;
- `OrdinaryBVUremProvider kappa`;
- `SWSeq`.

`scalarTypeII_bound_of_providers` is proved *from arguments* of the first two types. The source identities preceding it are real theorems; the analytic providers are still assumptions.

Similarly, `W4Route.lean:160-175` defines `W4DiagEstimate`, `W4RamEstimate`, and `W4SpecEstimate`, and proves `W4_bound_of_pieces` from those three estimates plus a structural split. The latter theorem adds three already-assumed inequalities; it is not a proof of the spectral large sieve.

A static symbol search in the current `SourceChain/Physical` subtree found no direct invocation of `source_to_W4`, `CleanAtom`, `AstraAtomBound`, `W4SpecEstimate` or `W4_bound_of_pieces`. This limited search is not a semantic impossibility result; it is consistent with the archive's explicit provider boundary and shows why a generic W4 lemma must not be presented as an already-instantiated physical-source theorem.

Clean `#print axioms` output does not remove theorem binders. For example, `theorem conditional_example (P : Prop) (h : P) : P := h` introduces no new global axiom, yet it proves P only from h. Inspect full types as well as axiom dependencies. [L1,L2]

## 5. Interfaces to repair before trying to discharge the providers

### 5.1 Quantifier order and actual affine data

The current `PascadiCriticalCellProvider` chooses C and X0 before quantifying over every A, Bres and scalar parameter set. It also has no A>0, Bres != 0, or coprimality hypothesis on these affine coefficients. The supplied actual-atom paper fixes admissible affine A,B first and permits its constants to depend on them.

Therefore the supplied theorem cannot simply instantiate this provider as written. This review does not assert that every possible strengthened provider is false. It identifies a theorem-scope mismatch.

Repair by fixing the finite actual affine tuple, smooth profiles and scalar construction before choosing constants; prove a source-specific bound with the actual admissibility assumptions. Then take maxima over the finite pair/box family if justified. Do not prove a broader statement accidentally demanded by an abstraction, and do not add the needed source-specific estimate as an unproved final assumption.

### 5.2 The allowed base exponent is incompatible with the imported bound

The proved `physAtom_provider_contract` exports epsilon = kappa/2000. The provider currently allows f <= X^(kappa/1000), whereas the actual-atom supplement assumes sigma <= epsilon/100. Thus the formal base cap is 200 times the supplied sufficient cap.

Even the retained final packet margin becomes negative if one simply substitutes those displayed constants:

    epsilon/2 - (391/256)(kappa/1000) = -327 kappa / 256000.

One compatible conservative repair is

    epsilon = kappa/2000,
    sigma = kappa/1000000,
    delta_spectator = sigma/4.

Then sigma <= epsilon/100 and

    epsilon/2 - (391/256)sigma = 63609 kappa / 256000000 > 0.

The paired spectator lcm exponent 2 delta_spectator = sigma/2 leaves room for fixed slopes and the growing presieve. Its actual bound must still be proved. It is also permissible to derive and use a genuinely stronger exported epsilon, with proof. Merely quoting the old scalar margin is not sufficient.

Do not confuse the source cutoff parameter named K in `physCell` with the number of Maynard forms; the code uses K in several different roles.

### 5.3 Roughness and SW must belong to the actual source

The current critical provider assumes only dyadic support and `SWSeq`; it does not require the roughness hypotheses used by the published Type-II reduction or the cleaned atom. `SWSeq` also lacks the additional coprimality-mask parameter present in Maynard's stated SW condition. [M]

The current `OrdinaryBVUremProvider` quantifies over arbitrary bounded dyadic alpha,beta without ANY SW/distribution premise. Being below the one-half modulus level does not itself give an equidistribution theorem for arbitrary coefficients.

This is not presented as a verified counterexample to the entire existing `physUrem` proposition. The repair must either derive an estimate for the actual Heath--Brown sequences, including the precise relative-centering and coprimality condition used in its proof, or reformulate a sufficient provider with those hypotheses and then prove they hold. The last theorem must not retain a newly named unproved provider.

### 5.4 Product scale and norms

The formal provider currently assumes only N*M <= S.X. The actual-atom proof uses x=MN (up to explicit fixed comparability). Either restore that relation on the actual critical cells or separately prove the small-product ranges. Do not identify different scale variables without an inequality ledger.

A packetwise inverse-log estimate cannot be multiplied by a polynomial number of packets. Retain the relative-BDH density ordering; only fixed-power errors may use the crude packet count. Main-term normalization must be the actual positive N_X I, not a freely inflated `target` chosen to trivialize little-o.

## 6. The FCHS correction is in the code, but needs downstream propagation

`W4Route.lean:135-168` correctly defines the selected corrected expression with FCHS. The old expression is retained for regression only.

The published supplement now displays FCHS in (6.5), but its immediately following g-scaling prose and list of four monomials are unchanged. A display-only patch is not itself a proof that the old range calculation survives.

The companion `FCHS_AND_PARAMETER_REPAIR.md` supplies two elementary repairs:

1. If 0<=F<=B0 and 0<=H<=S, then

       F C H S <= B0 C S^2,

   hence the corrected square-root term is bounded by

       sqrt(F C^2 + 2 B0 C S^2).

   Use actual length envelopes to establish F <= C_* B0 with a fixed constant if the literal dyadic variables do not satisfy F <= B0 pointwise. This changes constants, not exponents.

2. With F=F0/g, C=C0/g,

       sqrt(F)*sqrt(F C^2+B0 C S^2+F C H S)
       = sqrt(F0)/g * sqrt(F0 C0^2/g^2+B0 C0 S^2+F0 C0 H S/g).

   Thus the claimed 1/g domination survives, with the formerly omitted last term recorded explicitly.

Primary-source caution: Pascadi's displayed proof has an intermediate FCHS/B term and a later simplified FHS term after prefactor cancellation. Do not describe those different expressions as the same formula. Retaining the archive's conservative enlarged FCHS expression is legitimate in ranges where the domination is justified, but it is not a verbatim transcription of every displayed stage. [P]

A documentation-only direction error also appears at `W4Route.lean:145-146`: the theorem below proves `old <= new`. A valid bound by the smaller old RHS would imply a weaker bound by the new RHS (under its positivity assumptions), not the reverse. Correct the comment, not the already-correct algebraic theorem.

None of these algebraic repairs proves the actual W4 spectral estimate.

## 7. What the next run must deliver

The correct unit of work is not another top-layer audit. It is:

    actual PhysicalFamily
      + proven correct provider instances
      + actual HB/partial-summation / noncritical / centering assembly
      + proven one-sided seven-block framework
      -> a closed term of Tail287Statement.

The next prompt fixes that objective, preserves already-constructed source data, and prevents escaping into a new generic interface.

For formal success, the final exported theorem must have no unresolved analytic or framework parameters and must be consumable by an independent file containing an `example : Tail287Statement := ...` outside sections with assumptions. A citation in a comment is not a Lean proof term. Missing deep formal results remain explicit provider dependencies even when the corresponding paper theorem is accepted informally.

For paper-level reconciliation, every remaining provider must have a complete stated written theorem, exact hypothesis match, and proof/citation chain. Standard library formalization incompleteness and a missing mathematical argument are distinct statuses. Neither an earlier model PASS nor this source review settles the latter.

## 8. Publication verdict

Keep the present main manuscript conditional until the actual analytic estimate AND its source/main-term integration have been verified at the claimed level. The archive does not justify promoting Hypothesis 9.1 to an unconditional theorem. A complete conditional Lean dependency certificate is useful, but is not an unconditional formal tail proof.

Effectivity/finite splice is separate. No additional finite endpoint is inferred here; the elementary prime-free threshold and arithmetic height lemmas do not prove all remaining finite cases.

## References

[L1] Lean Language Reference, Axioms, especially displaying axiom dependencies:
https://lean-lang.org/doc/reference/latest/Axioms/

[L2] Lean community, Did you prove it?:
https://leanprover-community.github.io/did_you_prove_it.html

[P] A. Pascadi, *On the exponents of distribution of primes and smooth numbers*, v2:
https://arxiv.org/html/2505.00653v2

[M] J. Maynard, *Primes in arithmetic progressions to large moduli II: Well-factorable estimates*, v1, Definition 3 and Proposition 6.8:
https://arxiv.org/html/2006.07088v1

Archive source references and exact line-numbered excerpts are in `SOURCE_EVIDENCE.md`. All source files quoted there are preserved unchanged in `inputs/archive_evidence/`.
