# Summary of changes for run 5d86c016-42d5-4c09-8677-d71014106c45
**Verdict: §§6–7 of the V100R4S proof (exponent algebra only) are now checked in Lean, but the result is conditional. Erdős #287 is still open, and I did not prove `Tail287Statement`.** I worked from the new attachment (`05_ERDOS287_PROOFS_AUDIT_PROMPT_REVISED.md`): its V100R4S landing guide and the author proof `PROOFS/actual_atom_proof_FCHS.md`. Your later files (`FCHSPropagation.lean`, `ScopedProviders.lean`, `UremFamily*.lean`) were already in the project. I added to them and changed nothing that was there.

**Checks:** `lake build RequestProject.Erdos287.SourceChain RequestProject.Erdos287.SourceChain.RepairAudit` succeeds. The three new files contain no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` or `implemented_by`, and every new theorem uses only `propext`, `Classical.choice` and `Quot.sound`.

**New files** (all in `RequestProject/Erdos287/SourceChain/`):
- **`W4RatioLedger.lean`** defines `V100Range`, the range conditions (1.1)–(1.3) plus `Q ≤ N` and `N, Q, R, S ≥ 1`. It proves the ratio bounds with no analytic assumption:
  - `diag_ratio` for (6.3);
  - `ram_ratio` for §6.2, with saving \(x^{-64\epsilon/3}\);
  - `ratio_6_6a`, `ratio_6_6b`, `ratio_6_6c`, `ratio_6_6d`, with exactly the savings claimed in (6.7);
  - `H0_div_S_ratio`.
  
  **No counterexample:** every claimed saving holds as stated.
- **`W4SourceBound.lean`** puts in the actual source sizes (\(F\le cN/Q\), \(C\le cNRS\), \(B_0\le cNR\), \(0<H\le\Lambda H_0\)). It keeps the corrected `FCHS` term and does not assume \(H\le S\). `spec_mono_1`…`spec_mono_6` bound the six terms of the expanded spectral estimate. Four of them are (6.6a–d); the other two come from `FCHS` and do not change the exponent. Also proved: `bracket_H_le`, `spec_source_bound`, `diag_source_bound`, `ram_source_bound`. **`W4_uniform_bound_6eps`** gives the (6.8)-shape bound \(\mathscr W_4\le 8c^3\Lambda^2T^{7/64}N^2R^2S^3x^{-6\epsilon}\), conditional on the three narrow W₄ estimates.
- **`V100Kernel71.lean`** proves:
  - `kernel_7_1`: (4.9) plus (6.8) give the \(f^{199/128}\) budget;
  - `kernel_1_8` and `kernel_1_9`;
  - **`kernel_1_9_of_narrow`**: the full chain from (4.9) and the narrow W₄ estimates to the (1.9)-shape bound \(f^{263/128}N^2/(Qx^{\epsilon})\), with an explicit constant.

`SourceChain.lean` and `RepairAudit.lean` now import these files, and `RepairAudit.lean` prints their axioms.

**First unproved analytic inequality:** V100R4S (6.5), the narrow spectral estimate `W4SpecEstimate` with the `FCHS` term (Pascadi Lemma 4.1 with Propositions 3.4/3.8). The diagonal estimate (6.2), the Ramanujan estimate (6.4) and the source inequality (4.9) are also still hypotheses. The degenerate cells of §8 are not covered.

The equation-by-equation status table is in `ERDOS287_V100R4S_W4_LEDGER_REPORT.md`. The Properties table has four new rows: `V100Range`, and three proved rows for the ratio bounds, the conditional (6.8) bound and the conditional (1.9) chain. All work is committed.

# Summary of changes for run 3751f43a-d32d-4146-ae06-40fc950cd74c
**Verdict: the Urem branch is now proved in Lean, but only conditionally.** It depends on two published analytic results, stated as explicit hypotheses rather than axioms: Maynard I, Lemma 13.8, and a Siegel–Walfisz-type condition (6.1) for the two base rough sequences. Neither is formalized here. The bound also has not yet been checked against the actual moduli range (see "Still open"). Erdős #287 is still open, and I did not prove or claim `Tail287Statement`. All earlier lemmas are unchanged and none were renamed.

**Checks:** `lake build RequestProject.Erdos287.SourceChain RequestProject.Erdos287.SourceChain.RepairAudit` succeeds. The five new files contain no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` or `implemented_by`. Every new theorem uses only `propext`, `Classical.choice` and `Quot.sound`.

**New files**, all in `RequestProject/Erdos287/SourceChain/Physical/TypeII/`:

- **`UremFamilyMoments.lean`** (no analytic hypotheses):
  - `sum_tau_pow_div_le`: \(\sum_{n\le x}\tau(n)^k/n\le(1+\log x)^{2^k}\).
  - `nat_le_card_divisors_mul_totient`: \(n\le\tau(n)\varphi(n)\).
  - `sum_tau_pow_div_totient_le`, the reciprocal-divisor moment: \(\sum_{r<K}\tau(r)^B/\varphi(r)\le(1+\log K)^{2^{B+1}}\).
  - `sum_tau_pow_le`: \(\sum_{n\le x}\tau(n)^k\le x(1+\log x)^{2^k}\).
- **`UremFamilySW.lean`**: defines `IntervalSWAt`, which is condition (6.1) on every initial segment \((N,t]\).
  - Proved: truncation (`intervalSW_trunc`), partial summation (`abel_bound`) and the log normalisation (`swCondition_log_of_intervalSW`, constants \(2c_A\)).
  - `alphaSeq_swCondition`: (6.1) holds for every actual `alphaSeq` component (rough log normalised by \(1+\log 2N\), rough constant, rough truncated μ, and the unit). It is derived from `IntervalSWAt` for \(1_{P^-(n)\ge z_0}\) and \(\mu(n)1_{P^-(n)\ge z_0}\), with constants uniform in \(z,j,e,c\).
  - `alphaSeq_abs_le_tau`: the divisor-power bound \(|\alpha/\text{norm}|\le\tau(n)^{B_0}\).
  - The extra \((n,r)=1\) mask costs \(\tau(r)^{B_0}\). That loss is handled by the existing `swCondition_masked` and paid for by the reciprocal-divisor moment.
- **`UremFamilyAggregate.lean`**: `packet_density_le`, `atom_total_le`, and `actual_family_urem_explicit`, the family bound with every sum evaluated.
- **`UremFamilyCell.lean`**:
  - `physUrem_scale_left` and `physUrem_sum_right`: `physUrem` is linear in each coefficient.
  - `betaSeq_lt` and `betaSeq_eq_sum_dy`: support and exact dyadic splitting of the actual β.
  - `betaSeq_dy_sq_le`, the actual β second moment: \(\sum\beta^2\le(1+\log 2M)^{10}\cdot 2M(1+\log 2M)^{256}\).
  - `cell_urem_bound`: the bound for one cell.
- **`UremFamilyFinal.lean`**:
  - **`cell_urem_polylog`**: for every \(A>0\), \(\sum_\xi|\mathrm{physUrem}_\xi(\texttt{alphaSeq},\texttt{betaSeq})|\le C_{\rm fin}X/(\log X)^A\). It assumes only `MaynardLemma13_8`, `IntervalSWAt` and parameter-range conditions, with no provider hypothesis.
  - **`cells_urem_polylog`** with `card_cellBox` (\(18E_0^6\) cells): summing over all cells gives \(O(X/(\log X)^{A-6})\).

`SourceChain/Physical.lean` and `SourceChain/RepairAudit.lean` were updated to import the new files and print their axioms.

**Paper level versus Lean level:** Lemma 13.8 is a published theorem that has not been formalized. I checked the match to it: divisor-power coefficients, uniform SW constants, complete modulus \(q=fl<N/(\log N)^C\), and the packet and coefficient multiplicities. The `IntervalSWAt` input comes on paper from the Siegel–Walfisz theorem: combined with the fundamental lemma or Rankin's trick when \(z_0\le\exp(c\sqrt{\log N})\), or with convolution closure when \(z_0=N^\delta\). Siegel's theorem is not in Mathlib.

**Still open:**
- **Moduli range not checked:** the bound needs moduli \(fl\le\min(M,N/(\log N)^C)\) (hypothesis `F·2^{n₀} ≤ 2^E`). I have not checked that the actual routing satisfies this. If it does not, the bound does not apply.
- The cell roughness \(z_0\) is never fixed anywhere in the project.
- I did not start the critical Pascadi/W4 estimate, which is the next item. The noncritical routing, the base remainder and the seven-block framework also remain open.

Full theorem signatures, the residual-hypothesis table and source citations are in `ERDOS287_UREM_BRANCH_COMPLETION_REPORT.md`. The Properties table has seven new rows.

# Summary of changes for run f5352bd5-0fe1-4940-97f3-2608f434de55
**Verdict: UREM PAPER REPAIRED; PUBLISHED ANALYTIC FORMALIZATION REMAINS.** Erdős #287 is still open, and I did not prove `Tail287Statement`, either on paper or in Lean. I added a family-averaged replacement for the false packetwise remainder provider. It is a proved theorem, not a new provider assumption. `not_ordinaryBVUremProviderScoped` and all earlier results are unchanged.

**Proved without any analytic input** (new files `UremFamily*.lean` in `SourceChain/Physical/TypeII/`):
- **Finite steps:** the CRT projection identity (3.2) and the energy contraction (3.3), which loses no factor of \(\phi(f)\) or \(\phi(l)\). The exact residue rearrangement (5.1) is proved for the actual inner sum of `physUrem`; it needs only \((c,f)=1\) and \((A|B|,l)=1\), and never inverts \(A\) mod \(f\). Also proved: residue occupancy (5.2), the per-packet Cauchy step (5.3) using the actual \(\beta\) \(L^2\) norm, the packet Cauchy step (5.4), and the grouping of moduli \(q=fl\) (4.2).
- `physUrem_eq_uremBlocks`: `physUrem` equals an exact sum of family blocks built from the actual atom coefficients. \(\Gamma\) appears only once, inside the coefficient.
- `physical_family_urem_le`: for one group sharing a common \(\alpha\), \(\sum_\xi|\mathrm{physUrem}_\xi|\) is bounded by atom weights × packet density × the complete-modulus BDH energies of the masked sequences \(\alpha^{(r)}\).
- `packet_multiplicity`: for the actual packets, \(\sum_{f_\xi=f}|\Gamma_\xi|\le (VB_f^k)^2k^2\tau(f)^{2k}\), keeping every spectator multiplicity.
- `group_typeII_sub_cells_le`: any bound on that family sum also bounds the gap between the group's scalar Type-II source and its cell sum, via `scalarTypeII_eq_cells`.

**Analytic layer:** I copied Maynard I's Siegel–Walfisz condition (6.1) and Lemma 13.8 from the arXiv text and stated them as `SWCondition` and `MaynardLemma13_8`. These are definitions used only as hypotheses, not axioms. I proved that masking by \((n,r)=1\) keeps a sequence in the SW class. From Lemma 13.8 I then derived the masked BDH energy bound and `actual_family_urem_maynard`, the family bound for the actual packets. That theorem proves \((c_\xi,f_\xi)=1\), the affine-prime condition, \(f_\xi>0\) and the multiplicity bound rather than assuming them. It takes no provider argument.

**First remaining obligation:** the Siegel–Walfisz condition (6.1) and divisor bound for the actual `alphaSeq` (rough constant, log and truncated μ). The paper argument relies on the fundamental lemma of the sieve and on Siegel–Walfisz for μ, and is not formalized. Lemma 13.8 itself is a published theorem that has not been formalized; that is a formalization gap, not a missing proof.

Turning the explicit bound into \(CX/(\log X)^{A}\) also needs some elementary estimates I did not formalize: a divisor moment bound giving \(\sum\beta^2\ll M(\log X)^{C}\), the divisor sum \(\sum_r\tau(r)^{B_0}/\phi(r)\ll(\log X)^{C}\), and \(MN\asymp X\).

The other Tail287 obligations are untouched and unproved: the critical Pascadi/spectral estimate, the W4 estimates, the noncritical routing and its error terms, the base-only remainder and main-term normalization, and the seven-block framework.

**Files and checks:** I added the eight `UremFamily*.lean` files, updated the imports in `SourceChain/Physical.lean`, and added `#print axioms` lines to `SourceChain/RepairAudit.lean`. The write-up is `ERDOS287_UREM_FAMILY_FORMAL_REPORT.md`. `lake build RequestProject.Erdos287.SourceChain RequestProject.Erdos287.SourceChain.RepairAudit` succeeds. The new files contain no `sorry`, `axiom`, `native_decide`, `unsafe` or `implemented_by`, and every new theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. The Properties table has four new rows: the unconditional family bound, the Maynard statement (a definition), the Maynard-conditional actual-packet bound, and the multiplicity bound.

# Summary of changes for run f73700d3-0610-4b4c-b56e-8433de9fa67f
I read "fix it" as the repair suggested at the end of the last run: restate the remainder provider so the known counterexample no longer applies. That is done. Erdős #287 is still open, and the repaired providers are new statements that I have **not** proved.

**The repair:** a new file, `RequestProject/Erdos287/SourceChain/Physical/TypeII/RepairedProviders.lean`, fixes the two defects behind `not_ordinaryBVUremProviderScoped`:
1. The **provider**, not the caller, now chooses the Siegel–Walfisz parameters `A'` and `B`. A caller can no longer pick `B = 0` to make the distribution hypothesis empty.
2. A new hypothesis, `AffinePrimesDivideBase A Bres f`, requires every prime dividing `A·|B|` to also divide `f`.

These fixes give `OrdinaryBVUremProviderRepaired`, plus `PascadiCriticalCellProviderRepaired`, which adds fix 2 to the critical-cell provider. Both are definitions used only as explicit assumptions; neither is an axiom or proved.

**Proved in Lean:**
- `uremCE_data_not_admissible`: the counterexample's data (\(A=1, B=3, f=2\)) break the new hypothesis, so that refutation no longer applies.
- `physData_affinePrimesDivideBase`: the actual physical packets (with \(j\ne\ell\)) satisfy the new hypothesis.
- `pascadi_repaired_of_scoped` and `bvUrem_repaired_of_scoped`: each repaired provider follows from the old scoped one, so the repaired statements are weaker.
- `scalarTypeII_bound_of_repairedProviders`: the scalar Type-II bound follows from the two repaired providers. It is conditional on them. Since each provider picks its own Siegel–Walfisz parameters, the bound assumes both conditions. Its assumptions are no longer refuted by the known counterexample, but whether they hold is still open.

**Not done:** proving the repaired providers. That needs a Bombieri–Vinogradov-type or beyond-half estimate for bilinear forms, which isn't formalized here. I also haven't ruled out other counterexamples to the repaired statements.

**Other files changed:** I added an import to `SourceChain/Physical.lean`, and an import plus `#print axioms` checks to `SourceChain/RepairAudit.lean`.

**Checks:** `lake build RequestProject.Erdos287.SourceChain RequestProject.Erdos287.SourceChain.RepairAudit` succeeds. The new file has no `sorry`, `axiom`, `native_decide`, `unsafe` or `implemented_by`. The new theorems use only `propext`, `Classical.choice` and `Quot.sound`.

I added two rows to the Properties table: the repaired provider (a definition) and the conditional bound (proved, as a conditional result). Everything is committed.

# Summary of changes for run e3182376-a8a2-408e-b681-ff8ae39c228d
**Verdict: REPAIR / TAIL OPEN.** Erdős #287 is still open. I did not prove `Tail287Statement` and did not compile the `example : Erdos287.CurrentTail.Tail287Statement` you asked for. The main new result is that the remainder provider, as currently stated, is false, and Lean checks that.

**The remainder provider is false (Priority 2).** In the new file `RequestProject/Erdos287/SourceChain/Physical/TypeII/UremCounterexample.lean`:
- `not_ordinaryBVUremProviderScoped` proves `¬ OrdinaryBVUremProviderScoped κ` for every \(0<\kappa<10^{-5}\), which is the whole critical regime.
- Two corollaries follow. `not_ordinaryBVUremProvider` shows the older provider is false too. `scopedProviders_inconsistent` shows the two scoped providers can't both hold, so `scalarTypeII_bound_of_scopedProviders` says nothing in that regime.

The statement has two independent defects:
1. **The distribution hypothesis is empty.** The caller picks the Siegel–Walfisz parameters. With \(B=0\), only \(q=1\) is tested, where the difference is identically 0.
2. **A modulus can share a prime with the affine residue.** Nothing requires \((l,AB)=1\). With \(A=1, B=3\), on odd multiples of 3 the term \(h_3=I_3-U_3\) equals 1, so nothing cancels.

The witness takes \(X=2^{6r}\), \(f=2\), \(K=4\), primes in a dyadic block \([N,2N)\) that has many primes, and \(m\equiv3\pmod 6\) in \([M,2M)\). The remainder is then exactly \(-\pi[N,2N)\cdot\#\{m\}\), which is of order \(X/\log^2X\) and beats the claimed \(X/\log^3X\). Every step is proved in Lean:
- `ellX_three`: \(\ell_X(3)=-1\).
- `physUrem_eq_three` and `inner_sum_eq`: the remainder reduces to that single explicit sum.
- An elementary Chebyshev bound and a dyadic pigeonhole, giving a block with enough primes.
- A final real inequality comparing the two sizes.

`PhysData.prime_dvd_f_of_dvd_AB` shows the actual physical packets avoid defect 2: every prime dividing \(A\cdot|B|\) also divides \(f\), so those moduli drop out.

A corrected statement would have to let the provider choose the SW parameters and require every prime of \(A\cdot B\) to divide \(f\). Defect 2 on its own still breaks the version with only the quantifiers fixed. That last step is informal, because the Siegel–Walfisz theorem isn't formalized here. Following your instruction, I did not add a repaired provider. Proving one would also need a Bombieri–Vinogradov theorem for bilinear forms, which neither Mathlib nor this project has.

**The critical-cell provider is not proved (Priority 1).** The first unsupported inequality is the bound on `(physCell …).T`: the sum over \(l, m, r, n\) of \(\beta_m\, c_{l,r}\, \alpha_n\, 1_{mn\equiv c\,(f)}\, I_l(mn)\, h_r(mn)\) must be at most \(C B_\alpha B_\beta|\Gamma| w\, X/(f\log^A X)\), with moduli up to \(X^{59/100}\). That needs Pascadi's estimate, which rests on Deshouillers–Iwaniec bounds for Kloosterman sums; neither is formalized anywhere available here. Also unproved for the actual source:
- roughness and masked Siegel–Walfisz for the real Heath–Brown sequences (this needs Siegel–Walfisz);
- \(f\le X^{\kappa/10^6}\) for the constructed family.

Priorities 3 and 4 depend on these and were not reached. That covers the W4 estimates, non-critical routing, partial summation, both little-o bounds and the seven-block framework.

**Files:** one new file, `UremCounterexample.lean`. I added an import to `SourceChain/Physical.lean` and axiom checks to `SourceChain/RepairAudit.lean`. The write-up is `ERDOS287_ANALYTIC_PROVIDER_DISCHARGE_REPORT.md`.

**Checks:** `lake build RequestProject.Erdos287.SourceChain RequestProject.Erdos287.SourceChain.RepairAudit` succeeds. The new file contains no `sorry`, `axiom`, `native_decide`, `unsafe` or `implemented_by`, and every new theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. All earlier results still build. In the Properties table, the remainder-provider claim is marked negated, and the conditional Type-II row now notes that its hypotheses are inconsistent. Everything is committed.

## Suggested follow-up

One thing in the statements you supplied: `OrdinaryBVUremProviderScoped` lets the caller choose the Siegel–Walfisz parameters, and it does not require the primes of `A·B` to divide `f`. Either defect alone breaks the statement, and Lean now proves it false. If useful, I can draft a corrected statement: the provider chooses the SW parameters, and every prime of `A·B` must divide `f`, which the actual packets already satisfy. I would mark it explicitly as unproved.

# Summary of changes for run d2976fb7-3e7f-48c4-b38c-66614410f85c
**Short answer: the new notes help, but only partly.** `FCHS_AND_PARAMETER_REPAIR.md` and `AUDIT_REPORT.md` settled the algebra and parameter objections they raise, and I have now proved those in Lean. They do not supply any of the missing analytic estimates. Erdős #287 is still open, and `Tail287Statement` is not proved. **Verdict: REPAIR / TAIL OPEN.**

**Now proved in Lean**

*The corrected FCHS term* (`RequestProject/Erdos287/SourceChain/FCHSPropagation.lean`):
- **Bounding the extra term:** if \(F\le cB_0\) and \(H\le dS\), then \(FCHS\le cd\,B_0CS^2\). This is `FCHS_le_B0CS2` and `FCHS_le_const_B0CS2`. Consequences are `pascadiInner_le_two`, `pascadiInner_le_const` and `sqrt_pascadiInner_le`.
- **Scaling by g:** `pascadi_g_scaling` is the exact identity for \(F=F_0/g\), \(C=C_0/g\), keeping the last term \(F_0C_0HS/g\). `pascadi_g_scaling_le` gives the \(1/g\) bound for \(g\ge1\).
- **Pascadi's intermediate step:** `pascadi_normalized_identity` shows that the intermediate \(FCHS/B_0\) expression simplifies to a final term \(FHS\), not \(FCHS\). So the paper's two stages use different normalizations. `regr_normalizations_differ` checks that the two expressions really differ.

*Parameters and provider scope* (`RequestProject/Erdos287/SourceChain/Physical/TypeII/ScopedProviders.lean`):
- **Exponent margins:** with \(\varepsilon=\kappa/2000\) and \(\sigma=\kappa/10^6\), the margin is \(\varepsilon/2-\tfrac{391}{256}\sigma=\tfrac{63609}{256000000}\kappa>0\). With the old cap \(\kappa/1000\) it is \(-327\kappa/256000<0\). Also proved: \(\sigma\le\varepsilon/100\) and \(2\delta<\sigma\).
- **Repaired provider statements:** `PascadiCriticalCellProviderScoped` and `OrdinaryBVUremProviderScoped` are still **unproved assumptions**. Each fixes the affine data first (\(A>0\), \(B\ne0\), \(\gcd(A,|B|)=1\)) and a roughness exponent \(\rho>0\), and only then chooses the constants. Each also requires:
  - \(f\le X^{\kappa/10^6}\);
  - \(X\le 4NM\);
  - rough support of α;
  - a Siegel–Walfisz condition with a coprimality mask (`SWSeqMasked`).
  The second provider now has the distribution hypothesis it lacked before.
- **Nothing lost:** `pascadi_scoped_of_old` and `bvUrem_scoped_of_old` show each old provider implies its scoped version, so the new assumptions are weaker.
- **Conditional bound:** `scalarTypeII_bound_of_scopedProviders` derives the scalar Type-II bound from the two scoped providers. It still depends on them as hypotheses.

*Comment fix:* the docstring of `pascadiInner_ge_old` in `W4Route.lean` had the direction backwards. It now says old ≤ new, so a bound with the old right-hand side implies one with the new right-hand side, and not the converse.

**Still open, and not addressed by the notes**
1. Proofs of the two scoped providers: the beyond-half critical-cell estimate, and the BV/BDH-type estimate for the remainder term. The beyond-half estimate is the first step with no proof.
2. Proofs that the actual Heath–Brown sequences satisfy the roughness and masked Siegel–Walfisz conditions. The published roughness threshold also needs confirming; here it is an arbitrary fixed \(\rho>0\).
3. A proof that the constructed base satisfies \(f\le X^{\kappa/10^6}\). The ledger only shows this cap is consistent with the other parameters.
4. The diagonal, Ramanujan and spectral W4 estimates for the actual source, and applying `source_to_W4` to it.
5. Non-critical routing, partial summation, and the little-o bounds for a concrete physical family.
6. Constructing the seven-block framework.

**Checks:**
- `lake build RequestProject.Erdos287.SourceChain` succeeds (8148 jobs).
- `RepairAudit.lean` shows every new theorem uses only `propext`, `Classical.choice` and `Quot.sound`.
- The new files contain no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` or `implemented_by`.

**Files:** three new files, `FCHSPropagation.lean`, `Physical/TypeII/ScopedProviders.lean` and `RepairAudit.lean`. Edits are the `W4Route.lean` docstring and imports in `SourceChain.lean` and `SourceChain/Physical.lean`. The full write-up is in `ERDOS287_FCHS_AND_SCOPE_REPAIR_INTEGRATION.md`. Everything is committed.

# Summary of changes for run 02f66efc-7d08-4009-9a94-9bfabc99d909
You're welcome. I took your message as a go-ahead to re-audit the elementary structural package for Erdős #287, the top layer and prime-power exclusion. The project already contained it. Erdős #287 itself remains open, and nothing here claims to solve it.

**Files changed:** no Lean source was changed. I added one report, `ERDOS287_TOPLAYER_PACKAGE_REAUDIT.md`, and committed it.

**Build:** the seven package modules in `RequestProject/Erdos287/` (`Defs`, `TopLayer`, `Cnum`, `Window`, `Counterexample`, `PrimeFree`, `Blocker`) build successfully. The only warning is an unused hypothesis, explained below.

**Placeholders:** these files contain no `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `native_decide` or `bv_decide`. Every theorem below depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`. `C_values` uses no axioms at all.

**Theorems proved, by item:**
1. `Erdos287.topLayer_congruence`.
2. `topLayer_card_ne_one`, `topLayer_two_obstruction` and `topLayer_three_obstruction`.
3. `C` is computed exactly over the subsets of \(\{1,\dots,j\}\) and linked to the reduced numerator.
   - `C_values` gives \(C(1..8)=(1,3,11,25,137,137,1019,2143)\), checked by plain `decide`.
   - `C_seven_witness` shows \(S=\{1,2,3,4,5,7\}\) attains \(C(7)=1019\), since \(\sum_{s\in S}1/s = 1019/420\).
   - `C_spec` proves `C j` really is the largest numerator, and `C_mono` proves `C` is monotone.
4. `primePower_window_exclusion`.
5. `Gap2CE.holes_isolated`, `N_mem`, `M_mem`, `exp_lower` \((e(N-1)<M)\), `exp_upper` \((M\le e^2(N+1))\), and `N_gt_M_div_eight`, which gives \(M<8N\) when \(M\ge97\).
6. `Gap2CE.primeFree`: for \(M\ge 8152\), no denominator is prime.
7. `Gap2CE.blockerPair_contradiction`, plus `Gap2CE.excludedPP_blockerPair`, which covers the case where both holes come from prime powers excluded by item 4.

**False statements:** none. No statement failed, so there is no counterexample to report.

**How the statements were formalized:**
- A gap-≤2 counterexample is a set where every element except the largest is followed by `a+1` or `a+2`. This is the same as saying every gap between consecutive elements is at most 2.
- `primePower_window_exclusion` keeps the hypothesis \(q\le M\) because you asked for it. The proof doesn't need it: if \(q>M\), no element of \(A\) can be divisible by \(q\) anyway. That is the unused-hypothesis warning.

I also added these results to the Properties table, marked proved. The table already had many entries from earlier work, so some of these may duplicate older rows.

# Summary of changes for run 641eb380-6c2a-4ab8-bca1-84cbd16b55ef
I've stopped work so you can add your material. Everything is committed and the project builds.

**Verdicts:** `PHYSICAL FACTORIZATION CLOSED` (in the small-ε₀ regime) and `EFFECTIVE ARITHMETIC CLOSED`. Erdős #287 is still open, and I have not declared a provider-free `Tail287`. Details, including before/after signatures, are in `ERDOS287_PARAMETER_SOURCEFIT_JUNCTION_REPORT.md`.

**Priority 1, actual parameters** (`Physical/Factorization/ActualParams.lean`)
- `Dlow_eq_rpow_beta` proves \(D_{\rm low}=X^\beta\) from the existing definitions.
- `CritRegime` is the small-ε₀ regime: \(0<\kappa<10^{-5}\) and \(T\ge100/\kappa\). It is not arbitrary `Good`.
- `critRegime_Tchoice` shows the fixed choice \(T=\lceil100/\kappa\rceil+2\) works for every such κ.
- In the regime: `beta_lt_kappa` gives \(\beta<\kappa/100\), and `Dlow_sq_le` gives \(D_{\rm low}^2\le X^{\kappa/2}\) with no extra hypothesis.
- On critical cells (\(X^{3\kappa}\le N\le X^{1/3+\kappa/2}\)), `atomParams_of_crit` derives every `AtomParams` field with δ = κ. That includes \(X^{2\delta}\le N/D_{\rm low}\) and \(N\le X^{1/3+\delta}\).
- New theorem `atom_factorization_actual (h : CritRegime S κ) (hN : CritCell S κ N) …`. Compared with `atom_factorization_clean`, it drops the hypotheses `AtomParams S δ N` and `D_low² ≤ X^{δ/2}`.

**Priority 2, source fit** (`TypeII/ProviderDictionary.lean`)
- Decision: literal membership of each modulus in \(\mathcal D^+\) is not needed. I dropped it as a blocker. The downstream estimate only needs one-bounded sequences with the right supports and the three boxed range conditions of spec §18.
- That reading relies on the spec's description of Prop. 4.4; Pascadi's full text is not in the repository.
- Proved: `boxed_one/two/three`, `boxed_mono`, the coefficient dictionary `physCoefAtom_eq_dict`, and `physAtom_provider_contract`. The contract covers one-boundedness, supports, pairwise coprimality, the scalar bound, and the three boxed inequalities with ε = κ/2000.

**Priority 3, Ordering-B** (`TypeII/SourceComposed.lean`)
- `scalarTypeII_eq_cells` is an exact identity: the scalar Type-II source equals the sum of the actual Ordering-B cells over atoms and dyadic scales, plus the \(h_lU_r\) part.
- `packet_typeII_eq_cells` sums it once over the packet set Ξ. The designated pair is part of the packet index and is not summed again.
- `physCell_contract` gives the support, norm and size-range contract for each cell.

**Remaining analytic providers** (`TypeII/RemainingProviders.lean`; full statements, not proved)
- `PascadiCriticalCellProvider`: Pascadi's beyond-half estimate. Moduli reach \(X^{59/100}\), so ordinary BV/BDH does not cover it.
- `OrdinaryBVUremProvider`: the \(h_lU_r\) part, which is in ordinary BV/BDH range.
- `SWSeq`: a Siegel–Walfisz condition on α, used as a hypothesis inside the Pascadi provider.
- `scalarTypeII_bound_of_providers` is proved assuming these two providers.
- Still outside this file: non-critical routing, Heath–Brown/partial summation, BaseSW and the seven-block framework.

**Priority 4, effective arithmetic** (`Effective/LcmBound.lean`, `Effective/V103Comparison.lean`)
- `Lh_le_four_pow` proves \(\mathrm{lcm}(1..h)\le4^{h-1}\) for every h.
- Consequences: `log_height` (\(8^h\le M\Rightarrow h\le H_*(M)\)) and `floor_log_le_Hstar` (\(\lfloor\log M/\log 8\rfloor\le H_*(M)\)).
- New theorem `log_height_nine (hM : 9^h < M) : h ≤ Hstar M` drops the `LcmBound3` hypothesis. The old conditional theorem is kept.
- V103 comparison: V103's text isn't in the repository, so I proved structural facts about the Lean definitions instead (multiplicity, support, normalization, monotone endpoint). My question asking for V103's literal definitions is still unanswered.
- Uniform hinge positivity and finite-bank certification remain explicit, unproved inputs.

**Checks:** `lake build RequestProject.Erdos287.SourceChain` succeeds (8146 jobs), and so does `RequestProject.Erdos287.Effective.Audit`. `#print axioms` on the composed theorems (in `JunctionAudit.lean` and `Effective/Audit.lean`) shows only `propext`, `Classical.choice` and `Quot.sound`. The new files contain no `sorry`, `axiom`, `native_decide`, `unsafe` or `implemented_by`.

# Summary of changes for run fc7acf0b-67ef-4b68-8521-243fb9aa9422
**Verdict: PARTIAL CONSTRUCTION.** All the combinatorial parts are proved in Lean with no `sorry`, but one source-fit gap remains: support is proved at box-endpoint level, not at the level of each actual modulus. No SOURCE MISMATCH was found. Erdős #287 is still open, and nothing here claims Tail287.

All work is in `RequestProject/Erdos287/SourceChain/Physical/`. The full write-up, with before/after signatures, is in `ERDOS287_PASCADI_FACTORIZATION_EFFECTIVE_REPORT.md`.

**What is proved**
- **Pascadi Prop. 5.2, constructive (§1).** The greedy proof, including Lemma 5.3 and Cases 1–3, is formalized on the ordered list of prime factors with multiplicity (`InDplus` follows Def. 5.1). `prop52_nat` covers all of Pascadi's parameter conditions and gives \(d=d_1d_2d_3\) with \(d_1\le Nx^{-\delta}\), \(N^2d_2d_3^2\le x^{1-\delta}\) and \(N^2d_2^5d_3^2\le x^{2-\delta}\). The cases \(d=1\), fewer than six primes, and boundary equalities are handled by padding with 1's.
- **Support of the actual atoms (§2).** Every nonzero low-sieve coefficient is squarefree, uses only small primes, and lies in \(\mathcal D^+\) for even \(J\) or \(\mathcal D^-\) for odd \(J\) (`kappa_sector`). The upper endpoints of the high-prime boxes lie in Pascadi's support set when \(\delta\le 1/5000\) (`boxVec_vecHyp_pascadi`).
- **Factorization of each atom.** `atom_factorization` gives the three inequalities, each with an explicit extra factor \(D_{\text{low}}^2\). `atom_factorization_clean` gives Pascadi's exact system, with \(\delta/2\) in place of \(\delta\), under the extra condition \(D_{\text{low}}^2\le X^{\delta/2}\).
- **Three-colour decomposition (§3).** `ellX_tensor` is an exact signed identity for every modulus. Its factors are bounded by 1 in absolute value (`colFactor_le_one`, `abs_lowFactor_le`), have coprime supports and correct size ranges. The total variation is at most \(\sum_{J\le T^2}H^J3^J\), which depends only on \(T\) (`total_variation_le`).
- **Split parameter removed (§4).** The new `physCoefAtom` takes no `σ : SplitRule`. `physCoefAtom_reassemble` sums back exactly to \(\Gamma\sum_d 1[(f,d)=1]\ell_X(d)g(d)\). `typeII_source_decomp` splits the source atom by atom, and `physOB_source_eq_T` matches it to the Ordering-B source. The old `TypeII/Instance.lean` is kept unchanged; no other downstream declaration used `σ`, so no other signature changed.
- **Heath–Brown sign (§5).** The corrected sign \((-1)^{j+1}\) and the negative-control fixture for the printed sign are both kept and appear in the axiom audit. The new Type-II source does not recombine Heath–Brown terms, so the false sign cannot come back through it.

**Why this is not CLOSED**
- **Support level.** I did not prove that each actual modulus \(d=b\prod q_i\) itself lies in \(\mathcal D^+(x^{3/5-50\delta})\). Instead the factorization is applied to box endpoints, with the low factor \(b\) put into \(d_1\). That is where the \(D_{\text{low}}^2\) cost, or the extra condition, comes from.
- **Repeated boxes.** These are handled by averaging over random colourings, with an explicit nonnegative weight \(3^J\prod\gamma_k/(\gamma(P)3^K)\), rather than a multinomial expansion.

**Remaining analytic inputs (§6), none proved or assumed proved**
- Pascadi's beyond-half spectral estimate. Ordinary BV/BDH does not supply it, and I have not counted it as doing so.
- BV/BDH, the remainder terms, Poisson summation, fundamental-lemma main terms, partial summation, and the seven-block assembly.

**Effective-finisher module (earlier request):** new module `RequestProject/Erdos287/Effective/` (`Finisher.lean`, `Hinge.lean`, `Audit.lean`, plus the aggregator `Effective.lean`). It is independent of the Type-II code. Verdict: **EFFECTIVE FINISHER: FORMAL ARITHMETIC CLOSED**, with these conditions stated as hypotheses:
- `one_prime_finisher` and `row_empty` are proved outright.
- `onset_exp`: \(M\ge e^{12}\Rightarrow H_*(M)\ge10\).
- `sbMeasure_sum`: the size-biased measure sums to 1.
- `not_ce_of_hingeT_pos`: \(T_M>0\) rules out a counterexample.
- `no_ce_of_finite_and_hinge` is conditional: it assumes a finite exclusion and a uniform hinge bound.
- The logarithmic height lemma assumes \(\operatorname{lcm}(1..h)\le 3^h\) as a hypothesis. That bound is checked by computation only for \(h\le40\).
- I reconstructed the hinge statistic and the size-biased measure from your description; please check that they match what you intended.

**Build and audit:** `lake build RequestProject.Erdos287.SourceChain.Physical RequestProject.Erdos287.Effective.Audit` succeeds. Every audited theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. A search finds no `sorry`, `axiom`, `native_decide`, `unsafe` or `implemented_by` in the new files. The Properties table lists the main results, and all work is committed.

# Summary of changes for run 1bba1d7a-37a4-4c72-afd3-e21bb812644e
**Verdict: SCALAR SOURCE COMPLETE.** For Type-II, every construction is done except one formula, where the work is **BLOCKED**. Erdős #287 is still open, and I do not claim `Tail287`.

All new work is in `RequestProject/Erdos287/SourceChain/Physical/`, and every proof that was already there is kept. Details are in `ERDOS287_PHYSICAL_SOURCE_COMPLETION_REPORT.md`.

**Task A (scalar coefficient), files `Scalar/*.lean`:**
- **Low-prime weights:** \(\lambda_{\rm low}^{\pm}\) follow Pascadi's Definition 5.1 (squarefree, primes \(< u_0\), level \(D_{\rm low}\)). I use even \(J\) = upper, odd \(J\) = lower. That matches Lichtman's proof; his printed proposition statement has the opposite convention.
- **Box grid:** explicit endpoints, ownership by the least box containing the prime, parity-dependent thresholds, repeated-box multiplicities, and the empty case \(J=0\).
- **The coefficient:** \(\ell_X\) is written literally as the source formula.
- **Proved facts:**
  - `ellX_support`, and `ellX_level`: \(d \le D_{\rm tot}=X^{59/100}\).
  - `Dtot_eq`: \(D_{\rm tot}=D_{\rm int}^{1+\epsilon_0+\tau}\), kept as a separate fact.
  - `ellX_J0_sector`: the full coefficient is not ordinary \(\lambda^+\); only its \(J=0\) part is.
  - `UX_eq_parity_sum`, `UX_nonneg`, and `abs_ellX_le` (\(|\ell_X|\le T^2+1\)).
  - `UX_majorant`, proved separately and not by definition: \(U_X(v)\ge1\) whenever every prime factor of \(v\) exceeds \(z\).

**Task B (Type-II), files `TypeII/*.lean`:**
- **Heath–Brown identity** (`heathBrown`, `heathBrown_three`). One repair: the sign \((-1)^j\) printed in Maynard's Lemma 5.3 is a misprint. The correct sign is \((-1)^{j+1}\), and `maynard_printed_sign_false` refutes the printed version.
- **Coefficients:** the terms split into dyadic cells \(\alpha*\beta\). Proved: \(|\alpha_n|\le1+\log n\), the support of \(\alpha_n\), and \(|\beta_m|\le(1+\log m)^5 d_5(m)\).
- **The square:** \(V_\xi\) is written literally with all masks, residues and ranges. Proved about it: `V_expand`, `T_sq_le` (first Cauchy–Schwarz step), and `base_congruence`.
- **Coefficient \(c_{\xi,l,r}\)** (`physCoef`) is built from the actual \(\ell_X\). Proved: its bound, that nonzero coefficients have \((l,r)=1\), and that summing it over \((l,r)\) gives back the scalar sum exactly.
- **Where it is blocked:** the formula for splitting \(d=l\cdot r\). Pascadi's Proposition 5.2 only says a suitable split exists; no supplied source gives an explicit rule. So the split rule is an explicit parameter. The three-colour tensorization is also not done.

**Task C (bridges), files `Bridge.lean` and `TypeII/OrderingB.lean`:**
- I started from the independently defined Maynard weight \(w_X(t)\). For the actual \(\ell_X\), the moment with the \(\ell\)-th divisor deleted and primality replaced by \(U_X\) equals the designated-pair packet sum exactly (`majorizedMoment_eq_packets`).
- The literal two-prime moment is only **bounded above** by the packet sum (`twoPrimeMoment_le_packets`), not equal to it. This is because primality is replaced by the majorant \(U_X\ge1\).
- `source_eq_T`: the independently defined Type-II source equals \(T_\xi\) exactly.

**Remaining analytic hypotheses (none discharged):**
- an explicit well-factorable split rule, plus the three-colour tensorization;
- Bombieri–Vinogradov / Barban–Davenport–Halberstam beyond 1/2;
- the bounds \(R_{\rm rel}, R_{\rm base}=o(\cdot)\), the Poisson identity, and the bounds for \(V_\xi\);
- fundamental-lemma main terms;
- partial summation from \(\Lambda\) to primes, and removal of prime powers and log weights;
- the seven-block assembly that would give `Tail287`.

**Checks:**
- `lake build RequestProject.Erdos287.SourceChain.Physical` succeeds (8101 jobs) with no errors or warnings. The aggregator now imports all the new modules.
- No `sorry`, `axiom`, `native_decide`, `unsafe` or `implemented_by` appears in the new files.
- `SourceAudit.lean` prints the axioms of every key theorem; each depends only on `propext`, `Classical.choice` and `Quot.sound`.
- Negative controls:
  - `maynard_printed_sign_false`: the identity with the printed sign is refuted.
  - `Uz_mul_needs_coprime`: the multiplicative split needs \((l,r)=1\); it fails at \(l=r=2\).
  - `ellX_J0_sector`: confirms the full coefficient is not ordinary \(\lambda^+\).

# Summary of changes for run 2f276251-72d1-456a-b940-2e505c4a7c7e
I built the designated-pair packet source in Lean and proved the exact pair-indexing identity, with no `sorry`. **`Tail287` is still not proved unconditionally, and Erdős #287 remains open.**

**The spec file.** There was no ZIP, no SHA-256 manifest and no `sources/KNOWN_GAPS.md` in the repository. The spec was at the root as `physical_spec.md`, and I copied it unchanged to `sources/physical_spec.md`. I read all 2,302 lines, through Part XII and its last line. Its SHA-256 is `8a235ea3…0f0303`; with no manifest, there was nothing to check it against.

**New Lean files**, all in `RequestProject/Erdos287/SourceChain/Physical/`, plus an aggregator `Physical.lean`. The only change to an existing file is one import line in `SourceChain.lean`; your BV/SW adapter and one-sided seven-block work are untouched.
- **Definitions taken directly from the spec:**
  - the Maynard coefficient \(\omega_d\), the labelled packet \(\xi=(j,\ell,d,d')\), \(q_i\), \(q_0\), \(f_\xi=a_jWq_0\) and \(\Gamma_\xi=\omega_d\omega_{d'}\);
  - \(c_\xi\) and \(b_{\xi,d}\), each defined as the least CRT solution;
  - \(A_{j\ell}\) and \(B_{j\ell}\);
  - prime counts \(P_j\) (not von Mangoldt weights), \(V_j=\int dt/\log t\) and \(E_j\);
  - the literal pair term, and the remainder \(R_\Sigma^P\).
  - I also defined \(W=\prod_{p\le\log\log\log X}p\) and the explicit plateau profile \(\Psi\).
- **Residues:** I proved existence, uniqueness and \((c_\xi,f_\xi)=1\), and the same for \(b_{\xi,d}\). \((A,B)=1\) and \((g,d)=1\) are proved, not assumed, as is the equivalence of the reduced and unreduced congruences. Every inverse is an explicit Bézout coefficient.
- **Key congruence (`packet_congruence_iff`):** for \(p=L_j(t)\), all of \(W\mid t\), \(q_i\mid L_i(t)\) and \(d\mid L_\ell(t)\) hold together exactly when \(p\equiv b_{\xi,d}\pmod{f_\xi d}\).
- **Pair-indexing identity (`pairSum_eq_packets`):** the literal pair term equals \(\sum_\xi\Gamma_\xi\sum_{(d,f_\xi)=1}\ell_X(d)P_j(f_\xi d,b_{\xi,d})\). Also proved:
  - `RSigmaP_eq_packetIndexed`: the same sum over the single packet set, with \(j=j(\xi)\);
  - Main + \(R_\Sigma^P\) decomposition, and \(R_\Sigma^P=R_{\rm rel}+R_{\rm base}\) (§21);
  - a packet-by-packet adapter to the existing generic tensor source;
  - a check showing that an unrestricted \(j\)-sum overcounts.
- **Also proved:** the presieve conditions hold for the actual \(W\) once \(X\) is large; \(\Psi\) is smooth, compactly supported and at least 1 on \([1,2]\).
- **Conditional tail (`Tail287_of_physical`):** it uses the literal \(R_\Sigma^P\), but still takes the seven-block framework, \(R_{\rm rel}=o\) and \(R_{\rm base}=o\) as hypotheses.

**The old interface can't hold the physical source.** A single `TensorSource` / `TailSourceFamily` would need its scalar support coprime to every \(f_\xi\) at once, and its sequences can't depend on \(\xi\). So the old `physicalTailSource` can't be built faithfully. The packet-by-packet adapter plus a tail boundary stated for a general remainder function replaces it (`framework_iff` shows the two framework forms are equivalent).

**Formulas still missing, and the first theorem each blocks:**
- **Low-prime weights \(\lambda_{\rm low}^\pm\)** and the concrete high-prime box grid \(P_h\): these block the definition of \(\ell_X\) itself (left as a parameter here), and so the claim that \(U_X\ge0\) and majorises.
- **Type-II coefficients \(c_{\xi,l,r}\) and the Heath–Brown sequences \(\alpha_n\):** these block the physical Ordering-B square \(V_\xi\), i.e. the Ordering-B cells.

**Checks:**
- `lake build RequestProject.Erdos287.SourceChain` succeeds.
- The new files contain no `sorry`, `axiom`, `unsafe` or `native_decide`.
- `#print axioms` on 35 new theorems shows only `propext`, `Classical.choice` and `Quot.sound`.
- `leanchecker` exits 0 on each of the 8 new modules, checked one at a time.
- The full `SourceChain/audit.sh` did not finish within the time limit, so I can't report it as passing.

Details are in `ERDOS287_PHYSICAL_PACKET_SOURCE_REPORT.md`.

# Summary of changes for run 178dad44-fd24-4f83-8086-69cdb54b6e3d
I did not construct the physical source, and `Tail287` still cannot be proved with zero hypotheses. The conditional tail theorems are kept as they were.

**Your specification reached me cut off.** I could read only the first ~2,500 of the roughly 58,000 characters, ending at "…revised seven-block tail framework using the corrected dic…". No spec file or `manuscript.pdf` is in the repository. My follow-up question went unanswered, so I invented none of the missing formulas. I've flagged the truncation to the Harmonic team.

**BV/SW import (Priority 2)**
- **Versions:** the `openai/math` statements are pinned to commit `adc7f124…`, Lean v4.34.1 and Mathlib `d13f23b…`. This project uses Lean 4.28, so they can't be imported directly.
- **Transcription:** I copied the statements word for word into `OAIImport/Defs.lean` (only change: `NNReal.mk a h` written as `⟨a, h⟩`).
- **Audit in their own environment:** I built the external `PrimeGaps` code, and there it passes:
  - the transcribed statements are definitionally equal (`Iff.rfl`) to `SiegelWalfisz` and `BombieriVinogradov`;
  - `siegelWalfisz` and `bombieriVinogradov` use only `propext`, `Classical.choice` and `Quot.sound`;
  - `leanchecker` exits 0.

  The script and outputs are in `external/oai_primegaps_crosscheck/`.
- **Type gap closed, proved without `sorry`:** the external BV is an endpoint ψ-form. `ordinaryBVProvider_of_OAI` shows it implies the project's prime-counting `OrdinaryBVProvider` (main term π(x)/φ(Q), all x ≥ 2). The proof uses discrete summation by parts, ψ−θ ≤ 2√x log x and ∑1/φ(Q) ≤ (1+log X)².
- **Also proved:** the exact dictionary to `progErr`, the BV statement in project notation, and AP-form Siegel–Walfisz for q ≤ (log x)^B from the external BV alone.
- **What this does not cover:** this is ordinary BV for Λ, not divisor-weighted BDH or beyond-half distribution. `BaseSWProvider` concerns the physical sequences α_j, which haven't been defined, so it is not discharged.

**One-sided seven-block layer (proved)**
- `one_sided_moment_ineq`: a lower bound on 𝔼P and an upper bound on 𝔼Q, with the strict margin, give 2(𝔼P+2𝔼Q) < (𝔼P)².
- `OneSidedSevenBlockDictionary` allows model errors e₁, e₂ that need not vanish when R = 0. `oneSided_of_twoSided` shows the old dictionary implies the new one.
- The revised tail results are `tail_of_remainder_littleO_oneSided` and `Tail287_of_MinimalAnalyticProviders_oneSided`. The framework itself is still an input. The constants μ_lower, ν_upper come from the unread manuscript, so the theorem is stated for any constants that satisfy the margin.
- I checked `prescribedShape_gcdClique` and `edgeOnly_compiler`. They are gcd-shift constructions (edge-only is a direct corollary) and say nothing about moments.

**Your five questions**
1. **Constructed:** the transcribed statements, the BV→`OrdinaryBVProvider` adapter, and the one-sided consumer, framework and tail boundary. The physical source, cells, scale and seven-block framework were not built.
2. **Providers removed:** `OrdinaryBVProvider` now follows from the externally proved BV. The two-sided dictionary is replaced by the weaker one-sided one. No argument of `Tail287_of_MinimalAnalyticProviders` disappears.
3. **External audit:** passed.
4. **First remaining blocker:** the definitions of the pair-packet source (Ξ, Γ_ξ, f_ξ, c_ξ, b_{ξ,d}, α_n), needed for `physicalTailSource`. The report lists each missing formula (also c_{ξ,l,r}, λ_low^±, Ψ, box ownership) with the first theorem it blocks.
5. **Zero-hypothesis `Tail287`:** no.

**Checks**
- `lake build RequestProject.Erdos287.SourceChain` succeeds, and the build-time axiom check confirms all 577 source-chain theorems use only the standard axioms.
- The new files contain no `sorry`, `axiom` or `native_decide`.
- `leanchecker` exits 0 on each new module.
- I re-ran all six negative controls and each was rejected as expected.
- I did not re-run the `leanchecker --fresh` pass over the whole source chain, which had stalled last run.

Details are in `ERDOS287_PHYSICAL_SOURCE_BV_IMPORT_REPORT.md`. To continue the physical construction, please commit the specification as a file (e.g. `sources/physical_spec.md`).

# Summary of changes for run 0ca433cd-164e-4ae0-bed6-c267547421bf
There is still no unconditional Lean tail theorem: I did not construct a provider-free `Erdos287.SourceChain.Tail287`, and Erdős #287 remains open. The strongest results are conditional tail theorems that take named hypotheses. The new work is append-only in `RequestProject/Erdos287/SourceChain/`; `CurrentTail/` and the other protected subtrees are unchanged (checked against the root commit).

**Verdicts**
- **V99–V100R4 consolidation:** `ERDOS287 SOURCE CHAIN FORMALLY CONSOLIDATED`, against the formulas you supplied in messages. The full V100R/V100R2/V100R4 papers, `COMPLETE_KERNEL_MEMBERSHIP.md` and the Opus report were not in the repository.
  - The two monolithic hypotheses `OrderingBSourceDictionary` and `AuxPieceProviders` are replaced by proved source algebra plus separately named hypotheses.
  - `MaynardE1Estimate` and `PascadiE2Printed` are no longer needed. `QuantitativeTH` is now derived from a narrow spectral hypothesis carrying the `7/32` exponent.
  - The new conditional theorems are `Tail287_of_MinimalAnalyticProviders` and `Tail287_of_NarrowProviders`.
  - Two hypotheses remain at source level because their full text was not supplied: `OrderingBPoissonReduction` and `SharpMembership`.
- **Actual-atom → positive \(W_4\):** `ERDOS287 ACTUAL-ATOM INTERFACE BLOCKED`. The canonical atom cannot yet be instantiated from the literal packet object.
- **Unconditional closure:** `SUBSTANTIVE PROVIDER REMAINS`. The first blocker is **physical-source construction**. The repository has no Lean definitions of the actual packet set, \(\Gamma_\xi\), sieve coefficients or smooth profile \(\Psi\). So `physicalTailSource`, `physicalOrderingBCells`, `physicalFamilyScale` and a Poisson-summation proof cannot be written faithfully, and I did not write surrogates. After that come:
  - `UpperSieveWellFactorable`: purely combinatorial, stated exactly, not yet proved;
  - the seven-block framework;
  - the deep analytic estimates (Siegel–Walfisz/Bombieri–Vinogradov, divisor-weighted BDH, reciprocal-divisor moments, Pascadi's \(W_4\) estimate, and the two-large-variable estimate).
- **Source mismatches:** none found. The Astra phase identity is exactly the already-proved PH.1 with \(l=q\). One correction is recorded: the full pair coefficient is \(\frac{200}{59}(1+\epsilon_0+\tau)\), not \(200/59\) alone.

**Proved in this session**
- **Source algebra:** Type-II split; relative centering with an explicit witness for every inverse; residue-fibre \(1/f\) density; Ordering-B square \(n_1\equiv n_2 \pmod{fl}\); zero-mode covariance; Poisson scaling and \(\mathscr P_M(kq_0,\rho_k)=\mathscr P_{M/k}(q_0,\tilde\rho_k)\); bounded-variation discrepancy; literal \(F_{AB}\) and \(F_{AA}\) objects with their sector split; recombination.
- **Scalar weight:** exact equality in the single convention \(\gamma(\mathbf D)=1\); unique low/high split; \(|\Gamma_1|\le1\); parity sign routing; \(\frac{391}{256}\) ledger.
- **Actual-atom layer:**
  - canonical `CleanAtom` with the exact CRT system, the no-dilation phase, and a counterfixture showing that dropping the \(Af\) colour changes the phase;
  - character expansion mod \(Af\), with total coefficient mass \(\le Af\) and \(T_H(\omega_t)\le Af\);
  - first Cauchy step into a positive \(W_4\), fixed-\(A\) domination, and the \(N^2/(fQ^2R^2S^3)\) prefactor with negative regression tests;
  - three separate narrow \(W_4\) hypotheses using the corrected term \(FC^2+B_0CS^2+FCHS\); a regression rejects the old \(FHS\) term;
  - packet exponents \(391/256\) (Astra) and \(775/256\) (V101), and a new conditional theorem `Tail287_of_AtomProviders`.
- **Repairs:**
  - an exact cross-coprime colouring identity, plus a regression showing a subpower partition count times a log-only saving is unbounded;
  - upper-sieve support implies \(d<D\);
  - V97 large-variable routing with the exact two-large estimate isolated, and the \(17/5-1/295\) safety margin.

**Trust check**
- Full `lake build`: success (9041 jobs), no `sorry`.
- A build-time check confirms that all 481 theorems in the source chain use only `propext`, `Classical.choice` and `Quot.sound`. `#print axioms` on the conditional theorems gives the same list, but they still take their hypotheses.
- `lean4checker` is not installed; I used `leanchecker`, which exits 0 on each of the 19 content modules checked individually.
- **`--fresh` did not complete.** The run on the whole aggregate was stopped after about 50 minutes at about 63 GB of memory.
- Two of the six negative controls were interrupted by memory pressure and not re-run.

**Reports (in the project root)**
- `ERDOS287_CURRENT_TAIL_FORMAL_REPORT.md`: new sections 9–12, including the change table, provider diff, updated closure graph and trust results.
- `ERDOS287_MINIMAL_ANALYTIC_INTERFACE.md`
- `ERDOS287_MESSAGE_SOURCE_INTEGRATION_REPORT.md`
- `ERDOS287_ACTUAL_ATOM_W4_FORMAL_REPORT.md`

Status labels (`V100R4_AuthorCandidate`, `IndependentAuditPending`, `PaperCandidate`, etc.) are recorded as documentation only; none of them is used as a Lean hypothesis.

# Summary of changes for run 2a932542-40fd-441a-bb93-ce8d6daaa95f
**Erdős #287 is still open, and TAIL-287 is not banked.** The asymptotic tail is formalized only as a conditional theorem; no unconditional version exists in Lean. The verdict is **`ERDOS287 ANALYTIC INTERFACE BLOCKED`**.

The first step I could not reduce is the Ordering-B `E₁` source dictionary: the Maynard reduction that turns the relative main part of `R_rel` into Type-II sums satisfying every hypothesis of the `E₁` estimate. The V95–V100 texts (including the V97/V98 coloured `E₁/E₂` work, V100 RBDH and the Opus verdict) are not in the repository. So this step is stated as a separately named, not-yet-proved assumption (`OrderingBSourceDictionary`), not folded into an analytic provider. The `E₂` and RBDH links, and the 7-block compiler/main-term framework, have the same status. I asked about uploading the V99/V100 texts but got no reply, so I worked from the formulas in your message.

**Files** (new only; W3, W2.984, the PostV87V90R/PostV71V87 subtrees and `ARISTOTLE_SUMMARY.md` are unchanged):
- `RequestProject/Erdos287/CurrentTail.lean` (aggregator) and 16 modules in `RequestProject/Erdos287/CurrentTail/`, plus `audit.sh`
- `ERDOS287_CURRENT_REPOSITORY_CENSUS.md` and `ERDOS287_CURRENT_TAIL_FORMAL_REPORT.md`, which has the full results table and the Bank / Conditional / Paper-level / Retired / Open sections

**Proved outright (no open inputs):**
- **V99 source:** `v99_relative_centering`, `R_Σ^P = R_rel + R_already_paid`, exact removal of the zero-frequency term, and the exact coprimality insertion identity.
- **RBDH algebra:** the CRT identity `rbdh_crt_identity`, the variance contraction, the CRT unit-class bijection, factorization multiplicity at most `τ(Q)`, divisor-weight transport, and SW at modulus `fq` giving relative SW.
- **Spectator norm:** the finite combinatorial bound (preimage count `3^K τ^K`).
- **Family payment:** the Cauchy routing `family_payment_tau`, with no multiplication of log errors by the packet population.
- **Near diagonal:** the counting bound `2NH/f + 2N` and its conversion to the reciprocal-density norm.
- **Ordering A (retired):** a counter-model showing it gives `K√f` against a true value of `K`.
- **Ordering B:** the structural routing, with `n₁ ≡ n₂ (mod f)` kept explicit after the first Cauchy step.
- **`E₁/E₂` source side:** coefficient placement, the CRT phase identity, and Fourier enlargement by `f`.
- **Exponent ledger:** exact rational arithmetic and the order of choice `δ → σ → K → X`. Only `7/128` is a paper value; the other loss coefficients follow the shape in your message.
- **Seven-block consumer:** `μ²/2 − μ − 2ν = 199965200021/14 > 0` and `α(Γ_{7,2}) = 2`. Moments within 1 of `(μ, ν)` give three occupied blocks, which contradicts an exact word through the existing affine compiler and row rigidity.
- **Also:** the closure DAG checks (acyclic, Ordering A feeds nothing, the tail feeds global #287 only through the splice) and 10 regression controls.

**Proved conditionally:**
- `RBDH_of_BDH` assumes only an ordinary BDH statement.
- `RSigmaP_littleO_of_providers` assumes the named providers (`MaynardE1Estimate`, `PascadiE2Printed`, `QuantitativeTH`, `BDHFamily`, `SpectatorMomentFamily`, `BaseSWProvider`, `AuxPieceProviders`) plus the dictionary.
- `Tail287_of_AnalyticProviders` (the conditional tail theorem) assumes all of these plus `SevenBlockTailFramework`. Its conclusion is an existential onset, not an effective one.

None of the providers is ever constructed. A build-time check confirms that none of them mentions `R_Σ^P`, the tail statement, counterexamples or exact words.

**Builds and audit:**
- The full `lake build` succeeded (9020 jobs) with no `sorry` warnings.
- The installed checker is `leanchecker` (not `lean4checker`); it passed on `RequestProject.Erdos287.CurrentTail` both normally and with `--fresh`.
- The axiom check covers 90 principal theorems; all use only `propext`, `Classical.choice` and `Quot.sound`.
- The new code contains no `sorry`, `admit`, project axioms, `unsafe`, `native_decide`, fake provider instances or `False.elim` providers.
- All 6 negative controls fail for the expected reasons.
- No statement turned out to be false.

**Still open:** the Ordering-B repair until it passes independent audit, the `E₁/E₂` dictionaries, the 7-block framework, the effective onset, the finite splice, global #287, and the dimension-floor issue (recorded as an open item).

# Summary of changes for run cf6c4dba-3d89-415e-bfee-8208b5aea028
I froze the W3 checkpoint and then wrote and audited the W2.984 package. The Lean side builds cleanly and is free of `sorry`, `admit`, project axioms, `unsafe` and `native_decide`. The analytic lemmas are written out in full in the paper but enter Lean only as hypotheses. One part is still owed at paper level: pinning down the specific \(O(\delta)\) constants, which the asymptotic theorem does not need.

**Two things you should know first**
- **A gap in Merikoski's Lemma 13.** The pointwise Chen inequality in its proof is false when \(n\) is not squarefree. Lean checks a counterexample: sifting primes up to 19, \(Y=4\), \(Z=20\), \(n=1925=5^2\cdot7\cdot11\), where the right-hand side is \(-\tfrac12\) (`merikoski_pointwise_fails`). I repaired it by adding a term \(\tfrac12\,\mathrm{sq}(n)\) (`chen_pointwise`, `chen_weighted`, `affine_chen_weighted`). The extra tail is negligible (§10 of the paper) and the constant is unchanged, so this does not block anything.
- **A gap in two published Bombieri–Vinogradov proofs (not their statements).** BFM Thm 4.2 and Merikoski Prop 11 are stated for all moduli \(q\) divisible by \(q_0\). Their proofs, however, assume the \(q_0\)-part of the character's conductor divides \(q_0\), which can fail for our non-squarefree bases \(a_jW\). Lemma 6.1 rechecks every step of the proof for our family of moduli.

**What is checked in Lean** (all in `RequestProject/Erdos287/W2984Publication/`)
- **Scalar certificate:** \(\Omega_1-\Omega_2+\Omega_3\le 796682507263/200000000000<3.984\) (`pairConstant_lt`). This includes the \(\Omega_1-\Omega_2\) integral identity, the Buchstab bound \(\omega\le3/5\), and \(\Omega_3\le14\log(3/2)-28/5\). No floating point is used.
- **\(\delta\)-budget arithmetic:** \(C_{\rm err}<85\) and \(\delta_0=6\cdot10^{-6}\) fits inside the room (`explicit_Cerr_lt`, `explicit_delta0`).
- **Affine arithmetic and the modulus ledger:** CRT for the designated prime, \(\phi(a_jW)=a_j\phi(W)\), the switched form, and the five-source ledger with total \(\tfrac12-2\delta+4\delta^2+\epsilon_W\le\tfrac12-\delta\).
- **Main implications:** the four Chen bounds give the per-pair bound (`pairExpect_le_chen`, `pairBound_of_chen`). Combined with the W3 framework, that gives **`W2984`** and **`W2984_counterexample_form`**, which reuse the imported W3 consumer unchanged.
- **Consistency check:** the same machinery with constant 4 recovers W3 (`W3_of_selbergPairBound`).
- **Regression controls:** one Lean control for each of the 12 shortcuts you listed, plus two extras (`RegressionSuite.lean`).
- **Hypotheses:** `W3FrameworkProvider`, `AffineChenS1/S2/S3Provider` and `AffineChenSquareTailProvider` are never constructed. A build-time check confirms none of them mentions W2.984, occupancy or contact conclusions.

**Trust audit**
- `lake build +RequestProject.Erdos287.W2984Publication` and the full `lake build` (9003 jobs) both succeed.
- The installed checker is called `leanchecker`, not `lean4checker`. `lake env leanchecker` and `lake env leanchecker --fresh` on the module both pass.
- The axiom check runs on 60 principal theorems; all use only `propext`, `Classical.choice` and `Quot.sound`.
- `audit.sh` passes: token scan, no SR-287/HLS imports, historical files unchanged, and five negative controls rejected.
- The older `PostV87V90R/audit.sh` (step 4) flags any file outside its own subtree, so it will now report the new subtrees. That is how the old script was written, not a regression.

**Files changed**
- New: the subtree `RequestProject/Erdos287/W2984Publication/` (10 Lean files plus `audit.sh`), the aggregator `RequestProject/Erdos287/W2984Publication.lean`, and the W3 checkpoint `RequestProject/Erdos287/W3Publication.lean` with `W3Publication/Checkpoint.lean` (aliases only, no new mathematics).
- Documents at the project root:
  - `AFFINE_CHEN_TRANSFER_W2984.md`: the full proof — the four admissibility facts that replace Merikoski's smoothness hypothesis, the corrected Lemma 13, the literal congruence system, the affine version of Merikoski §6, the ledger, Lemma 6.1, `AffineChenS1`/`S2` (lower bound)/`S3` (switched), the square tail, affine Prop 12, the scalar certificate, the \(\delta\)-budget, the downstream argument and effectivity.
  - `W2984_THEOREM.md`, `MERIKOSKI_DICTIONARY.md`, `W2984_FORMALIZATION_REPORT.md`, `OPUS_REAUDIT_PACKET.md` (it does not claim PASS) and `W3_PUBLICATION_CHECKPOINT.md`.

**What remains open**
- **Constants:** that \(C_1=392/9\), \(C_2=196\log\tfrac32\), \(C_3=5/2\) are the right values is argued in the paper, not formalized. Lean only uses the existence of constants that do not depend on \(\delta\), which is all the asymptotic theorem needs.
- **Analytic lemmas:** they are written proofs that the referee still has to check. They are not formalized, since Mathlib has no linear sieve or Bombieri–Vinogradov with exceptional moduli.
- **Scope:** the theorem is stated only for \(s>2.984\), with nothing claimed at the endpoint. It is tagged `ineffectiveExistential`.

**W2.984 REFEREE PACKAGE READY. W3 remains independently valid. W2.984 is reduced to the fully written fixed-affine analogues of Merikoski's Chen-sieve estimates, with the exact finite/combinatorial implication kernel-checked. Erdős #287 remains open, and the theorem is asymptotic and ineffective.**

# Summary of changes for run c225e860-8425-4f57-9b2e-d392135e529c
**Erdős #287 is still open; this work does not prove it.** I built the new append-only subtree. Everything that doesn't depend on a prime-distribution input is kernel-proved. W3, `E287_11_4` and the global splice are proved only as implications from explicit providers. None of those providers is ever constructed.

**Files (all new):** the subtree in `RequestProject/Erdos287/PostV87V90R/` contains `ModelCompatibility`, `ContactCycle`, `MomentConsumer`, `AffineCompiler`, `RowRigidity`, `OccupancyContact`, `RetiredRoutes`, `WidthThree`, `NarrowWidth`, `RegressionSuite`, `ClosureDAG`, `AxiomAudit` (all `.lean`) and `audit.sh`. The aggregator is `RequestProject/Erdos287/PostV87V90R.lean` and the report is `ERDOS287_POSTV87_V90R_REPORT.md`. `PostV64V71/`, `PostV71V87/` and `ARISTOTLE_SUMMARY.md` are unchanged; `audit.sh` checks this against the root commit.

**Exact results (kernel-proved, no open assumption):**
- **Model reuse:** `counterexample_iff_exactWord`, `ExactWord.exp_lower`/`exp_upper` (giving \(e(a-1)<M\le e^2(a+1)\)), `omitted_neighbours`. The subtree uses the existing `PostV71V87` word model directly.
- **Cyclic graph:** `alpha_contactCycle` proves \(\alpha(\text{ContactCycle } r\, m)=m\) for all \(1\le m\), \(2m\le r\). Also `alpha_G_11_2` (\(\alpha(G(11,2))=3\)), with `decide` checks over all 4-subsets.
- **Width geometry:** `width_ratio`, and `widthParam_spec`, which gives an explicit \(m\) with \(3+1/m<s\) for each \(s>3\).
- **Repaired moment consumer:** `moment_cauchy`, `expected_occupancy_lower` and the existence theorem `exists_occupancy_of_moment`. Then `moment_numerical` and `occupancy_11_3`, which need both \(C<11/3\) **and** the first-moment bound.
- **Sharp mean consumer, fully proved:** `qbal_le_pairs` (integer balancing), `sharp_mean_consumer` and `exists_occupancy_of_sharp`. The Jensen step did not need a provider.
- **Affine compiler:** `affine_adjacency` (\(n^+=n^-+1\)) with its integrality lemmas.
- **Row rigidity:** `BH_pos`, `selRow_empty_of_bounded_cofactors`, `adjacent_empty_rows_contradiction`.
- **Occupancy to contradiction:** `false_of_edge`, `occupancy_contact_false`, `moment_contact_false`.
- **V88 facts kept:** `conductor_replication`, `primePower_replication`, `guardOwner_unique`, `lcm_transfer`.
- **Retirement evidence:** `single_grid_realizable`, `even_multigrid_realizable`, `exterior_obligations_do_not_combine`, `proximity_density_no_contact`, and `crossScale_retired_equiv_tail` (cross-scale synchronization is equivalent to tail exclusion, so it is not a reduction).
- **Checks:** 10 regression tests in `RegressionSuite.lean`, and the `ClosureDAG` theorems (acyclicity, no retired node feeding a current one, global #287 open, the obsolete `11/6` constant unused).

**Conditional results (the implication is proved; the input is open):**
- `W3_of_provider`, `W3Statement_of_provider`, `W3_family_of_providers`. Only the step from `WidthThreeMomentProvider s` to W3 is proved; W3 on its own is not.
- `tail_of_W3family_narrow` and `erdos287_of_W3_narrow_finite`.
- `E287_11_4` (turns the 11-block provider into a narrow-chamber closure) and `tail_of_E287_11_4`.

The new owner of the remaining chamber is `NarrowWidth287`.

**Still open:** the width-\(>3\) analytic moment theorem, existence of the finite gcd compiler, the \([e,3]\) chamber, the `E287_11_4` provider, finite exclusion below the onset, the general annulus barrier (not needed downstream), and global #287.

**Audit findings:**
- The hypothesis \(p^2>M\) in the row-rigidity statement is unnecessary, so I dropped it; the theorem is stronger without it.
- A provider indexed by exact words would make W3 hold trivially, because those words are exactly what is being refuted. The providers therefore range over windows \((a,M)\), and I proved such windows exist beyond every onset.
- No statement from the prose turned out to be false, and W3 needs no hidden synchronization beyond what its provider states.

**Build and placeholder status:**
- `lake build RequestProject.Erdos287.PostV87V90R` succeeds.
- Full `lake build` succeeds (8990 jobs).
- `lake env leanchecker --fresh RequestProject.Erdos287.PostV87V90R` exits with code 0.
- `audit.sh` prints AUDIT PASSED, and all 7 compile-fail negative controls are rejected for their expected reasons.
- No `sorry`, `admit`, `axiom`, `unsafe` or `native_decide` appears in the code; those words occur only in comments and in the deliberately failing test files.
- About 85 principal theorems are checked during the build to depend only on `propext`, `Classical.choice` and `Quot.sound`.

The report ends: "This subtree does not prove Erdős #287. It kernel-verifies the post-V87 finite/combinatorial consumers and the exact implication from the explicit analytic providers to the width reductions. Any unformalized prime-distribution input remains an explicit assumption."

# Summary of changes for run ef8a6cb0-8a28-4788-8935-d20a58eb750f
I added the post-V71 → V87 bank as a new subtree, `RequestProject/Erdos287/PostV71V87/` (namespace `Erdos287.PostV71V87`, aggregator `RequestProject/Erdos287/PostV71V87.lean`). **Erdős #287 is not solved and remains OPEN.** Every build and audit check passes, and nothing in the subtree uses `sorry`, `admit`, a custom `axiom`, `unsafe` or `native_decide`.

No V83–V87 source documents are in the repository, so every statement was rebuilt from the descriptions in your request. Where no complete proof was given, the claim is an explicit hypothesis or marked OPEN.

**Files.** 17 Lean files, the aggregator, an audit script (`PostV71V87/audit.sh`) and the report `ERDOS287_POSTV71_V87_REPORT.md`. The report covers all 12 points of your section 14 in full. No existing file was changed; `git diff` against the initial commit lists only new files, and `PostV64V71/` and `ARISTOTLE_SUMMARY.md` are untouched.

**Proved with no assumptions** (axioms only `propext`, `Classical.choice`, `Quot.sound`):
- **Model:** exact words with `a > 1` are exactly the #287 counterexamples.
- **V83 (retired route):** \(C_R-D_R=B_R(S-1)\) and \(\operatorname{den}(C_R)=\operatorname{den}(S)/\gcd(\operatorname{den}(S),B_R)\); fixed-depth tests reduce to `den(S) ∣ gcd B_R`; `{1,2,3,6}` (mass 2) passes every test; a determinant of an integer matrix is always an integer.
- **V84/V85 positional chain:** absent modulus → forced omission → forced neighbours → singleton rejection; also \(Q_2\le M-a\).
- **V86 endpoint CRT:** `endpoint_anchored_crt` (\(de>M\) or \(M-a<de<2a\)), \(Q_pQ_r>M-a\) for \(p\ne r\), at most one \(p\) with \(Q_p\le\sqrt{M-a}\), the low-start chamber, dyadic saturation, the ceiling annulus, and owner-disjointness for large primes.
- **V87:** `log_Srec_le` (\(\log S_{\rm rec}(H)\ll H\log\log H/\log H\)), the shell fingerprint, and `repaired_recurrence` (\((M-a)/q_*\ge c\,\log D\log_2 D/\log_3 D\) with an absolute constant). The recurrence does not depend on \(\delta_0\) or on any assumption; its only analytic input is Mathlib's Chebyshev bound.
- **Physical consequences:** the `(1,0,1)` guard pattern at every internal \(q_*\)-multiple; a lower bound on the number of disjoint guard triples; \(P_p\ge p\) and \(P_p^4>D\) for non-exceptional \(p\) with \(p^2\le D\) (no other largeness condition needed); the at-most-four overlap bound; and the carrier-union lower bound.

**Proved only under an explicit, never-constructed hypothesis:**
- From the V84/V85 prime-supply assumptions (fixed-modulus and uniform versions): the fixed-base and growing-base growth results, and the maximal-carrier result.
- High-shell emptiness at a nontrivial threshold.
- `tail_closure_of_crossScale` and `erdos287_of_crossScale_and_finite`, assuming `CrossScaleSynchronization287`; the second also assumes finite exclusion below \(M_0\).

**Retired:** the V83 fixed-depth minor route as a way to close #287.

**Open:** `Proximity287`, `CrossScaleSynchronization287`, intermediate scales, finite exclusion, and the aggregate rough-part estimate. The rough-part estimate has no formal statement because no complete proof was supplied.
- I proved that every exact word satisfies all the conditions bundled into `CrossScaleSynchronization287`. So, as specified, that interface is *equivalent* to the tail of #287 (`crossScale_iff_tail`), not a weaker intermediate step.
- That makes **`Proximity287`** the first genuinely intermediate open theorem.

**Firewalls and regressions:**
- **Three zones:** everything below \(q_*\) is proved; above \(\lfloor M/2\rfloor\) all shells are provably empty, while "almost empty" at lower thresholds is conditional; intermediate scales are OPEN.
- **Terminal window:** the recurrence holds automatically in every polylogarithmic window, so it does not exclude \(M/(\log M)^B<q_*\ll M/T(M)\).
- **Regression fixtures:** `D ∣ X` vs `X = 0`; actual minor vs target-one quantity; surrogate tests vs exact mass; pointwise vs uniform statements; a realised second CRT branch; and a word with \(q_*=3\) that still has an active row at 5, so emptiness just above \(q_*\) does not follow from the definitions.

**Dependency graph and audits:**
- `ClosureDAG.lean` gives each result a status and checks the graph in the kernel with `decide`: it is acyclic; exact results depend only on exact results; every conditional result traces back to an open input; nothing exact or conditional uses the retired route; and the #287 node is OPEN, its open inputs being exactly the four listed above.
- `AxiomAudit.lean` makes the build fail if any of 73 principal theorems uses a non-standard axiom. It also fails if any declaration constructs one of the assumption interfaces without a hypothesis; the one exception is the trivial \(\lfloor M/2\rfloor\) high-shell case, which is allowed explicitly.
- Three negative controls (a `sorry` proof, a `native_decide` proof, and an assumption built without a hypothesis) are each rejected, as intended.

**Build results:**
- Narrow build: succeeded (8047 jobs).
- Full `lake build`: succeeded (8977 jobs).
- `leanchecker` on all subtree modules: exit 0.
- `leanchecker --fresh`: exit 0.
- `audit.sh`: AUDIT PASSED.

Work is committed, and the main results are recorded in the Properties table.

# Summary of changes for run 53169e9a-30d1-4a35-bc4b-b20c41bca5cc
I added a new append-only subtree, `RequestProject/Erdos287/PostV64V71/`, that formalises the exact, finite and algebraic parts of the V67–V71 delta bank in Lean. Erdős #287 is still open, and nothing here claims to solve it.

**Files added** (no existing files were changed):
- The aggregator `RequestProject/Erdos287/PostV64V71.lean`.
- `ReciprocalFingerprint`, `SourceRows`, `ResidualDenominator`, `DeterminantBox`, `ExceptionAccounting`, `TailClosure`, `FingerprintLogBudget`, `RoughPart`, `SourcePinned`, `ComponentFactorisation`, `LocalAdmissibility`, `WeightedCorrelation`, `CircleIdentity`, `AnalyticFrontier`, `RegressionFixtures`, `CurrentLedger` and `AxiomAudit`, all `.lean` files under `PostV64V71/`.
- The report `ERDOS287_POSTV64_V71_DELTA_REPORT.md`.

**Main results proved:**
- `determinant_supply_implies_no_tail'`: if you assume both `DeterminantSupply287` and `LcmUpperBound12`, there is no counterexample with maximum \(\ge 2^{1500}\). Both assumptions are unproved inputs.
- `exception_weight_loss`: the loss from excluding exceptional primes is between 0 and \(4H\log M\sum_{p\in E}\log p\).
- `mangoldt_prime_power_error_exact` and `mangoldt_prime_power_error`: the error from prime powers is between 0 and \(8H\sqrt M(\log M)^2\).
- Also proved: `circle_correlation_identity`, `weighted_subbox_le_full_supply`, `good_large_prime_row_empty`, `pinned_selected_mass` / `_iff`, the fixtures and the ledger.

**One statement is false as written:** in V67, the claimed equivalence of \(X(E)=0\) with \(D\mid X(E)\). Counterexample: \(P=D=2\), \(Y=1\) gives \(X=2\), so \(D\mid X\) but \(X\neq 0\). This is proved in Lean as `pinned_D_dvd_counterfixture`. The corrected versions, `pinned_W_dvd_iff` (using \(W\mid X(E)\)) and `pinned_D_dvd_iff_of_coprime` (keeping \(D\mid X(E)\) but adding \(\gcd(P,D)=1\)), are proved.

**One constant differs from the source:** the source gives 4 in the \(\sqrt M\) form of the prime-power error. Lean proves 8, because Mathlib's bound for \(\psi-\theta\) has constant 2. The downstream margin still holds with 8.

**Build:** `lake build RequestProject.Erdos287.PostV64V71` succeeds with no warnings in the new files; I fixed four linter warnings in `ExceptionAccounting.lean`. The full `lake build` also succeeds (8959 jobs). The new files contain no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `implemented_by` or `opaque`. All 51 declarations checked in `AxiomAudit.lean` depend only on `propext`, `Classical.choice` and `Quot.sound`.

**Still open:** `EffectiveMajorArc287`, `MinorArcLowerBound287`, `DeterminantSupply287` and #287 itself. `DeterminantSupply287` is never assumed outside explicit hypotheses or proved. The following external inputs are stated but not proved and are used only as named hypotheses: `D2LogBound287`, `AverageSingularSeries287`, `SiegelWalfiszLogModuli287`, `EventualMajorArc287`, `LcmUpperBound12` and `HuangFiniteExclusion287`. The Properties table now lists the main results.

# Summary of changes for run 631ab4c0-c63e-4199-9c5b-7054f803a299
**Erdős #287 remains open.** PG‑287 is defined but not proved, and no finite exclusion beyond \(M \le 4\cdot 10^9\) is formalised: the Huang 502‑digit certificate is not in the repository, so that range stays an explicit premise. No V53–V64 source documents were supplied either, so all definitions were rebuilt from your task text.

The repository now ends at the frontier you described. `PG287` (open) gives `PG287_implies_no_tail_source`, which gives `finite_exclusion_and_PG287_imply_erdos287`, which gives the original statement. The tail theorem also takes `PsiLowerBound` (\(\psi(M)\ge 0.9M\)) as an explicit hypothesis, because it is not formalised locally. The full table (object | Lean declarations | math status | formal status | axioms | supersedes | notes), the retired list and the audit findings are in `ERDOS287_POSTQSIGMA_V64_REPORT.md`. The same statuses are in Lean in `PostQSigma/Ledger.lean`, which only compiles if every listed declaration exists. Its `open_entries` theorem shows the only open entries are the original problem and PG‑287.

**Main results proved in Lean, all \(M\):**
- **V57 deep classification** (`deep_mandatory_classification`): if \(a\ge1\), \(H(a,M)\ge1\) and a layer with \(d\ge2\) is mandatory, then \((p,d)\in\{(2,2),(2,3),(3,2),(5,2)\}\). There is no census; the two leftover cases \((21,55)\) and \((21,56)\) are checked in the kernel.
- **`MAND = MAND1 ∪ Ddeep`**, with the two disjoint and every deep element lying in one of the four exceptional layers.
- **SC‑287 is retired by proof** (`SC287.prime_moduleA_false`): on the family \(M=2p-1\), \(a=\lfloor M/4\rfloor\), the bound \(\|A_p\|\le C p^\theta P\) fails for every \(\theta<1\) and every \(C\). This needs no external input; it rests on \(A_p = pN_p - P\), \(p\mid X(E)\iff p\in E\), and an exact Fibonacci formula for the forced count.
- **Translated‑row theorem**, with the \(p=7\) fixture: the translated row \(\{4,5,6\}\) passes and the prefix row \([1,6]\) fails.
- **Three‑status generating function and carry cosets**, including \(g = L_h/\operatorname{lcm} V\) and the firewall that an LCM‑complete reservoir gives \(g=1\).
- **Square‑certificate firewall**: interpolation, plus the punctured‑cube bound (degree \(\ge r\) on \(\{0,1\}^r\)).
- **Transfer matrix**: the recurrence and the matrix‑product form (exact algebra only, no contraction claim).
- **V54 source‑qualification identity**.

Earlier sections of this run also built and proved, among others, QSigmaStrong with the 84/168/105 fixture, the weighted primary cover, mandatory adjacency, the exact‑mass automaton with the mod‑\(W\) false‑acceptance fixture, the core/carry identity, hard‑core coefficient, no‑wrap, the conductor/Ramanujan identities, Gram PSD, the majorant \(N_T \le \lambda^T G\lambda\), and the \(W=30\) strictness fixture.

**Audit finding.** The deep classification is false if \(H(a,M)\ge1\) is weakened to \(2a\le M\). The counterexample \((a,M)=(22,50)\) has a mandatory \((7,2)\) layer and is proved in `deep_classification_needs_harmonic`. The proof also needs the sharp \(e>2.718\) bound; the weaker \(8(a-1)<3M\) is not enough. No formalised bank item was false once its hypotheses were made explicit.

**Not formalised:**
- the bound \(|\mathrm{Ddeep}|\le5\);
- the size‑\(\le3\) first‑digit classification and the \(3M\le8n\) endpoint cap (not supplied);
- the composite‑resonance and Croot firewalls (need PNT/Selberg/Croot; kept as documentation);
- the physical CRT fixture (its \((a,M)\) was not supplied);
- the explicit contact supply, isolated as the unasserted assumption `ContactSupply`. The contact–carry bridge is therefore proved only conditionally on the contact‑count hypothesis.

**Files:** 26 new modules in `RequestProject/Erdos287/PostQSigma/` (listed in §6 of the report), the aggregator `RequestProject/Erdos287/PostQSigma.lean`, and the report. `git diff --name-status 7a33e99` shows only added files; nothing existing was changed.

**Checks:**
- Full `lake build` succeeds (8941 jobs); its 26 warnings are all in pre‑existing files.
- `#print axioms` on 51 major declarations (`AxiomAudit.lean`) shows only `propext`, `Classical.choice` and `Quot.sound`.
- The new code contains no `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `unsafe`, `implemented_by` or `opaque`.
- `PG287`, `FiniteExclusionUpTo`, `ContactSupply` and `ContactDefect287` are never constructed or asserted.
- `leanchecker` without `--fresh` passes on the audit module. `leanchecker --fresh` timed out after 1750 s with no output, so there is no fresh‑replay result.

# Summary of changes for run 864f9c57-d33a-469c-9daf-b8a0f4751fdc
**Erdős #287 is not closed.** The interior is open, no explicit \(M_0\) was found, and only the existing \(M \le 4\cdot10^9\) part of the finite splice is covered. The result is **SUCCESS D**: an obstruction to the GOAL, backed by a heuristic and a paper argument rather than a proof.

**Missing input.** The V53–V54 audit material you cite is not in the repository (the newest bank is V30). I rebuilt the exact objects from the definitions in your message, for an arbitrary compulsory omission set \(R\) (one with \(R\cap A=\varnothing\)). The rough baseline \(R_b\) itself is not formalised and I have not re-checked that it is compulsory. One caveat: at \(b=1\) the simple top-layer argument would need \(\psi(x) < x - O(\log x)\), which fails for infinitely many \(x\). So \(b=1\) depends on the audited argument I don't have; any fixed \(b<1\) is safe. A proved compulsory baseline is formalised instead (`windowBaseline_compulsory`).

**What is proved in Lean.** Seven new files, `RequestProject/Erdos287/QSigma.lean` plus six in `RequestProject/Erdos287/QSigma/`. Nothing else was changed. They build with no `sorry`, no new axioms and no `native_decide`; all 27 main theorems use only the standard axioms. Namespace `Erdos287.ExactSource`:
- **Exact source:** \(\tau=\sum_B 1/n-1\); every solution has reciprocal mass exactly \(\tau\) and \(|E|\le R_T\).
- **Equivalence with the original problem:** two adapters (`sourceSol_of_counterexample`, `counterexample_of_sourceSol`) and `erdos287_iff_no_source` — #287 holds iff no source with \(1<a<M\) and \(R=\varnothing\) has a solution.
- **Carry system:** \(\kappa_{p,d}\), \(\Gamma_p=\sum_d\kappa_{p,d}\), \(Q_\Sigma\). Key results: `kappa_le_card_inter`, `no_solution_of_infeasible`, `kappa_mono`, and the sum-of-depths bound `Gamma_le_factorization_prod`.
- **(DIV):** `QSigma_dvd_prod`.
- **(CERT):** `no_solution_of_QSigma_gt_Pmax`, plus a sharper version against \(P_{\text{mass}}\le P_{\max}\).
- **Bounds on both sides of the inequality:** \(\operatorname{den}\tau \mid Q_\Sigma\) and \(Q_\Sigma \mid \prod_V n\); \(a^{|F|}\le P_{\text{mass}}\) and \(P_{\max}\le M^k\).
- **Baseline transport (exact):** `tau_transport`, `tau_add_compulsory_mass`, `omissions_transport` — changing \(b\) only moves the same omitted mass between compulsory and optional.
- **Conditional end theorems:** `erdos287_of_universal_certificate` and `erdos287_of_universal_certificate_above_4e9`. The second uses the project's existing check that no counterexample has \(M\le 4\cdot10^9\), so the GOAL is only needed above that. Both are implications whose hypothesis is the open GOAL.

**What is argued on paper only** (in `ERDOS287_QSIGMA_INTERIOR_REPORT.md`, not formalised):
- **Row entropy for general \(\lambda\):** rows have length \(c(1-e^{-\lambda})\log M\), with the dichotomy \(c(1-e^{-\lambda})h(\theta)<1\).
- **Summing over strips:** forced optional mass is at least \((\lambda\log(c_\lambda/b)+I(\lambda))/\log M\). I evaluated \(I(\lambda)\) numerically with an unverified script (\(\approx 0.156\) at \(\lambda=1\)). This rules out \((\lambda-1)\log M < \lambda\log\log M + K(\lambda)\), and \(b\) drops out exactly.
- **Ceiling on these methods:** strip arguments can only ever force \(O(1/\log M)\) mass. The interior has \(\tau\asymp\lambda-1\), so they cannot close it.
- **Deeper \(p\)-adic digits:** primes \(p\le\sqrt M\) contribute only \(O(M)\) to \(\log Q_\Sigma\).
- **Sharper product bound:** \(P_{\text{mass}}\) improves on \(P_{\max}\) by no more than a factor bounded in terms of \(\tau\) — no order-of-magnitude gain.
- **Varying \(b\):** answer (B). It only reclassifies mass, so I've marked \(b\)-optimisation retired.

**Obstruction.** In a random-residue model, \(\log Q_\Sigma=O(M)\), while \(\log P_{\text{mass}} \asymp \tau M\log M\). So \(Q_\Sigma > P_{\text{sharp}}\) is expected to fail as soon as \(\tau\log M\to\infty\), i.e. throughout the interior. Exploratory Python runs (\(R=\varnothing\), \(M\le 3200\); not verified in Lean) fit this: at \(\lambda\approx1.6\), \(Q_\Sigma\) already falls below a feasible product. The interior question is unchanged: it needs \(\kappa_{p,1}\ge\vartheta L_p\) for a positive-weight set of primes in \([M^{1-\varepsilon}, M/\log M]\).

**Ledger** (full table with exact names in §5 of the report):
- **BANK:** exact source, carry system, \(Q_\Sigma\) divisibility, product exclusion, baseline transport
- **PROVISIONAL:** \(\beta_b\) boundary theorem (not in the repository; redone on paper), general-\(\lambda\) entropy, multi-strip accumulation
- **STRICT REDUCE:** deeper \(p\)-adic amplification
- **RETIRED:** sharper product bound; \(b\)-optimisation
- **OPEN:** interior domination, explicit \(M_0\), finite splice, original Erdős #287

None of the new theorems turned out to be false. The only statement I had to change was `Pmax_le_pow`, which needs \(M>0\); I added that hypothesis.

# Summary of changes for run e831a131-22e0-49e9-82f8-15c487c13f43
I added Research Banks V29 and V30, but the result is **not** the SUCCESS A final bank. The outcome is **SUCCESS D (semantic mismatch)**: the analytic branches are not tied to the physical source anywhere in V2–V28, so some internal composition assumptions could not be removed. **Erdős #287, explicit M₀ and the finite splice all remain OPEN.**

**Why it stopped at §4.** No V2–V28 declaration builds a clean state from a physical source.
- The Kloosterman data carries only real parameters and an arbitrary kernel. It has no fields for q₀, D, r₁, r₂, n₁, n₂, so the gcd conditions cannot even be stated on it.
- `DIClass` is a free, undefined parameter: the DI provider holds vacuously for the empty class and fails for the full class (`DIClass_underdetermined`).
- The §4 arithmetic conditions on their own also make it fail (`arithOnlyClass_provider_false`), so DIClass could not simply be replaced by those conditions.
- **Earliest remaining hole:** the membership `DIClass s.DD.KD` for the clean states of the nonzero branch.
- **First same-source mismatch:** the branch functionals `D0, D1, D2, Db, DEnz` are free parameters, not defined from the physical pair. `same_source_not_established` proves that zero functionals with an empty DI class satisfy every branch field, the DI field and the nonzero realization, so those fields constrain nothing.

**What still could not be derived**
- **Kernel (§5):** no physical smooth cutoff exists. `kernel_is_load_bearing` shows two forms with identical numeric data but opposite DI verdicts, so the kernel cannot be skipped. Building it would mean inventing the DI kernel formula, which §24 forbids.
- **Pruning (§6):** `NonzeroPruningContract` is **not** retired. The seven-sector shape and the step from an exact sector decomposition to the contract are proved (`nonzero_pruning_from_sector_decomposition`). The decomposition itself has nothing to be derived from, because R_nonzero is not defined physically.

**What did go through**
- **Provider split (§12):** `MinimalExternalAnalyticProviders` contains only analytic fields: rosser, tuple, euler, hat, di, the four branch class bounds, and s1.
  - The two internal fields that could not be removed (actual-measure `tensor` and `nonzero` realization) are isolated in one labelled structure, `InternalGlueOwner`.
  - `old_FinalAnalyticProviders_of_minimal` rebuilds the V28 bundle from the minimal bundle plus the certificate plus the glue, in the direction you asked.
  - A degenerate rebuild with all branch functionals zero also typechecks, but only with a tensor provider that drops the remainder, which is stronger than any external theorem. It is recorded as a warning and not used.
- **Same weight and same normalization (§8–9, §16–17):** both chains are proved with exact equalities. One `LambdaNewPlus` is used in every slot, and one N serves S0, S1, the principal term, the pair baseline and the consumer.
- **Quantifier order (§18):** S and τ are chosen after η and before M, and appear in the conclusion; ρ is a fixed constant.
- **Certificate (§10):** no certificate data exists anywhere in the repository. The bounds μ_F > 7147687/10000 and W_F < 98278402/10000 are isolated as `FunctionalKernelCertificate`, labelled FINITE CERTIFIED INPUT. The exponent −1079/1900 also has no derivation in the repository.
- **Score formula (§11): mismatch.** The consumer uses μ_lo − (A_C W_hi + 27/5)/99 − 350 = 12093752057/12285000000, without your −1/20. Your formula equals that minus 1/20, which is 11479502057/12285000000 > 0. It implies the consumer's check but is not the quantity consumed.
- **Full pair composition (§14):** `full_pair_composition` composes every stage in one proof.
- **Final theorem (§19):** `pre_effectivity_287_FINAL_BANK` has type minimal bundle → certificate → `InternalGlueOwner` → sieve geometry and cell data → Li ≥ 0 → φ(W) > 0 → ∃ M₀, ∀ M ≥ M₀, no counterexample. It is conditional, and its type shows that it still depends on the internal glue.
- **Trusted challenge (§21):** the file states the closed proposition and discharges it.

**Files:** everything is new; `git diff` against the base commit shows 28 added files and nothing modified.
- V29: `ResearchBankV29.lean` plus the 13 requested files.
- V30: `ResearchBankV30.lean` plus the 9 requested files.
- Reports: `PROVIDER_CLASSIFICATION.md`, `FINAL_EXTERNAL_PROVIDER_MAP.md`, `ERDOS287_RESEARCH_BANK_V29_REPORT.md`, `ERDOS287_RESEARCH_BANK_V30_REPORT.md`.

**Checks**
- **Builds:** `lake build` succeeds for V29 (8307 jobs), for V30 (8315 jobs) and for the full project (8907 jobs), with no warnings in the new files.
- **Axioms:** `#print axioms` on all 51 audited declarations shows only propext, Classical.choice and Quot.sound, or no axioms at all.
- **Forbidden tokens:** a scan of the new code finds no sorry, admit, axiom, native_decide, bv_decide, unsafe, implemented_by, opaque, skipKernelTC or trustCompiler.
- **External checker:** `lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV30` exited 0 after about 57 minutes; this covers V29 through the import.
- **Comparator:** not installed (`lake comparator` is an unknown command), so it was not run.

The Properties table is updated with these results.

# Summary of changes for run 55b77848-f5b5-49dc-a83b-109d40508609
I added Research Banks V25–V28 as append-only work. Erdős #287 is still **OPEN**. The strongest result is a conditional theorem: it asserts that some M₀ exists, gives no explicit M₀, and does no finite splice.

**Append-only check.** Against the base commit `a08308e`, `git diff --name-status` shows 48 files, all added and none modified. V2–V24, every earlier report and `ARISTOTLE_SUMMARY.md` are untouched. The added files are the four aggregators `RequestProject/Erdos287/ResearchBankV25.lean`…`V28.lean`, every per-version file in your layout (each version has an `AxiomAudit.lean`), and `ERDOS287_RESEARCH_BANK_V25..V28_REPORT.md`. The new files use ordinary (non-`module`) headers, like V2–V24.

**What is proved outright (LEAN BANK)** — 220 theorems in total (V25: 58, V26: 57, V27: 76, V28: 29):
- **Centering:** `full_centering_fixed_modulus_exact` holds for every integer v. The unit hypotheses on c and a turned out to be unnecessary, so they are not assumed. A regression shows that deleting the correction term is false.
- **Residue energy:** the conditioned-energy Pythagoras identity and contraction (arbitrary complex masses, overlapping moduli), plus the coprime and divisor-weighted reindexing inequalities.
- **Affine clearing and counterfixtures:** good-modulus clearing with the V16 divisibility relations, and both historical counterexamples (mod-3 constant sequence; A_i=2, A_j=3, t=8).
- **Source identities (V26):** the rough-convolution identities, the Heath-Brown identity and its k=3 case, the rectangular interior boxes, and the Type II / one-large / two-large trichotomy with source-level coverage.
- **Decorated reduction (V27):** Cauchy direction (with a regression showing the reverse fails), grouped coefficient `bPsi`, the representation combinatorics, finite-label energy (`label_energy_le`, √L cost), the character-free orbit count `orbit_card` = φ(E_D), reciprocity algebra, the exact 1/d factor, and the savings 347/418000 and 347/836000.
- **Parameters and firewalls (V28):** all exact parameter arithmetic, the effectivity firewall and the ten overclaim firewalls.

**What is conditional (LEAN CONDITIONAL)**
- `decorated_conservative_linear`: |W| ≤ √3·N_q·x^{−η}. It depends on the DI provider and a representation-moment provider.
- `colour_sqrt_phi_bound`, and the clean-nonzero bound `clean_nonzero_derived`, which is now proved as a theorem rather than assumed.
- `routeC_pair_baseline_after_full_repair`: gives P_actual/N ≤ A_C·W_F + 27/5 + o(1) at err = −423/5.
- `pre_effectivity_asymptotic_287_after_full_repair`: the analytic bundle `FinalAnalyticProviders` implies ∃ M₀ beyond which there is no counterexample.

**Monolithic provider retired.** The final theorem no longer assumes the old V16/V24 source-class provider. `derived_source_class_provider` builds it from four branch class bounds (zero-frequency/BDH, one-large, two-large, product boundary). The bundle contains only analytic inputs; none of the algebraic, finite or parameter results are fields.

**Caveats you should know about**
- **The DI provider had to be restricted.** Stated over all admissible Kloosterman data, it is provably false: `unrestricted_provider_false` builds a degenerate admissible form with Ξ = 0 that violates it. So `DISpectralProvider η DIClass` covers only a class of genuine DI forms, and each clean form used must be certified to belong to it.
- **The composition works at the level of branch bounds.** The V25/V26 identities are proved separately; their role in deriving those branch bounds is documented, not composed in Lean.
- **The pruning identity is a named hypothesis.** R_nonzero = P_clean + errors was not found as a theorem in the frozen banks, so it is carried as `NonzeroPruningContract`.
- **Kernel construction is not formalized.** Building each clean state's kernel from the physical smooth cutoff is part of the per-instance "clean realization" hypothesis.
- **Supplied constants.** −1079/1900 and 8746001/25000000 are recorded as given; only their arithmetic is checked, not their derivation.
- **Score margin formula.** I reconstructed it as μ_lo − (A_C·W_hi + 27/5)/99 − 350 − 1/20 so that it equals the supplied value exactly. Please confirm this is the formula you intended.
- **Certified inputs.** The bounds μ_F > 7147687/10000 and W_F < 98278402/10000 do not appear in V2–V24; they enter as certified inputs.

**Checks run**
- **Builds:** `lake build` succeeds for each of V25–V28, including every `AxiomAudit`, and the full project build succeeds (8883 jobs).
- **Axioms:** `#print axioms` on all 220 theorems shows only subsets of {propext, Classical.choice, Quot.sound}.
- **Forbidden tokens:** a scan for sorry, admit, axiom declarations, native_decide, bv_decide, unsafe, implemented_by, opaque, skipKernelTC and trustCompiler finds nothing.
- **External checker:** `leanchecker` is installed; lean4checker is not. `lake env leanchecker --fresh` exits 0 on V25, V26, V27 and V28.
- **Comparator:** not installed, so it was not run.

The Properties table is updated with the main results and definitions. Full per-file contents, trust details and the git audit are in the four report files.

# Summary of changes for run 32abe5c1-3655-454b-87ba-b35ae54688f2
Research Banks V21–V24 are added, and everything builds without `sorry`. **Erdős #287 is still open.** The asymptotic result is conditional only: it holds under explicit analytic assumptions, which are Lean structures ("providers") that are never constructed. There is no explicit M₀ and no finite splice.

**Append-only check.** Base commit is `ce8a536`. `git diff --name-status ce8a536 HEAD` shows 45 files, all added: 37 module files, 4 aggregators (`ResearchBankV21.lean`–`ResearchBankV24.lean`) and 4 reports (`ERDOS287_RESEARCH_BANK_V21..V24_REPORT.md`). No V2–V20 file, historical report or `ARISTOTLE_SUMMARY.md` was touched. The new files use ordinary (non-`module`) headers, like the V16–V20 files they import.

**Proved from definitions (LEAN BANK):**
- **V21**
  - The identity `C_λ(q) = Σ_S a_λ(S) ∏ q/(1−q)` and monotonicity `normCost_mono`. It needs only the divisor sums to be ≥ 0; the individual coefficients may be negative.
  - The spectator local law, the envelope `h(p)=1/(p−K+1)`, and `quadratic_domination` for an arbitrary complex `B`.
  - The mod-11 counterfixture `spectator_square_density_not_invariant` (4/37 ≠ 1/10). The old V17 inference is recorded as REPAIRED/RETIRED.
- **V22**
  - The weight `LambdaNewPlus` = μ_E ⋆ β_sm⁺ ⋆ ℓ_rd is an actual definition. The small-prime Rosser weight is built directly, so it needs no provider.
  - First-forbidden-prefix positivity (`dsum_ellRd_ge`) and the factorised divisor sum S_Λ ≥ 1(survivor).
  - `exact_colouring_identity` with π⁻¹ ≤ 3^R, and the first-bin factorisation.
  - The literal convolution has multiplicity 2 at 143 (REPAIRED/RETIRED).
  - The four margins are positive. The formulas deriving them from ρ, σ, η were not supplied, so they are certified exactly as given.
- **V23**
  - `principal_prob` and its full-lcm form, `signed_expansion`, and `same_weight_principal_bound`.
  - The Euler factor equals the local signed-square average; `singular_cancellation` holds under explicit nonzero hypotheses.
  - `two_div_diff` = 1000/149057727 and `principal_slack` = 147807727/186322158750 > 0.
  - A firewall: the hat function is not differentiable, so it is not a smooth cutoff.
- **V24**
  - `rounded_completed_weight_matches_V16_contract`: the actual weight is an explicit combination of V16 bilinear source-class coefficients, with coefficient mass ≤ (R+1)^#cells·3^R.
  - For this I proved that rounded rough weights depend only on their cell counts (`ellRd_countDetermined`). The only remaining hypotheses are the atom bound R and the cell data.
  - Nine firewalls `fw1`–`fw9` and `v24_final_status`.

**Interfaces only (EXTERNAL PROVIDER, never constructed):** the Rosser scalar asymptotic, the prime-harmonic tuple rounding bound, `PrincipalEulerProvider`, the hat-reference approximation, the inherited V16 source-class provider, and a new `SameWeightActualMeasureProvider`. The last one plays the role that V20's pair-decomposition provider played, now for the new weight. The first five are bundled in `RepairedCompletedSieveProvider`; the zeta-pole field inside it is provable from Mathlib.

**Proved from the providers (LEAN CONDITIONAL):**
- `completed_cost_bound`
- `same_normalization_sifted_main`: its conclusion includes the frozen `S0Contract` for the same N.
- `principal_budget_conditional`: M_new ≤ (2/ϑ₀+1/5000)W_F+ε eventually, hence ≤ A_C W_F+ε.
- `repaired_routeC_baseline_of_providers`: gives the frozen V16 Route-C baseline, using the same weight for the principal term and the error term.
- `conditional_pair_baseline_after_repair`
- `conditional_asymptotic_287_after_positive_sieve_repair`: ∃M₀ ∀M≥M₀, no counterexample with maximum M.

**Still open:** explicit M₀, the finite splice, and global #287.

**Checks run:**
- `lake build` of each V21–V24 module, each `AxiomAudit`, and the full project all succeed.
- `#print axioms` covers 254 theorems (43/106/53/52); all use only propext, Classical.choice and Quot.sound, or a subset.
- The forbidden-token scan finds no `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `unsafe`, `implemented_by`, `opaque`, `skipKernelTC` or `trustCompiler` in code; the only hits are the word "axiom" in doc comments.
- `leanchecker` is installed and `lean4checker` is not. `lake env leanchecker --fresh` exited 0 for all four banks (about 36 min each).
- Comparator is not installed (`lake comparator` is an unknown command), and I did not emulate it.

Full details are in the four reports; the trust section is in the V24 report. The main results are in the Properties table.

# Summary of changes for run cdcae127-6142-4968-a332-a1c6fd3ebc7c
I added Research Banks V16–V20 without changing any existing file. Erdős #287 is **still OPEN**. The top-level result is only a **conditional asymptotic reduction**. `ActualCenteredSourceCompositionProvider` is defined but never constructed. An explicit M₀, the finite splice and the global problem all remain OPEN.

**Files (append-only).** Base commit `f0dc239`. `git diff --name-status f0dc239 HEAD` shows 62 lines, all `A`: nothing modified, deleted or renamed. V2–V15 and `ARISTOTLE_SUMMARY.md` are untouched. The new files are:
- `RequestProject/Erdos287/ResearchBankV16..V20/*.lean`, with every module you listed plus an `AxiomAudit.lean` per version.
- The aggregators `RequestProject/Erdos287/ResearchBankV16.lean` … `V20.lean`.
- `ERDOS287_RESEARCH_BANK_V16..V20_REPORT.md`.

The V20 report has the full file list and git audit. The files use ordinary (non-`module`) headers so they match the V2–V15 banks they import.

**What was proved (265 theorems: V16 86, V17 35, V18 55, V19 66, V20 23).**
- **V16:**
  - α(G(26,7)) = 7 by the general rotate-to-contain-0 / seven-point-arc argument, the 4-colouring, and "8 occupied groups ⟹ an edge" via a symbolic blow-up (no coordinates enumerated).
  - `50 − f(v) = (v−99)(v−100)/198`, with nonnegative weights an explicit hypothesis.
  - `c_C = 46/125 > 1/e` and `c_C·R_C < 1`; the Route-B constant 37/100 is shown to fail.
  - Relaxed budget `A_C W_F + 90 + err + o(1)`, with o(1) as explicit ε/eventual quantifiers.
  - `routeC_eventually_no_counterexample`, conditional on `RouteCBaselineProvider`.
- **V17:**
  - `log P = (L+2) log 2 + log 3`, plus the regression that `L log 2 + log 3 = log(3K) ≠ log P`.
  - Uniform thinning with the order δ → fixed tuple → x→∞, plus a countermodel to an x₀ uniform in δ.
  - Support comparisons with 4/7, 7/12, 3/5, and a firewall that a level below 3/5 builds no provider.
  - The thin consumer (conditional).
- **V18:**
  - Colour-conductor reduction with no assumption that c is a unit, and the E = 1 case.
  - Exact reciprocal-monomial separation valid for every m, so m never enters the cost.
  - `M_p³ ≤ p²`, and the principal Ramanujan sum.
  - Multiplier transfer and polarization constants 4 / 16 / 64.
  - The D^m residue-cell bound shown strictly weaker.
- **V19:**
  - Zero-frequency compatibility and the exact CRT count κ.
  - Coherent roots (same assignment in both copies), and the root-class Gram identity.
  - Prime-power / overlap CRT reduction and conductor divisibility for all positive D, s; nonunit reduction.
  - Periodic completion identity.
  - E2 outer / own-variable multiplier absorption.
  - Outer-cost ledger: a square root halves σ, the conservative exponent is ε/2 − δ(2+p), and the margins 17/40000 and 13/30000 are local only.
  - The structural taxonomy, `ActualBranchData`, and the provider.
- **V20:**
  - `thinPairBaseline_of_providers_CONDITIONAL`.
  - `conditional_asymptotic_287_CONDITIONAL`.
  - All eight required non-implications, each with a checked countermodel.
  - `v20_final_status`, which checks the final classification.

**Where the V19 audit rejected an earlier claim, it appears only as a counterexample:**
- Ω(0)=1 does not fix the main term.
- Independent-copy root assignments do not satisfy the zero-mode theorem.
- The conductor E is not the q-period V.
- Joint q/h dependence is not covered.
- σ is not preserved by the square root.
- A fixed J does not make the unweighted conductor sum polylogarithmic.

**External inputs are explicit providers only, never axioms:** `RouteCFunctionalCertificate`, `ThinFunctionalCertificate`, `FunctionalThinningProvider`, `PrimeDistributionProvider`, `GaussMagnitudeProvider`, the two Maynard exponential-sum providers, `CompleteKloostermanProvider`, `E1PeriodicProvider`, `PairDecompositionProvider`.

**Reconstructed values (no answer arrived to my question about them):**
- `R_C = ((19+2ξ)/(7−2ξ))·(10001/10000)²`.
- The audited μ_lo, W_hi and err are left as parameters.
- The thin support exponent is a parameter, instantiated at 273/500.
- The (ε, δ, p) triples are (1/1000, 1/40000, 1) and (1/1000, 1/40000, 2/3). They reproduce the stated margins but were not supplied.
- The SW firewall uses a toy mod-2 balance model.

**Checks.**
- **Build:** each V16–V20 target builds, including all axiom-audit modules, with no errors or warnings in the new files. Full `lake build` succeeded (8798 jobs).
- **Axioms:** `#print axioms` was run on all 265 theorems. They use only `propext`, `Classical.choice`, `Quot.sound` or a subset (230 / 13 / 6 / 16 no axioms).
- **Forbidden tokens:** none of sorry, admit, axiom, native_decide, bv_decide, unsafe, implemented_by, opaque, skipKernelTC or trustCompiler occurs in the new code.
- **External checker:** the installed checker is `leanchecker` (`lean4checker` is not installed and was not used). `lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV{16..20}` exited 0 for all five modules, each taking about 2400 s.
- **Comparator:** `lake comparator` is not installed (unknown command), so it was not run and nothing was emulated in its place.

The main theorems are recorded in the Properties table, and the composition provider is listed there as a definition that is never constructed.

# Summary of changes for run 2e78fde4-5bcb-4e54-9f39-cc8c08adbef3
I added Research Bank V14 and V15 as new files only. The full `lake build` succeeds, and there is no `sorry`, custom axiom, `native_decide` or `unsafe` anywhere in V14/V15. **Erdős #287 is still OPEN.** The one-lemma reduction is conditional: the pair provider it depends on (`ActualWeightedColouredPairProvider`) is defined but never constructed.

**What changed:** against the pre-V14 commit `7b0e706`, 34 files were added and none modified. V2–V13 and `ARISTOTLE_SUMMARY.md` are untouched. No existing aggregator needed an import line, because the library glob already includes the new modules.
- V14: `RequestProject/Erdos287/ResearchBankV14.lean` plus 14 files in `ResearchBankV14/` (BalancedKernelParameters, MacroGraph11, BalancedBlowup, EdgeOnlyCompilerInterface, CompilerApplication, ContactAnnulus, UsefulPairIdentity, ScoreCombinatorics, RowRigidity, HarmonicTail, ConditionalAsymptoticImplication, EffectivityFirewall, Ledger, AxiomAudit).
- V15: `ResearchBankV15.lean` plus 16 files in `ResearchBankV15/` (FixedAffineSource, DerivativeKernel, MobiusCoefficients, CompleteLCMModulus, CRTResidues, CollisionLocalFactors, DivisorMultiplicity, Normalization, BombieriVinogradovProvider, ZerothMomentContract, FirstMomentContract, PairProvider, OneLemmaReduction, ScopeFirewalls, Ledger, AxiomAudit). You didn't list a separate file for the divisor-multiplicity item (B8), so I gave it its own `DivisorMultiplicity.lean`.
- Reports: `ERDOS287_RESEARCH_BANK_V14_REPORT.md` and `ERDOS287_RESEARCH_BANK_V15_REPORT.md`, which list every theorem by name.

**V14 results (all proved):**
- **Score margins:** `margin_gt` and `remaining_margin_gt` give the margins > 163216957/2995000000 and > 13466957/2995000000. The functional bounds are fields of a separate structure and are not identified with the arithmetic moments.
- **Macro graph:** `alpha_eq_three` proves α(G(11,2)) = 3; the 4-colouring {0,1,2},{3,4,5},{6,7,8},{9,10} is proved proper, and four occupied cells force an edge.
- **Blow-up:** the balanced blow-up is symbolic, with no enumeration of vertices.
- **Compiler (please note):** the repository had no proved edge-only compiler theorem to reuse. It had only a general CRT lemma and an interface with no proof. So I proved `edgeOnly_compiler` in V14 from that CRT lemma, for any finite graph and any rational boxes, and then applied it to the blow-up (`compiler_exists`). It gives existence only; the useful height bound stays OPEN.
- **Contact annulus:** `Rstar_chain` proves R* = 401802401/149000000 < 100/37 < 685/252 < e, using Mathlib's certified bound on e; with c = 37/100, c > 1/e and c·R* < 1.
- **Useful identity:** `useful_identity_oriented` is the oriented +1 form; without orientation only ±1 is proved, and a regression fixture refutes the signless version.
- **Scores, rigidity, harmonic tail:** the score lemmas use nonnegative weights only; `row_rigidity` includes the denominator-clearing argument; `two_hole_contradiction_c` is the harmonic two-hole contradiction.
- **Conditional implication:** `eventually_no_counterexample` concludes ∃ M₀, ∀ M ≥ M₀ (every sufficiently large M).
- **Effectivity firewall:** no height bound, no explicit analytic threshold, finite splice not closed, and the 10^500 payload is still marked not supplied.

**V15 results:**
- **Proved:** the fixed source is the single V14 tuple. The Möbius coefficients allow shared primes. The modulus is the full lcm (shared primes counted once), and the first-moment modulus is `a_i·W0·q`, not q. The CRT residue is shown to move with the tuple. The collision local factors, the finite divisor-multiplicity grouping, and N_X = C_X·S_W0(a)·I are formalized, with a regression showing that omitting I breaks scale invariance.
- **Conditional moment theorems:** `s0_contract` and `s1_contract` are stated in ε/eventual form, since the project has no o(1) framework. The square expansion and the periodic counting with period `W0·q` are proved exactly. `s1_contract` takes the Bombieri–Vinogradov provider as an explicit argument.
- **Explicit providers, none constructed:** `OrdinaryBVProvider`, the derivative-kernel provider (G vs F), and the S0/S1 main-term, divisor-moment and BV-transfer providers.
- **Reduction:** `one_lemma_reduction` proves that the BV provider plus the standard providers plus the pair provider give the #287 conclusion for every sufficiently large M. `open_content_concentrated` states that the pair provider is the only remaining new input. This does not mean the provider is known or follows from Pascadi.
- **Pascadi firewall:** `exponent_fact_does_not_construct_provider` shows that "0.624 < 5/8" does not imply the provider for every source.
- **Ledger:** `v15_final_status` matches your section D.

**Checks:**
- **Builds:** the narrow V14 and V15 builds and the full `lake build` (8741 jobs) all succeed.
- **Axioms:** `#print axioms` was run on 119 V14 theorems and 83 V15 theorems; only `propext`, `Classical.choice` and `Quot.sound` appear.
- **Forbidden tokens:** the scan found them only in English doc comments and the `#print axioms` lines.
- **External checker:** the installed checker is `leanchecker` (`/root/.elan/bin/leanchecker`), not lean4checker; lean4checker was not run. `lake env leanchecker --fresh` exited 0 on both the V14 and V15 modules.

No stated theorem turned out to be false.

# Summary of changes for run 52c86b6c-ff5e-4e32-a09a-8a75694b87bd
I added V12 and V13 as new layers only. `git diff --name-status` against the pre-V12 commit lists 30 files, all added. No V2–V11 file and no `ARISTOTLE_SUMMARY.md` was changed. Erdős #287 is still OPEN.

**Files added**
- `RequestProject/Erdos287/ResearchBankV12.lean` and `ResearchBankV12/{ConcreteParameters, EndpointCounterfixture, CompatibleCellsConcrete, RestoredTypeIIEnvelope, TypeIIWholeRectangle, HBSelectionConcrete, HBCaseI, HBCaseII, HBCaseIII, HBFullSupportConcrete, RoughSeedConcrete, ConcreteAsymptoticGate, Ledger, AxiomAudit}.lean`
- `RequestProject/Erdos287/ResearchBankV13.lean` and `ResearchBankV13/{FiniteRepresentationModel, PrimeLayer, HarmonicTwoHole, AdjacentPrimeLayer, PrimeCertificates, FiniteIntervalCertificate, DemonstrationPayload, AuditedEndpoint, UpdatedSplice, EffectiveFrontier, Ledger, AxiomAudit}.lean`
- `ERDOS287_RESEARCH_BANK_V12_REPORT.md` and `ERDOS287_RESEARCH_BANK_V13_REPORT.md`. Both contain every required sentence word for word.

**Two supplied statements are false**
- **First false statement:** the Case-III bound g1 ≥ 4/13−μ+θ0/2+(337/2)ζ does not hold on the whole Type-II window r+s ≥ d*−ζ. At μ=3/10, θ=θ0, ν=1/10, r=r*(ν), s=B−ζ−r* the box is legal and g1 = 4/13−μ+θ0/2+168ζ, which is ζ/2 too small (`g1_337_fails_on_full_window`).
- The same bound also fails in the d*=λ branch, at μ=4/13−θ0/2, θ=θ0, ν=1−3μ (top corner) (`g1_337_fails_in_lam_branch`).
- What is proved instead: the (337/2)ζ bound on r+s ≥ B, the sharp 168ζ bound on the whole window, and g1 > 0 on the whole window. Routing only needs g1 > 0, so the routing theorem is unaffected.

**Two items were not reconstructed** because their formulas were not in the material you supplied: the Case-III reserve G5 ≥ 19ζ (a weaker ≥ 9ζ reserve is proved instead), and the five domain margins of the frozen Type-I theorem. The Case-I reserve μ−3θ−s ≥ ζ and your rapid-decay margin μ−θ−r−s ≥ ζ are proved.

**Main V12 theorems (proved)**
- Parameters and gates: `theta0_lt`, `loss_eq`, `loss_lt`, `vartheta_gt`, `pair_gap`, `exact_gate`.
- `endpointOnlyHBArgument_false`: the endpoint-only HB argument is refuted by your fixture point.
- `detectorClasses_card`: exactly d compatible α classes, not |k|d, with fixtures where |k| > 1.
- Type-II envelope: `restoredTypeII_of_provider`, `prefactor_comparison`, `lowH_cheaper`, `diagonal_cheaper`. The spectral estimate is an explicit hypothesis and no instance of it is created.
- `concrete_selection`: the three-way HB selection is derived from the factor data, not assumed. The one classification hypothesis it needs is the Möbius-exponent bound ≤ 1/4; `mobius_label_is_minimal` shows it cannot be dropped.
- Case II: `g1_lower`, `g2_lower`, `g3_lower` hold over the whole rectangle, not just at corners; `worst_case_margins` gives 1/208, 9/208−θ0 and 7/208.
- Case I and III: `caseI_routed`, `rapidDecay_declared_margin`, `overlap`, `g1_pos_on_typeII_window`.
- `every_actual_HB_box_routed`: every support box falls into small-BV, Type I or Type II.
- Also: `wf_truncation_firewall`, `rho_z_identity`, `mu_rho_z_identity`, `mtSpecificAsymptotic_concrete` (conditional on visible providers), `v12_preserves_v11_ledger`.

**Main V13 theorems (proved)**
- `primeLayer_exclusion`, with L/A values checked for J = 2, 5, 10.
- `eta_lt_exp` and `two_hole_exclusion`: two adjacent forbidden integers exclude the interval.
- `familyA_interval`, `familyB_interval`, `familyB_outside_goodPrimeHalf`.
- Primality witnesses: `proth_sound`, `pocklington_sound`, and the matching checkers, with malformed witnesses rejected.
- Certificates: `FiniteIntervalCertificate.sound`, `checkChain_sound`, and `noncontiguous_rejected`.
- Splice: `finite_eventual_splice`, which closes exactly when M_an ≤ U+1; a U+2 fixture leaves one integer uncovered. Also `splice_closes_of_future_constants`.
- Status: `current_global_splice_blocked` (current_M_an = none; the reason is now that no explicit analytic threshold is available), `v13_preserves_v12_ledger`, and `all_regression_fixtures`, which bundles all ten regression fixtures.

**The 10^500 certificate was not replayed.** The audited 1,274-record payload is not in the workspace, so there is no `auditedFiniteEndpoint` and no Lean theorem about 10^500. The certificate format is proved sound in Lean; the actual payload is externally audited but not replayed by Lean. Separately, I generated a 117-record demonstration payload to test the checker end to end. The kernel checks it with ordinary `decide`, giving `demo_noCounterexampleUpTo` up to about 2.45·10^60. It is not the audited payload.

**Build and checks**
- `lake build` of V12 (plus its axiom audit): 8201 jobs, success.
- `lake build` of V13 (plus its axiom audit): 8223 jobs, success.
- Full `lake build`: 8709 jobs, exit 0. All 26 warnings are in older files; none are in V12 or V13.
- `#print axioms` on all 126 V12 and 92 V13 theorems reports only propext, Classical.choice and Quot.sound, or fewer.
- No `sorry`, `admit`, custom axiom, `unsafe`, `native_decide`, `bv_decide`, `opaque`, `implemented_by` or `skipKernelTC` in the new files; these words appear only in comments.
- `leanchecker` on V12: exit 0, no output. On V13: exit 0, no output. `leanchecker --fresh` on V13: exit 0, no output, 34 minutes.

# Summary of changes for run ea40301d-ba07-4aa7-9244-179850e8a2eb
I've added V10 and V11 to the Erdős #287 research bank. Everything builds, no placeholders or custom axioms remain, and the bank still records **#287 as OPEN**. One caveat: some of the Type-II/HB formulas you referred to weren't in your prompt, so those checks are stated in terms of parameters rather than your exact numbers (details under "Not supplied" below).

**Files: all new, nothing existing was edited.** `git diff --name-status` against the starting commit shows only added files. V2–V9 and `ARISTOTLE_SUMMARY.md` are untouched.
- `RequestProject/Erdos287/ResearchBankV10.lean`, plus these files in `ResearchBankV10/`: `FrozenFrontier`, `TypeIRescaling`, `TypeIRoughness`, `TypeIGroupedCoefficient`, `TypeIProvider`, `TypeIICompatibleCells`, `TypeIICoefficient`, `TypeIIHighLow`, `HBSelection`, `HBSupportCoverage`, `EndpointCounterfixture`, `WellFactorableCutoff`, `RoughSeedIdentities`, `Providers`, `AsymptoticComposition`, `ExponentGate`, `Ledger`, `AxiomAudit`.
- `RequestProject/Erdos287/ResearchBankV11.lean`, plus these files in `ResearchBankV11/`: `EffectiveConstants`, `PowerToLog`, `ExceptionalFactor`, `AnalyticActivation`, `FiniteArchitectureFrontier`, `EffectiveSplice`, `Ledger`, `AxiomAudit`.
- `ERDOS287_RESEARCH_BANK_V10_REPORT.md` and `ERDOS287_RESEARCH_BANK_V11_REPORT.md`. Both contain all the sentences you required verbatim, plus a per-theorem check of what each statement does and does not prove.
- The new files don't start with `module`, because Lean won't let a `module` file import the existing V9 files.

**Main theorems (all proved, 215 in total):**
- **V10:**
  - `v10_preserves_v9_ledger`
  - Type-I e-rescaling: support, divisor bound, bijection, `m₀n = uv`, reference term, density; `density_diagnostic_2_5_1` confirms the 1/10 vs 1/5 example.
  - Bonferroni lower/upper bounds, the shell identity, `e ≤ z₀^J`, and the symmetric-sum bound.
  - A type-level check that a coefficient depending on spectral variables fails the grouped-coefficient interface.
  - `compatibleAlpha_card_eq_d`, with fixtures where the old |k|d count fails.
  - The Type-II index-map factorisation.
  - The high/low-H cost identity `= H/(C²Q²) < 1`, and `smaller_norm_insufficient`.
  - `endpointCornerChecks_do_not_cover_support`.
  - The HB three-case selection, proved from the factor-list hypotheses.
  - The vertex argument, the d* overlap, and the routing theorem `every_box_routed`.
  - `wf_truncation_not_automatic`.
  - Both rough-seed convolution identities.
  - `mtSpecificAsymptotic_of_repairedProviders`.
  - The exact rational gates: θ₀ < 1/1000, 3θ₀+ε₀ < 1/1885, vartheta > 78/145, and 145/39 − 2/vartheta = 52426455/18953756081 > 0.
  - Ledger checks that nothing is reclassified and no path closes #287.
- **V11:**
  - `power_to_log`.
  - `analyticActivation_sufficient`: once numerical constants are supplied, the computed threshold is enough.
  - `current_M_an_eq_none`.
  - `asymptotic_does_not_imply_effective`.
  - `W_shortcut_invalid`: putting the exceptional prime into W doesn't make the full modulus safe.
  - `eventual_exclusion_of_architecture` and `killed_architecture_no_provider`.
  - `effectiveSplice_sound`: a complete splice input would close #287; no such input exists in the bank.
  - `splice_blocked_of_M_an_none`, `splice_blocked_of_no_architecture`, `current_effective_splice_blocked`.
  - `asymptotic_does_not_imply_closed` and `asymptotic_does_not_imply_finitePrimeSupply`.
  - Fixtures 7 and 8: `fixture_asymptotic_vs_effective`, `fixture_analytic_vs_finite`.
  - `v11_preserves_v10_ledger`, `v11_frontier`, `no_ledger_path_closes_erdos287_v11`.

**Build:**
- `lake build RequestProject.Erdos287.ResearchBankV10`: success, 8177 jobs.
- `lake build RequestProject.Erdos287.ResearchBankV11`: success, 8186 jobs.
- Full `lake build`: success, 8681 jobs. There are 26 warnings, all in files that already existed; none in V10/V11.

**Placeholders and axioms:**
- Across all 215 new theorems, the only axioms used are `propext`, `Classical.choice` and `Quot.sound`.
- The forbidden words (`sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `bv_decide`, `opaque`, `implemented_by`, `debug.skipKernelTC`) appear only in comments and in the `#print axioms` lines.
- The only automation is ordinary kernel `decide` on fixed finite lists.

**Independent re-check:** Lean 4.28 includes the checker as `leanchecker`, the successor to `lean4checker`.
- `lake env leanchecker RequestProject.Erdos287.ResearchBankV10`: exit 0, no output.
- `lake env leanchecker RequestProject.Erdos287.ResearchBankV11`: exit 0, no output.
- `lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV11`: exit 0, no output. This re-checks V10 too, since V11 imports it.

**Status:** asymptotic composition is conditional on the visible provider hypotheses; M_an is NONE; finite architecture is OPEN; the finite splice is BLOCKED; Erdős #287 is OPEN. No statement fails, so there's no counterexample to report. The analytic inputs are hypothesis structures that nothing in the bank constructs; they're only satisfied in zero-error test models.

**Not supplied:** I asked you for these and got no answer. The specific Type-II gap formulas (the ones with values 1/208, 9/208−θ₀, 7/208, the g1 bound and G5 ≥ 19ζ), the old margin formula, and the internal (r,s) point weren't in your prompt. So those parts are proved for general parameters, the gap formulas are taken as explicit inputs, and the reports label them as not reconstructed. I didn't make up any formulas. If you paste them, they can be plugged in.

Five of these theorems are also listed in the properties table as proved.

# Summary of changes for run 2cf0c343-890f-4616-885d-d098721d7f26
I added two new append-only layers, V8 and V9, plus the two reports. Everything builds without `sorry`, and Erdős #287 remains OPEN: this research bank does not prove or disprove it.

**Files added (no existing file changed):**
- V8: `RequestProject/Erdos287/ResearchBankV8.lean` and `ResearchBankV8/{Saturation, RoughWindow, WeakCutoffSeed, ExactEntrySystem, ActiveResidueDP, TernaryBlocker, RigidK2, GoodM, CertificateInterval, VirtualEdge, WholeParentCap, Ledger, AxiomAudit}.lean`
- V9: `RequestProject/Erdos287/ResearchBankV9.lean` and `ResearchBankV9/{GcdClique, AffineContact, CircularGraph, Occupancy, Gates, GraphLocalization, ArchitectureLimit, AsraCRT, AsraPrimeSlot, AsraZeroMode, AsraClearing, AsraInterfaces, Splice, Ledger, AxiomAudit}.lean`
- Reports: `ERDOS287_RESEARCH_BANK_V8_REPORT.md`, `ERDOS287_RESEARCH_BANK_V9_REPORT.md`

A git diff against the initial commit shows only added files. V2–V7 and `ARISTOTLE_SUMMARY.md` are unchanged, and the V7 ledger is carried into V8 word for word, with a proof that every V7 classification is preserved. All new names live under `Erdos287.ResearchBankV8.*` and `Erdos287.ResearchBankV9.*`, so nothing collides with older layers.

**Build and audit:**
- `lake build` succeeds for the V8 target (8142 jobs), the V9 target (8158 jobs) and the whole project (8653 jobs), with no errors and no warnings in the new files.
- `#print axioms` was run on all 135 V8 and 114 V9 theorems. Each uses only some of `propext`, `Classical.choice`, `Quot.sound`, or none. There is no `sorryAx`, no native-evaluation axiom and no custom axiom.
- A scan for `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `bv_decide`, `opaque` and `implemented_by` finds them only in the `#print axioms` lines and in comments saying they aren't used. Plain `decide` is used only on fixed finite data.

**Main results proved with no analytic assumptions:**
- Canonical saturation (`saturate_*`).
- Rough-multiplier uniqueness, with a counterexample showing rough labels need not be pairwise coprime, plus LCM gluing and the gcd endpoint-loss count.
- The weak-cutoff seed family (`weak_cutoff_entry_existence`), including that P±1 are not prime powers, with the firewall `weak_cutoff_does_not_transfer`.
- The exact entry system (`pLocal_entry_iff_row_congruence`), with counterfixtures showing the top digit alone is not enough.
- Active-residue DP exactness, the rule for when an owner can be forgotten, "resource exhaustion ≠ UNSAT", and a counterexample showing the boundary bit alone does not determine feasibility.
- The ternary blocker truth table and the rigid K2 core (joint UNSAT, each row alone compatible, unique contact, and a proof that κ=0 does not refute the κ≥1 theorem).
- GOOD-M counting, the certificate interval (`certInterval_eq_iff`), and the virtual-edge firewall.
- V9: the gcd-clique CRT core (`gcdClique_of_compatible`), the affine contact identity, α(G(n,r)) = r+1 and fractional chromatic value n/(r+1), graph-selective occupancy (`occupancy_forces_edge`, `occupancy_programme`), and the exact gates (13/4, 145/39, 26/7 < 145/39, 7/13 − 78/145 = 1/1885, the θ-gate equivalence, and 1/e < 39/106 from Mathlib's proved bound on e).
- Graph localization ⇒ no #287 representation (`no_erdos287Counterexample_of_usefulEdge`) and the architecture limit χ_f ≤ ρ+1.
- ASRA algebra: the CRT root bijection, the collision-zero statements, lcm-versus-product for the main modulus with the clean totient case, prime-slot truncation, the divisor decomposition into root classes, the zero-mode density and centred kernel, and bilinear clearing with the base progression kept.
- The finite splice lemma, `EffectiveFiniteSplice ↔ no counterexample`, and the ledgers (`v9_no_closed`, `no_ledger_path_closes_erdos287`).

**Conditional results (assumptions visible in the theorem statement, never proved):**
- The old whole-parent cap is incompatible with the supplied counting input (`CapAnalyticInput`). This is recorded as a killed sufficient hypothesis, not as ENTRY being false.
- `RoughLabelSupply → LocalDeletionInput → SharedGridOutput`, and the K2 prime-supply interface.
- The Iwaniec–Maynard upper sieve, Shiu and Zheng ratio-BV inputs.
- `asra_of_components`, whose premises include the two OPEN interfaces `ASRA_NonzeroFrequencyTransfer` and `ASRA_SignedSieveMainTerm`, and ASRA ⇒ below the gate only when κ < 145/39 is supplied.
- `eventual_exclusion_conditional`.

ASRA and both open interfaces are shown not to hold automatically. The current state has `M_an = none`, so M₀ is unavailable and the effective finite splice is BLOCKED. The ≈6.125×10^120 endpoint is kept only as a text note.

**Limits (also listed in the reports):**
- Placing clique offsets inside the prescribed boxes (the union-bound argument) is not formalized; it is OPEN in the ledger.
- The p=107 phenomenon is an abstract truth table, not the actual numerical data.
- Killed or superseded routes (raw sparse-owner SAT, three-group A<3, arbitrary-F A≥3, Chen tuning) are ledger entries only.
- ASRA is modelled over an abstract data record in ε–X₀ little-o form, not with the concrete Maynard weights.
- The finite thresholds M_geom, M_int, M_rig are stored as 0 because no values are available.
- The mixed zero-mode densities are not stated as separate theorems.

Both reports include the 11 required items and a short machine-readable ledger, and I added the main V8/V9 results to the Properties table.

# Summary of changes for run b7a9c145-c592-4484-a585-1547eddfd870
Added a strictly append-only layer `RequestProject/Erdos287/ResearchBankV7/` with aggregator `RequestProject/Erdos287/ResearchBankV7.lean`, plus a report `ERDOS287_RESEARCH_BANK_V7_REPORT.md`. Nothing in the AnchoredV2/V3/V4, ResearchBankV5 or ResearchBankV6 layers was edited, renamed, moved or reinterpreted — V7 only imports, re-exports and audits them. Erdős #287 remains OPEN; no proof, counterexample or global closure is claimed.

Banked, at its true evidence level: (1) research epochs with machine-checked meta-firewalls (superseded ≠ false; a historical owner being open does not fix the current owner; a later reduction does not retroactively inhabit an earlier open proposition; no closure status propagates along ledger edges). (2) Bounded adaptive absorption, proved: guarded charging `(1−3γ)|W| ≤ 2z₀+g₀`, unguarded `(1−3γ)|W| ≤ 2|Z₀|`, and at γ=1/8 the budgets `|W| ≤ 16/5 z₀ + 8/5 g₀`, `|U| ≤ 2/5 z₀ + 1/5 g₀` (guard-free `16/5|Z₀|`, `2/5|Z₀|`), plus the branching-bit budget; no asymptotic existence of row completions is encoded. (3) Exact mixed-modulus interval lifting, proved with actual Boolean subsets, non-coprime and repeated prime-power directions, the overlap-inequality non-vacuity lemma, and the exact recursion for successive lifts with support and mass bookkeeping. (4) Arithmetic-spine extraction from a supplied certificate, proved: interval inclusion, retention of starters and residue buffers, explicit support/mass bounds, with a firewall that no source is claimed to possess such a certificate. (5) ERASURE-HIT, proved: erasure of non-spine coordinates, arbitrary fixed part, and the two-sided complement form giving `[α, Σ1/n − α]` under the stated exact overlap condition, plus its rational form; lifting failure is explicitly not called UNSAT. (6) Guarded branch-to-HIT, proved from its hypothesis package: the actual deficit `w = J(S(x₀)−1)`, taken from the complete reference-word mass (with a counterfixture forbidding seed-mass substitution), is hit by the spine, giving `S = 1` on the same branch while preserving guards, protected neutrals and the zero budget; firewalls show it neither produces an ENTRY word nor kills unguarded branches. (7) STABLE-ENTRY: forward direction proved by following the ENTRY word through the branching tree, reverse direction and the equivalence conditional on the external polylog simultaneous-completion interface, with firewalls that it is a feasibility reduction, not existence. (8) Fixed-polylog completion: finite second moment and disjoint buffer packing proved internally; Croot, PNT prime supply and Lovász-Local-Lemma whole-row completion left as explicit uninhabited external interfaces, so the completion law is classified conditional, never kernel. (9) Fouvry-pin localization: Fouvry/Luca–Young, Selberg, Brun–Titchmarsh and prime-counting kept external and uninhabited; pin-capture inequality conditional; the sublinear-support and branch-budget localization consequences proved; no terminal-leaf existence inferred. (10) Finite `p = 2q ± 1` source kills with five checked instances (59, 83, 107; 61, 73), a counterfixture showing the pattern is not universal, and the firewall that finite kills give no uniform supply. (11) Corrected metadata, kernel-verified without `native_decide`: `J = L₄₄₇` has 194 decimal digits and 644 bits, together with `2¹⁹⁴ < J`. (12) A semantic spot audit of the five load-bearing V6 theorems (lower endpoints and actual cofactor sets present, genuine Boolean selection, intended rational denominator reduction, no conclusion inserted as a premise) — all match, so they are re-exported unchanged and no correction theorem was needed. (13) Owners and DAG: `UpperGapCarryCompression` and `ExactMassIntersection` recorded as superseded/refined and never false, with their proved consequences re-exported; the current sole owner `EntryFirstTerminalLeafExistenceOrKill` and the node `genuine ENTRY reference word` left uninhabited, with firewalls against bypassing or weakening them; the epoch-aware ledger preserves every V6 classification verbatim and machine-checks that no row is CLOSED.

Build and audit: `lake build RequestProject.Erdos287.ResearchBankV7` succeeds and the full project builds. `#print axioms` on all principal V7 theorems reports only `propext`, `Classical.choice`, `Quot.sound` (several bookkeeping theorems use none). A token scan of the V7 layer finds no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `opaque` or `@[implemented_by]`; the only computations are ordinary kernel `decide` on explicit finite data, kept in separate declarations. Final verdict: V6 frozen; absorption, interval lifting, spine, ERASURE-HIT and guarded branch-to-HIT banked; polylog completion, STABLE-ENTRY equivalence and Fouvry localization conditional with dependencies explicit; finite source kills as diagnostics only; genuine ENTRY seed / surviving terminal leaf OPEN; Erdős #287 OPEN.

# Summary of changes for run 8d0d1118-6808-4ff9-b0ae-75d56ee46766
I added the new append-only layer `RequestProject/Erdos287/ResearchBankV6/` with aggregator `RequestProject/Erdos287/ResearchBankV6.lean`. Nothing in the AnchoredV2/V3/V4 or ResearchBankV5 layers was edited, renamed, moved or weakened — the only changes are new files (verified with git). Erdős #287 remains OPEN and is not claimed.

New exact, sorry-free kernel mathematics:
• Upper-gap cofactor–carry (`UpperGapCarry.lean`): `rowMass_eq_div` (`∑_j ε_{pj}/(pj) = T_p/(p·L_N)`), `den_dvd_iff`, the denominator-entry equivalence `prime_removed_iff_dvd_rowNumerator` (removal of `p` from the row denominator ⇔ `p ∣ T_p`), the carry identity `rowMass_eq_carry_div` (`= k_p/L_N`, `k_p = T_p/p`), and the same-height aggregation `carry_height_aggregation` (`∑_p ∑_j ε_{pj}/(pj) = ∑_N K_N/L_N`, `K_N = ∑_{⌊M/p⌋=N} k_p`), all over the actual allowed cofactor set with explicit finite ranges, lower endpoint, selection bits and denominator hypotheses. Two counterfixtures show the cofactor range may not be silently replaced by `1,…,N`.
• Support disjointness (`SupportDisjointness.lean`): `pq > M` ⇒ no shared physical denominator position, pairwise disjointness for prime rows above `√M`, plus the firewall that disjoint support does not give independent row choices.
• Contact relation `|pj − qℓ| = 1` (`UpperGapContact.lean`): symmetry, coprimality, distinct row primes, `≤ 2` contacts per position (shown sharp), the same for contacts with the frozen trace, and uniqueness of the partner cofactor for primes `≥ 3`; a firewall records that no stronger sparsity is asserted.
• Finite contact target (`ContactTarget.lean`): the charging inequality giving `H ≤ 2π(z) + 4⌊M/z²⌋`, the exact count of multiples of `z²`, and the exact balancing identity `M/z² = z/l` at `z³ = M·l`.
• FULL-FROZEN denominator entry (`FullFrozen.lean`): under the previously banked prime-power window exclusion, the denominator set is disjoint from the whole physical `p^e`-row.
• Firewalls: `den(S) ∣ J` is not closure (explicit witnesses for every `J ≥ 2`), the ledger is not a proof, and no route equivalence is asserted.

Correctly classified non-kernel items: the middle-band same-trace theorem is proved only as an implication from the uninhabited fixed-cardinality additive interface (Dias da Silva–Hamidoune type) and is labelled conditional, not kernel; the cube-root contact asymptotic and the prime-counting input are kept as separate uninhabited adapters consumed by a conditional theorem; `UpperGapCarryCompression` is introduced as four clearly labelled, quantitatively explicit uninhabited candidate interfaces; `ExactMassIntersection` is the uninhabited final owner. `Ledger.lean` records the acceptance verdicts (KERNEL-BANKED / CONDITIONAL-BANKED / COUNTERFIXTURE / OWNER-OPEN / CLOSED) on top of the imported status × evidence discipline, adds the third route beside the two V5 routes without collapsing them, enters closure-DAG edges only with Lean proofs, and machine-checks that no row is CLOSED and that #287 is OWNER-OPEN.

Build and audit: `lake build RequestProject.Erdos287.ResearchBankV6` succeeds; there is no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `opaque` or `@[implemented_by]` anywhere in the layer, and `#print axioms` on all 45 audited principal theorems reports only `propext`, `Classical.choice`, `Quot.sound` (several use fewer). Finite `decide` diagnostics are kept separate from the general theorems. A full write-up is in `ERDOS287_RESEARCH_BANK_V6_REPORT.md`.

# Summary of changes for run 1c702357-513a-410d-904d-2095e07c58b4
Banking / reconciliation run completed, strictly append-only: nothing in `RequestProject/Erdos287/AnchoredV2*`, `AnchoredV3*` or `AnchoredV4*` was edited, renamed, moved or weakened; the new work lives entirely in the new layer `RequestProject/Erdos287/ResearchBankV5/` with aggregator `RequestProject/Erdos287/ResearchBankV5.lean` (the project's library glob already covers it, so no older aggregator needed changing).

New route-aware master bank (12 modules, ~2100 lines). Meta layer (`Routes.lean`, `GateLedger.lean`, `AsymptoticInputs.lean`): the two distinct routes (`anchoredV4`, `contactCoreV5`), the two-dimensional status system (`ResearchStatus` × `EvidenceKind`) with the firewall theorems `externalBank_not_kernelProof`, `conditionalInterface_not_inhabited`, `open_not_closed`, `killed_not_false_target`, `superseded_not_false`, `open_status_does_not_propagate`, `no_closure_without_bridge`; route-indexed `currentOwner`/`routeOwners` with a machine-checked disjointness firewall; the frozen Anchored V4 snapshot (V2/V3 frozen, V4 banked, bridge proved, the three open owners preserved and uninhabited); the Gate A/B/C/D ledger exactly as specified (A local closed / global open, B generic families paid / exceptional open, C reduced / open, D closed, #287 open); separate closure DAGs for the two routes; and the no-fake-closure theorems `erdos287_not_marked_closed`, `no_closure_from_status`, `ledger_is_not_a_proof`, `gateD_closed_does_not_close_287`.

New kernel mathematics (all sorry-free): exact path transfer `D_j p_j = C_j p₀ − R_j` with the unrolled and normalized remainder formulas, plus the `53 — 317 — 79` depth-two counterfixture retiring the direct root-to-terminal splice; the complete proper-power row condition PP-ROW with a proof that it is strictly stronger than the naive unit-inverse congruence; exact valuation-layer counting (`D_v ≤ 2 n_v + 5`, sparse tail `D_v ≤ 6ℓ`, deficient layer `D_v ≤ 4ℓ`, the `4ℓ` raw forced-zero port cap, the heavy-layer majority charge); the valuation lift `q d = h d₀` and `⌊⌊M/q⌋/ℓ^v⌋ = ⌊M/h⌋`; the finite additive lemma that subset sums of any `ℓ−1` nonzero residues cover `𝔽_ℓ` (the digit step of PADIC-SAT, proved from scratch); the STRICT-HEIGHT contact theorem with its height form, impossibility of same-height first-power cycles, exhaustive finite regressions, and the mandatory firewall that strict per-edge change does not give global monotone descent; the primorial local-factor cancellation and the `20 → 19` no-fixed-ratio fixture; and the contact-core Gate D bridge back to the original reciprocal-gap formulation, kept separate from the re-exported Anchored V4 bridge (`RouteReconciliation.lean` contains only proved implications and asserts no route equivalence).

External analytic inputs (Croot general modulus, its prime-power corollary, VAL-TRANS, FP-INTERFACE-GEN, FP-INTERFACE) are named `Prop`s that are never inhabited; only their logical consequences are proved (full-cube removability/elimination, LINEAR-CHARGE), and `AsymptoticInputs.lean` records each with statement, source, consumption point, status, refereeing and formalization flags, with machine-checked facts that none is formalized or marked as a kernel proof. The global PADIC-SAT statement is likewise carried as an uninhabited `Prop`.

Audits and build: `AxiomAudit.lean` runs `#print axioms` on 86 principal new theorems — every dependency is a subset of `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`, custom or native axiom. A textual placeholder search of the new layer finds no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `opaque` or `implemented_by` syntax (only the English word "admit" and audit documentation). `lake build RequestProject.Erdos287.ResearchBankV5` succeeds (8097 jobs) and the whole-project `lake build` succeeds (8597 jobs, no errors; the 24 warnings all come from pre-existing untouched layers). Two documents were added: `ERDOS287_RESEARCH_BANK_V5_REPORT.md` (15 sections plus the verdict string and the mandatory firewall text) and `ERDOS287_RESEARCH_BANK_V5_NEXT_STATE.md` with the exact required status block. Erdős #287 remains OPEN; no open owner is inhabited, no route equivalence is asserted, and no route was collapsed into another.

# Summary of changes for run 2f6c2672-620b-4edd-99a3-b8d336d3e6f5
I built a new, strictly append-only Anchored V4 layer under `RequestProject/Erdos287/AnchoredV4/` with the aggregator `RequestProject/Erdos287/AnchoredV4.lean`, and added exactly one new import line to `RequestProject/Main.lean`. Anchored V2 and Anchored V3 were not edited in any way (verified with git): they are only imported and used.

New proved mathematics (no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `native_decide` or `@[implemented_by]` anywhere in the layer):
- Normalized prime-power height `normHeight` and the exact theorem `n ∣ 2·lcm(1,…,t) ↔ normHeight n ≤ t`, together with proofs that the factor 2 is essential (`32 ∣ 2·L(16)`, `32 ∤ L(16)`) and that the un-doubled variant is false.
- The doubled denominator lattice: `den(2q) ∣ P ↔ den q ∣ 2P`, its normalized-height form, and the finite regression certificate `1/1056 + 1/1080 = 89/47520` with `den(2Δ) ∣ L(30)` and `den(Δ) ∤ L(30)`.
- Complete finite `no-00` guard geometry (all-even omissions are guarded; restoring a position never creates an adjacency; fresh even centers with low-height neighbours preserve the guard) plus exact word-value bookkeeping.
- The exact `Entry` structure (every ENTRY condition an explicit proposition) with proved necessary conditions: every omitted position exceeds `Q`, and a guarded omission set has at most `(M−aM)/2` elements.
- Exact descent data and a genuine well-founded descent theorem to any floor height, preserving interval, guard, mask discipline, freshness (no denominator reused) and the doubled denominator condition.
- The absorber split into deterministic parts: reduction of exact absorption to an integer subset-sum, the no-wraparound upgrade from congruence to exact equality, the exact finite Fourier counting identity for reservoir subset sums, and exact absorption from spectral dominance — all analytic inputs remain visible hypotheses.
- The transition problem as an exact finite global congruence system (`descent_congruence_iff`), component splitting, a dual/divisor unsolvability certificate, and `descentStep_of_congruence`, which reduces the descent-supply owner to a subset-sum congruence over the guarded reservoir.
- Route results: global column surjectivity refuted in the general model (columns `{2,3}` mod 7), Route B put in its only exact form (coset meets subgroup iff the target lies in their sum), and firewalls against "positive mass ⇒ coverage" and "many targets ⇒ hit".
- Reconciliation with the frozen V3 bank (mobility states satisfy the V4 lattice condition; the V4 absorber has the V3 sumset shape; the V4 guard implies the V3 `No00` predicate), with V3 firewalls re-checked and not revived.
- A bridge theorem proving that any final V4 configuration (interval word, non-adjacent omissions, selected endpoints, reciprocal sum exactly 1) *is* an Erdős #287 counterexample in the original sense, plus its contrapositive reading.

Conditional interfaces are clearly labelled implications: `conditional_entry_to_exact_one` (ENTRY + descent supply + absorber supply ⟹ exact value 1) and `exact_absorption_of_fourier_dominance`. None of their premises is inhabited.

Erdős #287 remains OPEN: nothing was proved or refuted about the conjecture. Exactly three owners remain open and are recorded machine-readably in `AnchoredV4/OpenOwners.lean`: `ENTRY_EXISTENCE`, `SAFE_DESCENT_SUPPLY`, `GUARDED_ABSORBER_ANALYTIC_SUPPLY`; the bridge owner is discharged. `lake build` succeeds for all normal targets (8584 jobs); the axiom audit in `AnchoredV4/AxiomAudit.lean` reports only `propext`, `Classical.choice`, `Quot.sound` (or fewer) for every principal theorem; the placeholder search over the layer finds only doc-comment mentions. Reports are in `ERDOS287_ANCHORED_V4_ENTRY_EXACT_ENDGAME_REPORT.md` (files, imports, build, axiom and placeholder audits, theorem ledger, dependency DAG, killed shortcuts, ENTRY status, bridge) and `ERDOS287_ANCHORED_V4_NEXT_STATE.md` (frozen bank, new bank, dead routes, remaining owners, first next theorem).

Verdict — ERDOS #287 STATUS: OPEN; ANCHORED V2: FROZEN; ANCHORED V3: FROZEN; ANCHORED V4: BUILT; ENTRY EXISTENCE: OPEN; ENTRY → EXACT S=1: CONDITIONAL (on descent and absorber supplies); BRIDGE TO ORIGINAL ERDŐS #287: PROVED; FIRST REMAINING OWNER: existence of a guarded fresh even center set solving `(2L(h)/2L(h')) ∣ numeratorAt (2L h) S − ∑ weights` at every active height; MOST IMPORTANT NEW PAYMENT: `final_configuration_is_counterexample`; MOST IMPORTANT FIREWALL: the factor-of-two lattice regression; LAKE BUILD: PASS; PLACEHOLDER AUDIT: PASS; AXIOM AUDIT: standard Lean/mathlib axioms only.

# Summary of changes for run d0e089bb-0461-4157-abf5-38d53552fd4b
Added a strictly append-only Anchored V3 layer for the Erdős #287 research programme. Erdős #287 remains OPEN: nothing here proves, refutes or claims a counterexample, and the certified finite frontier (U2 still pending) is untouched. Anchored V2 is frozen — no V2 statement was edited, renamed, weakened or re-proved; the only change outside the new directory is one new import line in `RequestProject/Main.lean`.

New files: `RequestProject/Erdos287/AnchoredV3.lean` (aggregator) and, under `RequestProject/Erdos287/AnchoredV3/`, the modules `GlobalNeutrality`, `OldEmptyNewHit`, `ColumnZeroPatterns`, `GlobalColumnCompiler`, `ColumnPackets`, `SupportMultiplicity`, `ColumnLattice`, `TargetMobility`, `MobilityStructure`, `AlignmentPolynomial`, `FourierHitInterface`, `BaselineCentrality`, `ResonanceInterfaces`, `ConditionalClosure`, `OpenOwners`, `Reconciliation`, `AxiomAudit`.

Banked exactly (all proved, no placeholders): rowwise multiplier neutrality implies global neutrality, with an explicit finite witness showing the converse fails (`rowwise_sufficient_not_necessary`); the `D = D_core · U_mult` lcm decomposition under explicit coprimality; the exact old-empty / new-global-hit finite certificate on one fixed bank (`same_bank_old_empty_new_global_hit`, based on `74·5407 = 199777 + 200341`, giving `S₀ + 1/n₁ + 1/n₂ = 1` while every old rowwise-legal completion needs at least four terms and therefore overshoots); exact zero-pattern integer weights and the reciprocal identity; the complete fixed-bank global column compiler (`Bank.globalColumnCompiler`) over all globally neutral completions with no per-row neutrality; column zero-sum packet extraction with at least ⌊n/ℓ⌋ disjoint packets and the packet-abundance firewall; the Boolean column gcd theorem for `n ≥ 2q−1` with the constructive telescoping certificate and the sharpness witness at `n = 2q−2`; fixed-bank target mobility (`den(S_y) ∣ D_core`, paid components stay paid, bank untouched, exact target movement); distinct mobility targets (`2^H`), an AP-free mobility family, the `3^H` sumset count, and the exact mobility congruence coset `gcd{D/n} = D/G`; and the central exact combined terminal × mobility coefficient identity (`alignment_coefficient`, plus its sumset form).

Banked only as conditional interfaces, with the analytic content left OPEN and never inhabited or axiomatised: the support-size bound from a uniform row-fibre input, the Fourier anti-hole bridge, centrality-to-bounded-tilt, and the sparse-resonance / central-lobe / remaining-spectrum budgets; these feed the exact dependency theorem `conditional_terminal_closure`, which stops at a terminal completion and invents no bridge to a global counterexample. Explicit firewalls record the retracted universal shortcuts (per-row neutrality as necessary, packets ⇒ hit, gcd 1 ⇒ hit, many targets ⇒ long AP, etc.).

Validation: `lake build` succeeds for all default targets (8566 jobs, no errors); `AxiomAudit.lean` reports only `propext`, `Classical.choice`, `Quot.sound` (several theorems use fewer) for all 52 principal V3 theorems; a repository-wide search confirms no `sorry`, `admit`, `native_decide`, `unsafe`, `opaque`, custom `axiom` or `@[implemented_by]` in the layer. The full write-up — files, imports, theorem list, old/new search-space comparison, compiler and mobility statements, open owners, firewalls, dependency DAG, axiom audit and build result — is in `ERDOS287_ANCHORED_V3_GLOBAL_TERMINAL_MOBILITY_REPORT.md`. Verdict: BANKED_ANCHORED_V3_GLOBAL_TERMINAL_MOBILITY.

# Summary of changes for run 89bdc5f0-8fe6-4515-ae92-405a262103b6
I added an append-only **Anchored V2** layer to the Erdős #287 project. Erdős #287 remains OPEN and is not claimed; Route S, Route D and the earlier anchored route are untouched, and the certified finite frontier (67108856338751594, U2 pending) is re-checked unchanged and not extended.

New files: `RequestProject/Erdos287/AnchoredV2.lean` (aggregator) and, under `RequestProject/Erdos287/AnchoredV2/`: `FeedbackEdge.lean`, `BlockCut.lean`, `CactusMessage.lean`, `AffineNormalForm.lean`, `ThetaFirewall.lean`, `TrackedKernel.lean`, `UnitSubsetSum.lean`, `CoupledCharge.lean`, `CoupledBatchSupply.lean`, `FiniteExtension.lean`, `Capacity.lean`, `CapacityCertificate.lean`, `CapacityGap.lean`, `Level2.lean`, `RouteBridge.lean`, `Reconciliation.lean`, `AxiomAudit.lean`. Only `RequestProject/Main.lean` was modified (one added import). The required run report is in `ERDOS287_ANCHORED_V2_REPORT.md`.

Proved (machine-checked, both directions where stated): the exact feedback-edge reduction `sat_iff_exists_branch` with the `2^β` branch count and forest-complement bookkeeping (`anchored_forest_branches`, `beta_two_four_tests`: β = 2 ⇒ at most four complete forest tests); exact block-cut gluing at a certified articulation set (`sat_split_iff`, `sat_split_single_iff`) and the certified cactus message solver (`cactus_star_sat_iff`, plus `msg2_pathChild` identifying a path child's two-contact message with the existing transfer); the affine path normal form (family, uniqueness, non-tree trichotomy, `FullyBalanced` ⇒ one-parameter affine family, and the integral root progression `x₀ + L·ℤ` with its converse); the theta/bicyclic firewall (`thetaBalancedRejection_false`); the tracked-prime kernel with feasibility monotonicity in the tracked-prime set; the unit-list subset-sum theorem over `ZMod m` and the coupled `2^e × p` charge theorem via CRT; the finite coupled-batch extension theorem under an explicit finite supply record, with the literal restriction direction and the resulting finite equivalence; the weighted capacity function with monotonicity, the sound capacity inequality, the negative capacity rejection certificate, and its attachment to actual anchored kernels and to tracked kernels; the capacity incompleteness firewall (an abstract two-block four-port example that is integrally infeasible yet admits no negative Level-1 certificate at any weighting); and the Level-2 fractional interface with soundness (`feasible ⇒ Level-2 feasible`, hence Level-2 infeasibility rejects the actual kernel). The previously vague global branching obstruction is refined, not deleted: `UniformNegativeCapacity` and `UniformLevel2Rejection` are each proved to imply it, and the unconditional form stays refuted.

Explicitly left open and never inhabited: `UniformNegativeCapacity`, `UniformLevel2Rejection`, `FixedPowerCoupledSupply` (the external analytic supply hypothesis; nothing about ranges like `M^ρ` is asserted in Lean), and the stretch goal of forest Level-2 exactness, which was not attempted. Build: `lake build` succeeds (8548 jobs). The new namespace contains no `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `opaque` or `@[implemented_by]`; the axiom audit file prints the axioms of all 40 principal exported theorems, and each uses only `propext`, `Classical.choice`, `Quot.sound` (some fewer).

# Summary of changes for run 1c595733-4498-40f7-92a3-5b12067026b6
Added a new, fully append-only **anchored / contact-graph proof-side route** to the Erdős #287 project. **Erdős #287 is recorded OPEN and is not claimed**, no research claim was imported as a theorem, and nothing in the existing bank was changed: Route S with its ten-node cut, the complete Direct/Route-D programme (both proved bridges, reciprocal compiler, raw-mask arithmetic, boundary kernel, LCM/carry algebra, path polynomial, finite Fourier all-target lemma, sparse subreservoir, protected switches, target tuning, absorber interfaces with `ExactSignedAbsorber` OPEN, hostile countermodels), the certified finite frontier 67108856338751594, pending U2, and the OPEN status are all preserved and re-checked by theorem.

FILES ADDED — new namespace `Erdos287.Anchored`, aggregator `RequestProject/Erdos287/Anchored.lean` plus `Anchored/Core.lean`, `ReciprocalState.lean`, `Fingerprint.lean`, `PrimePowerLayer.lean`, `ContactGraph.lean`, `PathTransfer.lean`, `ForestElimination.lean`, `CycleElimination.lean`, `CycleRank.lean`, `BicyclicInterface.lean`, `RouteBridge.lean`, `Reconciliation.lean`, `AxiomAudit.lean`, and the report `ERDOS287_ANCHORED_CONTACT_GRAPH_FORMAL_SYNC_REPORT.md`. FILE MODIFIED: `RequestProject/Main.lean` — one added import.

KERNEL-PROVED CONTENT. (3) Finite anchored reciprocal state in exact rational arithmetic: allowed subsets `P ⊆ E ⊆ C \ N`, the permitted value set with the zero state represented explicitly (never as a numerator), `AnchoredFeasible`, the exact reduced-numerator criterion `v ≠ 0 → (v_p(v) ≥ 1 ↔ p ∣ num v)` for *every* prime, the finite fingerprint and the exact equivalence `feasible ↔ zero state allowed ∨ p ∣ F` (with no size claim about F), plus the resulting decidability. (4) The full prime-power layer condition: for the layer cofactor set with ambient lcm `L` and `t = v_p(L)`, `p^(t+1) ∣ ∑_{c∈E} L/c ↔ v_p(∑_{c∈E} 1/c) ≥ 1` for every nonempty `E ⊆ C`, with **no** coprimality assumption — the case `p ∣ c` is retained and exhibited by an explicit witness, and the empty-subset exception is recorded as a firewall. (5) The local contact relation of a layer: a Boolean signature on the contact positions is allowed exactly when some subset agreeing with it on those positions satisfies the full anchored equation (noncontact cofactors existentially quantified); the contact graph is formalized as a finite binary constraint system with an exact decision procedure. Beyond that: exact leaf elimination (both directions), termination, iterated peeling and the forest decision; exact path transfer and the four-pair decision of isolated cycle components; the excess (cyclomatic count) with invariance under peeling and values 0 for paths and 1 for cycles; and the reduction of every finite instance to a leafless branching kernel. The endpoint theorem `anchored_contact_endpoint` packages exactly the requested statement: satisfiability is exactly decidable, forest and isolated-cycle components are decided exactly, and every remaining component reduces to a finite branching kernel that is still exactly decidable. The **global rejection of all branching kernels is OPEN** — stated as a parameterised interface and deliberately not inhabited — and its unconditional form is refuted by an explicit satisfiable leafless instance of excess 2. Two proved bridges connect the route to existing objects: for cofactors prime to `p`, the anchored valuation condition is exactly the mod-`p` inverse-sum condition, hence the cofactor set of the top `p`-adic layer of any set with reciprocal sum 1 is anchored-feasible; and the exact counterexample predicate yields the ambient compiler identity in the anchored conventions.

BUILD/TRUST: full `lake build` PASS (8530 jobs, 0 errors). `#print axioms` on every principal new theorem reports only `propext, Classical.choice, Quot.sound`. No `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `opaque` or `@[implemented_by]` in any new file; no linter warnings in the new modules. All work is committed.

NOTE ON SCOPE: the instructions I received end mid-sentence in section 5 ("The relation must incorporate accumu…"), so anything you intended after that point was not available. I formalized sections 3 and 4 in full, section 5 as far as it was given (contact relation with full anchored equation), and carried the programme through to the stated endpoint (forest/cycle elimination, cycle rank, branching-kernel reduction, route bridge, reconciliation, axiom audit). If you resend the remainder of section 5 and any later sections, they can be added on the same append-only basis.

# Summary of changes for run 40e26b49-3382-4042-83b5-9cf901f7a09a
Added the Direct Reciprocal ("Route D") programme to the existing Erdős #287 project, append-only. **Erdős #287 is recorded OPEN and is not claimed**; no research-report conclusion was imported as a theorem, and no custom axiom was introduced.

FILES ADDED — new namespace `Erdos287.Direct`: aggregator `RequestProject/Erdos287/Direct.lean` plus `Direct/Core.lean`, `Direct/ReciprocalCompiler.lean`, `Direct/RawMask.lean`, `Direct/BoundaryKernel.lean`, `Direct/LCMCarry.lean`, `Direct/PathPolynomial.lean`, `Direct/LargePrimeCompletionFinite.lean`, `Direct/SparseSubreservoir.lean`, `Direct/ProtectedSwitches.lean`, `Direct/TargetTuningFinite.lean`, `Direct/AbsorberInterfaces.lean`, `Direct/CurrentStatus.lean`, `Direct/Reconciliation.lean`, and the report `ERDOS287_DIRECT_ROUTE_FORMAL_SYNC_REPORT.md`. FILE MODIFIED: `RequestProject/Main.lean` — one added import.

KERNEL-PROVED CONTENT. Direct core: interval/mask/selected-set conventions with both bridges to the project's exact counterexample predicate proved (forward and backward). Exact ambient-LCM compiler as an equivalence, with the three denominators kept separate, an empty-subset consistency check and a firewall showing the `0 ∉ I` hypothesis is necessary. Raw-mask arithmetic: the `n = d·r` factorisation with `d ≤ 136` and its uniqueness for `M ≥ 18632`; mask counts only via an explicit counting interface. Boundary kernel: pin disjointness, non-adjacency of forced zeros, forced neighbours, the restriction bridge, and the top prime-power congruence bridges into the elementary package. Exact LCM/carry algebra: `p^e ∣ lcm(1..N) ↔ p^e ≤ N`, `L_N = J_N·L_{N-1}` with `J_N = p` at prime powers and `1` otherwise, fibrewise carry aggregation, and the descending recurrence with its divisibility criterion (no complexity claim). Path polynomial: coefficient formula, the **exact reciprocal target theorem** (reciprocal sum `= 1` ⟺ positivity of the coefficient of `X^τ`), the recurrence `F_i = F_{i-1} + X^{w_i}F_{i-2}`, and factorisation across separated components. Finite Fourier all-target lemma: the exact additive-character identity and the sufficient condition `(q−1)B < 2^{|C|}` ⇒ every residue attained — proved in the kernel, with the exponential-sum bound only as a named hypothesis. Sparse subreservoir: monotonicity, the floor `q ≤ 2^{|C|}`, and the reduction to an exponential-sum bound on the sparse set (the claim itself stays OPEN, not inhabited). Switch calculi: `1/(6k) = 1/(10k) + 1/(15k)`, carry neutrality exactly under `30k ∣ D` (with a counterexample otherwise), the signed increment, and from the full `ProtectedSwitch` predicate the preservation of endpoints, of the no-two-consecutive-omissions rule and of agreeing tracked statistics plus the exact value shift. Target tuning: the finite greedy-crossing lemma and the deterministic straddling bridge, conditional on four named open interfaces. Absorber: `D_buf`, `b_buf` and the necessary lattice conditions; `ExactSignedAbsorber` defined and deliberately not inhabited (OPEN).

RECONCILIATION AND AUDIT. The Route-S ledger and its ten-node cut set are re-checked unchanged; both routes' cut nodes remain open, so neither discharges the other; the only cross-route bridges are the two proved ones; the certified finite frontier is exactly the existing ceiling 67108856338751594 with U2 still pending, and Route D adds no finite exclusion node. Four hostile-audit refutations are proved: the kernel-extension interface is false for an explicit feasible kernel (conditional survivor ⇏ actual survivor); two individually feasible kernels can have no common realisation; approximate straddling ⇏ exactness; a value-moving switch satisfying every local condition can still change a tracked statistic.

BUILD/TRUST: full `lake build` PASS (8516 jobs, 0 errors). `#print axioms` on every principal new theorem reports only `propext, Classical.choice, Quot.sound` (two depend on none). No `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `@[implemented_by]` or `opaque` in any new file; no linter warnings in the new modules. All work is committed.

# Summary of changes for run ffb7e388-b061-4bf5-bdc1-cb660778a5e8
Continued the existing Erdős #287 project append-only on its pinned toolchain. No existing module, theorem statement or ledger value was altered; one import line was added to `RequestProject/Main.lean`. **Erdős #287 is recorded OPEN and is not claimed.**

FILES ADDED (all under `RequestProject/Erdos287/`, all imported from `Main.lean` via the new aggregator): `FivePrimeSourceGeometry.lean`, `DirectedSelbergFiniteAlgebra.lean`, `HighXConsumerLedger.lean`, `PhysicalK1Owner.lean`, `CurrentStatusLatest.lean`, plus the report `ERDOS287_SOURCE_CAPACITY_LATEST_SYNC_REPORT.md`. File modified: `RequestProject/Main.lean` (one import).

BUILD/TRUST: full `lake build` PASS (8502 jobs, 0 errors). `#print axioms` on every principal new theorem reports only `propext, Classical.choice, Quot.sound` (three depend on `propext` alone). No `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `@[implemented_by]` or `opaque` in any new file.

STRICT FINAL OUTPUT
- MAIN OLD BANK: PRESERVED (bounded-conductor layer, EARLY_4490 ancestor, long-fibre/multiplicity layers untouched; `banked_layers_preserved_latest` re-checks their evidence classes)
- FINITE OLD MAIN CEILING: `Erdos287.no_Erdos287Counterexample_of_max_le_extendedCeiling` (M ≤ 67108856338751594), restated as `finite_ceiling_here`
- U2 PROJECT SUPPLIED: NO
- FINITE ≤ U2: PENDING (`u2_reconciliation_pending`, tagged `pendingExternalImport`; also proves the available ceiling is strictly below U2, so nothing here implies the U2 statement). No certificate invented.
- U2 STATEMENT-INTEGRITY CHECK: NOT AVAILABLE
- FIVE-PRIME +6 SOURCE: KERNEL FORMALISED for the finite exponent geometry. The file fixes the conventions explicitly (low prime pinned; closed window endpoints, half-open collars) and proves: `H = N2 − N1 − N3`; disjointness/unconditional bounds; the exact chamber values (+ boundaries `a = 2δ`, `a = 2δ'`); sign separation `N1+N3>0 → N2=0` on the balanced chamber; `H ∈ {−6,0,+6}` there; the explicit `+6` cell (`plusSix_cell_H`); separation cost ≤ 6 and = 6 on that cell; representation error = 0; unique factorisation in disjoint prime boxes. It also proves `straddle_witness`: an explicit legal but *unbalanced* cell with N1>0 and N2>0, so sign separation genuinely requires the balanced chamber.
- DIRECTED SELBERG FINITE ALGEBRA: KERNEL FORMALISED (partial by design): capacity `1/G`, the quadratic-form inequality on the normalised simplex (λ₁ = 1), attainment of the optimum, the diagonalisation-consumer form, capacity monotonicity, proper-prime-power thinness, and the exact rational comparison `6.3e−7 / 0.3 = 2.1e−6`.
- T_box FINAL BOUND: CONDITIONAL ON <directed-sieve capacity input `A ≤ W/G` with `G ≥ 9523810`; prime comparison `B ≥ 0.3·W`>. The two deterministic bridges are proved (`T_box_bound_of_capacity`, `T_box_ratio_bound`); no external prime estimate was introduced as an axiom.
- HIGH-X CONSUMER LEDGER: INCOMPLETE (structure, available-budget arithmetic, monotonicity and fit criteria are proved; the true analytic constants are not formalised)
- 2.1e−6 B_prime ALLOCATION: UNDECIDED — `allocation_verdict_undecided` exhibits admissible ledgers on both sides; `early_slab_budget_too_small` proves the historical 1e−11 early-slab budget cannot host it
- ONE-LOW/FOUR-HIGH SOURCE UNION: finite chamber geometry only (legal region, H values, positive/negative/inert chambers, boundaries). The continuous integral is explicitly NOT claimed; the isolated remaining analytic proposition is a region-level directed-sieve bound over the source union.
- OLD FixedConductorCharacterBound: FALSE / RETIRED (refutation re-exported, never used as a hypothesis)
- OLD BoundedConductorK1Target: FALSE / RETIRED (same)
- NEW PHYSICAL k=1 OWNER: `PhysicalK1Budget b : ∀ X w A B z, SourceWeight w → PhysicalWindow X A B → |Σ_{1000<ℓ≤5000} Σ_{s∈[A,B)} w s·(K_ℓ(s,z) − mean_ℓ(z))| ≤ b·X` (bounded true source weights, long physical hyperbola windows, exact density centring). Proved about it: the density witness that killed the old target vanishes under the centring; some explicit budget works (so the content is smallness); monotonicity; the deterministic bridge to the ledger; a per-conductor reduction; and the constant-weight case closed with the X-independent constant `centredBudget`. The ledger-admissible instance is OPEN.
- OMEGA TWO / OMEGA ONE / PROPER GAMMA / S_live / R_012 / SIGNED FLOOR / FINAL SPLICE: OPEN (audited, unchanged, all `openNode`)
- CURRENT MINIMAL OPEN CUT SET (`latestCutSet`, with `cutSet_all_open`, `cutSet_prerequisites_closed` proving every prerequisite is already closed, and `erdos287_needs_cutSet`): 1. quantitative physical k=1 owner (narrowed to a per-conductor bound for non-constant weights); 2. affordability of the 2.1e−6·B_prime allocation in the true ledger; 3. Ω(k)=2; 4. Ω(k)=1; 5. EARLY_4490 residual; 6. proper gamma; 7. S_live; 8. R_012; 9. signed floor; 10. final splice.
- ERDŐS #287: OPEN

NEXT_GENERATION_STATE — U2 reconciliation: PENDING (project not supplied; import the smallest clean finite module when it is, without changing either problem predicate). High-X consumer budget: not yet determined; the ledger is formalised exactly and the 2.1e−6 allocation is UNDECIDED until b_T, t_T, E_L, E_2, E_M and the transfer costs are pinned. Current minimal open cut set: as listed above, starting from the per-conductor non-constant-weight k=1 bound and the ledger affordability node.

# Summary of changes for run e0c3b76b-0a57-4a8e-b850-b7131d1eb224
Continued the existing project from its committed state — nothing was restarted, rewritten or deleted. Details are in `ERDOS287_FRONTIER_AUDIT_SYNC_REPORT.md`.

CURRENT GIT/REPO STATE: entered on the single existing commit with a clean tree (467 Lean modules); left on 5 new commits, tree clean. Only additions plus one added import line in `RequestProject/Main.lean`.

INTERRUPTED WORK RECOVERED: the whole bounded-conductor layer (CompensatedMeasure, HyperbolaInterfaces, CompensatedSummationByParts, AdjacentInterfaceFirewall, ResidueCollapse, InternalProductFibre, SmallEllCRT, HalfOpenProgressionCompiler, SmallEllMeanCovariance, CompensationLoop, BoundedConductorFrontier, RankThreeOperator, RankThreeProjection, ConductorComplementLedger, AnnihilatorFamily, DensityCompensationRestoration, CurrentStatusEffectivityBoundedConductor) was already present, imported and building — verified, preserved, not redone. What was missing was the declaration-registration/audit stage and the continuation of the frontier; both are now done (registrations updated, status aggregator, evidence table, axiom audit, sync report, continuation state).

FULL LAKE BUILD: PASS (8497 jobs; entry build also passed at 8493).

AXIOM AUDIT: PASS — `#print axioms` on every principal new theorem reports only `propext, Classical.choice, Quot.sound` (one depends on none). No `sorry`, `admit`, custom axiom, `native_decide`, `unsafe`, `@[implemented_by]` or `opaque` in any new file.

MAIN #287 FORMAL BANK: fully preserved (EARLY_4490 remains a valid ancestor; long-fibre, multiplicity and bounded-conductor layers untouched). Four new modules added: `FixedConductorCharacterRepair`, `BoundedConductorTargetAudit`, `CentredFrontierTriviality`, `CurrentStatusEffectivityFrontierAudit`.

NEW RESULTS (all kernel-proved). Working on the `k=1` owner produced a decisive negative audit rather than a closure:
- `fixedConductorCharacterBound_unsatisfiable` — the recorded live frontier target `FixedConductorCharacterBound` is FALSE for every budget (one-point window at the prime conductor 2503; the surviving value is periodic and nonzero in the outer variable). The banked conditional bridge to the `k=1` owner bound is therefore vacuous.
- `characterMeanBound_iff_boundedConductorTarget` — the normalised character interface is exactly equivalent to the pointwise target, so the character/DFT packaging adds nothing.
- `returnedKernel_long_window` + `meanSum_ne_zero` (4999-adic valuation −1) ⇒ `boundedConductorK1Target_unsatisfiable` — the pointwise `k=1` target is FALSE for every budget: over n full periods the returned kernel equals P·n·meanSum with meanSum ≠ 0 (a density obstruction, matching the banked `DX_term_not_removable` firewall).
- Density-centred replacement target `CentredBoundedConductorK1Target` (ordered windows; the restriction is proved necessary), and `centred_target_satisfiable` — it holds for an explicit budget, so qualitative boundedness of the finite periodic kernel carries no analytic content.

FINITE ≤10^60: NOT PRESENT (not in the supplied repository; not reconstructed). What is kernel-proved here is no counterexample with maximum M ≤ 67108856338751594, restated as `finite_ceiling_kernel_proved`, with `finite_ceiling_below_ten_pow_sixty` recording that this ceiling is below 10^60.
FINITE ≤U2: PENDING — the certified-factor data and harmonic-blocker witness for U2 are not present in the project, so nothing was invented.

CURRENT MINIMAL OPEN CUT SET:
1. quantitative, ledger-admissible `k=1` budget stated for the physical hyperbola windows / source (the qualitative version is settled and empty of content);
2. Ω(k)=2; 3. Ω(k)=1; 4. EARLY_4490 residual; 5. proper gamma; 6. S_live; 7. R_012; 8. signed floor; 9. final splice.

FIXED CONDUCTOR CHARACTER BOUND: REFUTED (was OPEN; never inhabited)
K1: OPEN — but the previously recorded target statement is refuted; the owner must be restated quantitatively
RANK THREE: STRICTLY_REDUCED (unchanged, certificate-backed)
OMEGA TWO: OPEN · OMEGA ONE: OPEN · PROPER GAMMA: OPEN · S_LIVE: OPEN · R_012: OPEN · SIGNED FLOOR: OPEN · FINAL SPLICE: OPEN
ERDŐS #287: OPEN (not claimed)

CONTINUATION STATE: start from cut-set item 1 — restate the `k=1` owner as a quantitative bound over the physical hyperbola windows with the true source weights and an explicit ledger budget, then re-derive the bridge to the owner ledger; the refuted statements must not be reused as hypotheses. All exact machinery (CRT compiler, ≤65 atoms, half-open progression compiler, local mean, Gram structure, compensation-loop firewall, returned finite-conductor kernel) is unchanged and reusable.

# Summary of changes for run 214f29cc-e9b9-4bf9-b8b5-33e8e60924af
Appended a new, self-contained **EARLY_4490 rational-jet layer** to the Erdős #287 effectivity bank. Everything is append-only: no existing module, theorem statement or ledger value was altered, and **Erdős #287 is recorded OPEN and is not claimed**.

**Files added** (all under `RequestProject/Erdos287/`): `ProperGammaAdmission.lean`, `Early4490FiniteACompiler.lean`, `Early4490BernoulliJet.lean`, `Early4490RationalJetSource.lean`, `Early4490FiniteDFT.lean`, `Early4490NearResonance.lean`, `Early4490RationalJetLedger.lean`, `CurrentStatusEffectivityEarly4490.lean`, plus the report `ERDOS287_EARLY4490_RATIONAL_JET_FORMAL_SYNC_REPORT.md`.
**File modified**: `RequestProject/Main.lean` — one added import of the new aggregator.

STRICT FINAL OUTPUT
- MULTIPLICITY BANK: PRESERVED (long-fibre and proper-γ modules untouched and reused; `banked_layers_preserved` re-checks their values)
- HIGH-PRIME COUNT ≤ 3: KERNEL-PROVED (`highPrimeCount_le_three`, with `admission_threshold_pow` supplying `z < (N_z^ν)^4` from `4ν > γ`; ν never replaced by ν/2)
- ADMISSION e = 1 − C2 + 2C3: KERNEL-PROVED, all cases j = 0,1,2,3, plus “coefficient +2 forced” and “no j ≥ 4 case”
- γ = a₀ + ν/2 and 4ν > γ: KERNEL-PROVED in exact rationals (no floating point in any statement)
- FINITE-a COMPILER: KERNEL-PROVED (`finiteA_compiler`), including `largePrime_mask_irrelevant` (primes p > N dividing M cannot alter the mask for a ≤ N)
- FINITE-a PARTIAL SUMMATION: KERNEL-PROVED (`abel_summation_general`, `finiteA_partial_summation`), with an explicit finite witness that the compiler does not imply fibre annihilation
- BERNOULLI B2/B3 ALGEBRA: KERNEL-PROVED (values, reflections, and the derivative ladder B₃′ = 3B₂, B₂′ = 2ψ in `Polynomial ℚ`); strict sawtooth endpoint convention retained
- THREE-TERM Φ₃: KERNEL-PROVED DEFINITION; J3 and Jψ SOURCES: KERNEL-PROVED DEFINITIONS, with the exact chart difference
- I_X = Φ₃ + E₃ + Δ: CONDITIONAL ANALYTIC INTERFACE (hypothesis structure, no custom axiom)
- J3 TARGET 6.33976032e-9 and Jψ TARGET 4.03976032e-9: KERNEL-PROVED BUDGET ARITHMETIC (from `parentAvailable − 1.1e-10 = 8.03976032e-9`)
- ALTERNATIVE-CHART FIREWALL: KERNEL-PROVED (each chart closes exactly; charging both replacement errors strictly overspends)
- FINITE q-DFT: KERNEL-PROVED exact inversion (finite sums only); f1, f2, f3 ZERO MODES: KERNEL-PROVED, with mean(f₂) = μ(q)φ(q)/(6q²) for squarefree q, plus the coprimality-mask firewall (explicit q = 3 witness)
- NEAR-RESONANT DIVISOR IDENTITY: KERNEL-PROVED, reusing the banked odd-convolution weights; no smallness inferred
- CERTIFICATE-BACKED (typed, deliberately not proved): |2R[C3]|/B_X < 1.1e-10, late subslab < 7.8e-9, |J−J3|/B_X < 1.7e-9, |J−Jψ|/B_X < 4e-9, ‖W″‖∞ < 2110, ‖W‴‖₁ < 9800, and the EARLY_4490 range data (odd a ≤ 4489, c=2 lane a ≤ 2245, z < 7.94e10, p < 291200, q < 3.913e9), whose integer consequences are proved from the declared inputs
- OPEN: J3 and Jψ analytic bounds, EARLY_4490 (strictly reduced), proper-γ over the full slab, S_live, R_012, signed floor, final splice, Erdős #287; MAYNARD: NOT ENTERED — all certified by `early4490RationalJet_open_frontier` (no open node tagged closed, no open proposition inhabited)
- DEDICATED BUILD: PASS for every new module; FULL `lake build`: PASS (8476 jobs, 0 errors)
- AXIOM AUDIT: PASS — `#print axioms` on every principal new theorem reports only `propext, Classical.choice, Quot.sound` (several depend on none); no `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `@[implemented_by]` or `opaque` escape in any new file

Two deviations are recorded honestly rather than papered over: the f₁/f₃ zero-mode proofs need only `q > 1` (not oddness), so the theorems are stated in that more general form, and `q = 1` genuinely fails under the strict endpoint convention (recorded as a theorem); and the `MtruncN ∣ M` lemma turned out not to need positivity of M, so that hypothesis was dropped.

# Summary of changes for run 0c5f313f-39bb-412e-adc8-d7a2e0b7f81f
"Leanified" the proper-γ / multiplicity-geometry sync as an append-only layer. Erdős #287 is **not** claimed — it is formally recorded as OPEN, and no computer-assisted analytic certificate was turned into a kernel-proved theorem.

## Files added (all under `RequestProject/Erdos287/`)
`ProperGammaQFibre.lean`, `ProperGammaLaneRecombination.lean`, `ProperGammaSource.lean`, `ProperGammaMultiplicityGeometry.lean`, `ProperGammaShellSix.lean`, `ProperGammaCurrentSurvivor.lean`, `ProperGammaProductResummation.lean`, `ProperGammaOddConvolution.lean`, `ProperGammaTruncatedDivisor.lean`, `ProperGammaMultiplicityLedger.lean`, `CurrentStatusEffectivityMultiplicity.lean` (new aggregator), plus the report `ERDOS287_PROPER_GAMMA_MULTIPLICITY_FORMAL_SYNC_REPORT.md`.

## File modified
`RequestProject/Main.lean` — a single added import of the new aggregator. No existing module was rewritten; the long-fibre bank is preserved and reused (`BsrcWeights`, `AllQResummation`, `EdgeCutoffLedger`, `CurrentStatusEffectivityLongFibre`).

## Kernel-proved content
- **q-fibre**: `qFibre_reparam` (d ∣ ℓ ∧ ℓ > d ↔ unique q with ℓ = dq, q > 1 odd squarefree coprime to d), `beta_qFibre_mul`, plus a firewall that multiplicativity fails without coprimality.
- **Lane recombination**: `lane_recombination` (σ_c μ(d)B(d) = μ(z)B(z), z = cd), `lane_sign_transfer`, `lane_signs_survive`, and `lane_range_restricted_no_cancellation` (the same-d cancellation is not a legal source identity).
- **Multiplicity geometry**: `N_X(m) = ⌊9X/10/m⌋ − ⌊7X/10/m⌋` with an exact counting interpretation; a general engine `multAtLeast_iff` giving, for *every* k ≥ 1, the exact rational band decomposition of {N ≥ k}; explicit bands for k = 1…7; shells, monotonicity and pairwise disjointness. `shellOne_bands` gives the seven disjoint N = 1 bands; `shellSix_bands` / `NX_eq_six_iff` give the seven exact N = 6 bands and disjointness from shells 1–5 and from N ≥ 7.
- **Survivor**: `Ω_{≥7} = (0,9/310] ∪ (7/240,3/100] ∪ (7/230,9/290] ∪ (7/220,9/280]` proved to be exactly {N ≥ 7}; the region-restricted signed source `R_{≥7}` is defined with split algebra, and `Rge7_not_bounded_here` certifies that no smallness proposition is inhabited (its analytic bound stays OPEN).
- **Source**: `SGproper` is defined source-faithfully (γ admission, liveness, continuous endpoint, squarefreeness, coprimality, signs), with firewalls showing the coprimality and liveness markers change the value.
- **m = q·n**: `product_resummation` with the lower cutoff retained, and `lower_cutoff_matters` showing that dropping `m > z` changes the source; complementary n-geometry (n ≤ 21 absent, 22–24 exceptional, ≥ 25 chain-merged with t ≤ 9/310) with arithmetic conditions kept strictly separate in both directions.
- **Divisor / convolution algebra**: `truncated_divisor_identity` (A_z(m) = B(zm)/B(z) − excluded owner sums, reusing the banked all-q identity) with the naive identity refuted; `oddConvolution_identity` (g_z = 1_odd * h_z); `|ρ_odd| ≤ 1/2`; the finite-level factor-two inequality `|E_z(x)| ≤ (1/2) H_{z,α} x^α`.
- **Ledger / firewalls**: exact rational owner arithmetic (1.83e-8 + 2.4e-8 + 2.16e-8 + 7.77e-9 = 7.167e-8), target 7.204976032e-8, child remaining 3.7976032e-10, parent allocation 8.14976032e-9; `parent_child_owner_disjoint`, `shell6_parent_recombine_legal`, `shell6_double_charge_illegal`; the global ledger (5.257263872e-7 / 3.603386128e-7) explicitly left unchanged pending reconciliation.
- **Status**: an evidence taxonomy (KERNEL_PROVED / CERTIFICATE_BACKED / CONDITIONAL_ANALYTIC / RETIRED_NONCLOSING_METHOD / OPEN / NOT_ENTERED) and `properGammaMultiplicity_open_frontier`, proving no open node is tagged closed; Erdős #287 recorded OPEN, Maynard NOT ENTERED.

## Certificate-backed, deliberately *not* proved
q ≤ 200 (1.83e-8), N = 1 (2.4e-8), N = 2..5 (2.16e-8), N = 6 (7.77e-9), and H₀ < 88/5, C₁ < 5/4, C_{3/5} < 31/10 — all typed certificate objects, with theorems showing that inhabiting them carries no analytic content. `∑_d h_z(d)/d = 1/B(z)` is a hypothesis-level interface (conditional), not a theorem.

## Build and audit
Every new module builds individually, and the **full `lake build` passes** (8468 jobs, exit 0). The new files contain no `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, `@[implemented_by]` or `opaque` workaround; the aggregator's `#print axioms` audit shows only `propext`, `Classical.choice`, `Quot.sound` (several nodes depend on none).

One honest deviation is recorded in the report: the reported complementary-n split "22–30 exceptional / ≥ 31 passing" reconstructs, in the coordinates formalised here, as "22–24 exceptional / ≥ 25 chain-merged"; only the reconstructed statement is banked (the n ≤ 21 absence agrees).

# Summary of changes for run 95e25a04-6c8b-4224-a796-0dd9d31f1d62
Extended the Erdős #287 effectivity kernel bank with the new long-fibre material. All pre-existing modules are untouched; only new modules were added.

**FILES ADDED** (all under `RequestProject/Erdos287/`)
`CompletePeriodEndpoint.lean`, `LambdaWeights.lean`, `EdgeCutoffLedger.lean`, `AggregateThreshold.lean`, `AllQResummation.lean`, `ChartEquivalence.lean`, `CurrentStatusEffectivityLongFibre.lean`, plus the report `ERDOS287_GOLD_LONGFIBRE_SAFE_BANK_REPORT.md`.

**FILES MODIFIED**: none (BsrcWeights, AllComplement, OddHalfDivisor, Reflection, MediumLedger, C1C2Splice, OddLineCancellation, RatioBoundary, EulerLocal, TwoVariableZ, PerronAlgebra, IncrementalDirectedLedger, CurrentStatusEffectivity are preserved verbatim; the new status ledger imports and extends the old one).

**FULL `lake build`: PASS** (8457 jobs, 0 errors).

Strict output:
- LAMBDA FINITE ALGEBRA: KERNEL-PROVED — λ(b)=∏_{p|b}(p−1)/(p−2)², coprime multiplicativity, finite prime-product identity, positivity, and the exact local Euler algebra λ = B0·β on odd squarefree b. `H_λ(0) < 8/3` is *not* proved: it is split into a finite exact product theorem, an explicit analytic-tail hypothesis object, and the conditional combination, with a firewall theorem showing the conditional is not an unconditional claim.
- EDGE REPLACEMENT SEMANTICS: KERNEL-PROVED — explicit cutoff-status type (previous 50, current 1000), update law `old − oldEdge + newEdge`, and `edge_double_charge_illegal` (charging both is strictly larger; the conventions agree only when the old charge is 0). The `< 7.22e-10` edge estimate is carried as a certificate object, not an axiom.
- UPDATED SUBTOTAL 5.257263872e-7: KERNEL-PROVED; UPDATED CAPACITY 3.603386128e-7: KERNEL-PROVED, with `8.86065e-7 − 5.257263872e-7 = 3.603386128e-7` in exact rationals, plus a supersession theorem (subtotal strictly up, capacity strictly down vs. the previous ledger).
- COMPLETE-PERIOD COVARIANCE: KERNEL-PROVED — `(1/L)Σ_{v mod L} φ_{q1}^{(c)}(v)φ_{q2}^{(c)}(v) = (g²−1)/(12 q₁q₂)` for the centred finite sawtooth endpoint function, proved by exact finite computation (two-scale range splitting, an affine permutation of a complete residue system, Gauss sums) — no numerical testing. Corollaries: COPRIME ENDPOINT ORTHOGONALITY (KERNEL-PROVED), nonnegativity, strict positivity exactly on gcd>1 strata, gcd-stratum dependence, lane independence, odd specialisation. The identity needed only positivity of the moduli, so oddness is recorded as a specialisation rather than a hypothesis.
- REMAINING TARGET ARITHMETIC 69/5000 − 469/75000 = 283/37500: KERNEL-PROVED (endpoint budget constants banked as certificate data; also proved: the diagonal+off-diagonal lines exceed the period line, so they cannot substitute for it).
- F/ED/DD/S TYPE: KERNEL-PROVED — `C_rem = C_F + 2C_ED + C_DD + C_S` and its componentwise combination law.
- ANALYTIC REMAINDER BOUND: OPEN — `C_rem < 283/37500` is stated as a proposition with no proof, plus a firewall showing it is a genuine (non-tautological) goal.
- ALL-q RESUMMATION: KERNEL-PROVED — finite divisor identity `Σ_{q|n,(q,b)=1} β(q) = B(bn)/B(b)`, the exact split of `A_b^>(n)`, the hyperbola interchange `Σ_{n≤X} A_b^>(n) = Σ_{q≤X,…} β(q)⌊X/q⌋`, and its exact rewriting `= X·P_b^>(X) + Σ β(q)(⌊X/q⌋ − X/q)` in smooth singular-series discrepancy form. No discrepancy estimate asserted.
- CHART EQUIVALENCE: KERNEL-PROVED (source typing) — the λ-covariance and all-q charts carry the same source when cutoffs match, and charging both as independent errors is never chart-legal.
- UNWEIGHTED CJOINT 0.09: RETIRED / FIREWALLED — status and reason as metadata; proved it is not in the banked closing-estimate list.
- MEDIUM-k: OPEN (strictly reduced); TWO-HIGH: NOT ENTERED; SIGNED FLOOR: OPEN; MAYNARD: NOT ENTERED; ERDŐS #287: OPEN — all recorded by `longFibre_open_frontier`, which proves no open node is marked proved/certified/conditional.
- AXIOM AUDIT: `#print axioms` is run for every new principal theorem in the new status module; each depends only on `propext`, `Classical.choice`, `Quot.sound` (several on no axioms at all). No `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, `implemented_by` or `opaque` occurs in any new module.

Erdős #287 is not solved and not claimed.

# Summary of changes for run 61962c4d-c5c0-4dd9-944e-43a4d968eba9
Added a new, self-contained Erdős #287 **effectivity kernel bank** to the project — thirteen Lean modules, all proved, all wired into the default build. Full `lake build` **PASSES** (8450 jobs); no `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, `implemented_by` or `opaque` occurs in any new file, and `#print axioms` on all fifty principal theorems reports only `propext, Classical.choice, Quot.sound` (or none). **Erdős #287 is not claimed**; the joined square function, `C_joint ≤ 0.09`, medium-k, the two-high gap, the signed floor and Maynard are untouched.

Files added (`RequestProject/Erdos287/`): `BsrcWeights`, `AllComplement`, `OddHalfDivisor`, `Reflection`, `MediumLedger`, `C1C2Splice`, `OddLineCancellation`, `RatioBoundary`, `EulerLocal`, `TwoVariableZ`, `PerronAlgebra`, `IncrementalDirectedLedger`, `CurrentStatusEffectivity`; plus the report `ERDOS287_EFFECTIVITY_KERNEL_BANK_REPORT.md`. `RequestProject/Main.lean` gained the thirteen imports.

STRICT OUTPUT — PHYSICAL B1 NORMALIZATION: KERNEL-PROVED (B0/β multiplicative, `B1·B(ab)=B(a)B(b)`, plus a firewall showing one-B1-per-prime is a different normalisation) · ALL-COMPLEMENT DISCRETE: KERNEL-PROVED (`B(d)·∑_{k|n,(k,d)=1}β(k)=B(dn)`, by finite prime-factor products only) · CONTINUOUS EULER IDENTITY: KERNEL-PROVED finite / CONDITIONAL infinite (convergence is a `Tendsto` hypothesis, never postulated) · ODD HALF-DIVISOR: KERNEL-PROVED (exact variable change `n>cd ↔ c d²<w`) · w=6 FIREWALL: KERNEL-PROVED (`H₁^odd(6)=1` vs unrestricted `0`) · FULL-vs-MEDIUM TYPING: KERNEL-PROVED · INCREMENTAL LEDGER TYPE: KERNEL-PROVED (no coercion inserts a full estimate without an explicit removal list) · HALF-DIVISOR REFLECTION: KERNEL-PROVED, both boundary forms, plus special cases A and B · c1/c2 DISCRETE SPLICE: KERNEL-PROVED (the `4d` endpoint is derived from `n↦2n`) · c1/c2 CONTINUOUS SPLICE: KERNEL-PROVED, both ½'s coming from the substitution, integrability an explicit hypothesis · FULL ODD DISCRETE CANCELLATION: KERNEL-PROVED · CONTINUOUS COEFFICIENT CONVOLUTION: KERNEL-PROVED (`μ1_odd/φ = mOdd ⋆ r`), downstream cancellation conditional on `∑ mOdd = 0` · RATIO-BOUNDARY: KERNEL-PROVED (conditional on the two cancellations) · G_p LOCAL FACTOR and FINITE `B1·G(u,0)=1`: KERNEL-PROVED · TWO-VARIABLE LOCAL EULER IDENTITY and FINITE `Z(s,s)=0`: KERNEL-PROVED · INFINITE `Z(s,s)=0`: BLOCKED BY ANALYTIC CONVERGENCE (only a formal-product congruence is recorded, clearly labelled) · G ABSOLUTE-CONVERGENCE REGION: PARTIAL (`|G_p(u,0)−1| = 1/(p(p−2)) ≤ 3/p²`; the two missing analytic inputs are isolated in the docstring) · PERRON VARIABLE CHANGE: KERNEL-PROVED (algebra/Jacobian/kernel compensation only, no contour theorem) · STRICT EQUALITY ALGEBRA: KERNEL-PROVED conditional, giving `2(Δ₁−Δ₂)` from the −4 outer factor · INCREMENTAL LEDGER ARITHMETIC: KERNEL-PROVED (`8.86065e-7 − 5.250043872e-7 = 3.610606128e-7`, capacity `> 3.610606128e-7`) · JOINED SQUAREFUNCTION / MEDIUM-k / TWO-HIGH GAP / SIGNED FLOOR: OPEN · MAYNARD: NOT ENTERED · ERDOS287: OPEN.

Two places where the specification was ambiguous are documented explicitly rather than guessed silently: the `c=2` lanes are defined as the `n↦2n`-substituted lanes (which is what makes the `4d` endpoint and the two ½'s derived, not assumed), and `Z_P(u,v)` is defined as the difference of the two finite prime products. One statement was also weakened in hypotheses rather than strengthened: the all-complement identity turned out not to need `d` odd, so it is proved for all `d ≠ 0` with the requested odd-`d` form as a corollary.

# Summary of changes for run ff3caa6e-75f3-41eb-90ea-f831247718b8
Delivered both requested pieces: the Erdős #287 effectivity certificate bank and the surgical P0 `B_src` normalisation repair. Full `lake build` passes (8437 targets, no errors); a detailed report is in `ERDOS287_CERTIFICATE_BANK_AND_P0_REPAIR_REPORT.md`.

LEAN FILES (new)
`RequestProject/Erdos287/{SourceWeights, GcdDescent, BernoulliKernel, MediumKSource, RepeatedCores, DirectedLedger, FloorInterface, Bank}.lean` and `RequestProject/Status/CurrentStatusErdos287CertificateBank.lean`.
Edited surgically: `RequestProject/CurrentProgramme/Erdos287September4BsrcLocalMobiusCollapse.lean`, `RequestProject/Status/AxiomAuditErdos287September4SignedFloorBank.lean`, `RequestProject/Main.lean`. No proved bank was deleted.

NO SORRY: YES. NO CUSTOM AXIOMS: YES (no `axiom`, `@[implemented_by]`, `native_decide`, `unsafe`, `opaque`). LAKE BUILD: PASS.

P0 BUG LOCATED — confirmed exactly as suspected. The September‑4 module models the source as a purely local product `Bsrc Bloc d = ∏_{p|d} Bloc p` with the hypothesis `bloc p − Bloc p = −S₂` at every prime; multiplying that over `primeFactors(q)` inserts the global `S₂` once per prime and necessarily yields `S₂^{ω(q)}·μ(q)`. The theorems are true but describe an artificially locally‑normalised model, not the physical source.
OLD FALSE PHYSICAL THEOREM: RETYPED (nothing deleted). A P0 notice was added, §4.4/§4.5 retitled as the abstract model, and the counterexample renamed `literal_S2_mu_form_fails → abstractLocalNormalisation_S2_mu_form_fails` (its witness uses artificial local values, so it refutes only the over‑general abstract form). Exactly one physical local‑collapse theorem now exists.
CORRECT PHYSICAL DEFINITION: `B0(d)=∏(p−1)/(p−2)`, `B_src(d)=S₂·B0(d)`, `β(d)=∏1/(p−2)`, `λ(b)=∏(p−1)/(p−2)²`, with the typed relation `S₂·B_src(ab)=B_src(a)B_src(b)`.
CORRECT LOCAL COLLAPSE: KERNEL-PROVED — `β(p)−B0(p) = −1` for odd primes (and `= 0` at p=2, which is why oddness is required), hence `∑_{d|q} μ(d)B_src(d)β(q/d) = S₂·μ(q)` for odd squarefree q (`physicalBsrcMobiusCollapse45`).
q=15 REGRESSION: KERNEL-PROVED (`β(15) − B0(3)β(5) − B0(5)β(3) + B0(15) = 1`; divisor sum `= S₂`).
AFFECTED DECLARATIONS: only the four abstract `S₂^{ω(q)}` statements, referenced solely by the axiom-audit `#print axioms`; no physical compiler depended on them, so nothing had to be downgraded. UNAFFECTED BANK REBUILT: PASS.

CORE (all KERNEL-PROVED): coprime Möbius indicator; β/B0/λ multiplicativity and the typed `B_src` relation; λ local factor; exact local coefficient identity `μ(b)μ(bv)B_src(bv)β(bq) = λ(b)μ(v)B_src(v)β(q)`; the central `squarefree_gcd_descent` (stated over an arbitrary coefficient ring hom, with ℚ and ℝ instances), plus `gcd(b,q·v)=1` (with `gcd(q,v)` deliberately unconstrained) and a one-prime cancellation sanity check; phase / W-argument / derivative descent; hyperbola support descent (`0.9` always as exact `9/10`); medium-k exact source normal form (conditional on the finite truncation, no analytic bound claimed); `jointKernel_noLattice` — PROVED, by exact integration by parts, no Euler-summation lemma introduced; repeated-core ledger disjointness and exhaustiveness (no double counting), with the r=1/p²/p³ classification carried abstractly. The strict-endpoint sawtooth convention `ψ(n) = −1/2` is preserved, and the API firewall (only `jointKernel` is a k-consumer) is recorded.

CERTIFICATE — no compact machine certificate was attached, so the five analytic bounds are recorded as EXTERNAL-CERT inputs transcribed as exact rationals; only the arithmetic on them is kernel-checked, and nothing became an axiom.
CERTIFIED SUBTOTAL: 52188738751/10^17 = 5.2188738751e-7.
PRINTED 5.218873872e-7 CONSISTENT: NO — it is strictly smaller than the exact outward sum, short by exactly 3.1e-16, so it is not a valid outward subtotal.
REMAINING CAPACITY: 36417761249/10^17 = 3.6417761249e-7.
PRINTED 3.641776128e-7 CONSISTENT: NO — it overstates capacity by 3.1e-16. Use the corrected value.
The q=3 row (2.17e-8) is recorded as a sub-item of the k ≤ 31 total and proved not to be double-counted.
LARGE-SIEVE CONSTANTS: `∑λ(b)/√b < 7/2` and `∑β(q)² < 241/100` are NOT AVAILABLE (recorded, not kernel-checked); the sawtooth L² mass IS kernel-checked: `(1/q)∑_{a<q}(a/q−1/2)² = (q²+2)/(12q²)` and `≤ 11/108` for q ≥ 3.
q=3 CERTIFICATE: format/checker interface formalised only; the 4.5e9 search is not replayed and the claim is not asserted.
CONDITIONAL BUDGET THEOREM: KERNEL-PROVED, both abstractly and with the audited ledger numbers substituted.

OPEN: medium-k joint Bernoulli — OPEN; two-high a ≤ 180 — OPEN; signed B_src floor — OPEN (all three exist only as predicates); Maynard — NOT ENTERED (no predicate at all); Erdős #287 — OPEN, nothing here claims it.
FIRST EXACT REMAINING NODE: ERDOS287-TOT-BSRC-SQFREE-LATTICEBEARING-MEDIUMK-GCDDESCENT-JOINT-BERNOULLI-DIRECTED45.

`RequestProject/Erdos287/Bank.lean` runs `#print axioms` on every major theorem; each reports exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` and no custom axiom.

# Summary of changes for run caa78c95-832f-4710-8a9b-9cba8bd17ac4
Append-only September-4 signed `B_src` floor bank added. Nothing existing was deleted, edited or downgraded; **Erdős #287 is not claimed**, no Maynard theorem, no numerical Mertens statement and no analytic estimate is asserted. Full report: `ERDOS287_SEPTEMBER4_SIGNED_FLOOR_SAFE_BANK_REPORT.md`.

**Files added** (all under `RequestProject/`): `CurrentProgramme/Erdos287September4PhysicalW.lean`, `…CanonicalStateSign.lean`, `…T0T2DeepEvenCancellation.lean`, `…BsrcLocalMobiusCollapse.lean`, `…BoundaryDivisorLattice.lean`, `…SignedBsrcCompiler.lean`, `…BoundaryCertificateChecker.lean`, `…LargeLTailCompiler.lean`, plus `Status/CurrentStatusErdos287September4SignedFloorBank.lean` and `Status/AxiomAuditErdos287September4SignedFloorBank.lean`; `Main.lean` gained the ten imports.

**Kernel-proved.** Physical W: exact definition with rational break points 7/10, 4/5, 9/10; support ⊆ [7/10,9/10]; W(7/10)=W(9/10)=0, W(4/5)=1; 0 ≤ W ≤ 1; strictly increasing on [7/10,4/5], strictly decreasing on [4/5,9/10]; sup norm `IsGreatest (range W) 1`; **Var(W)=2** in Mathlib's own `eVariationOn` (no bespoke variation notion was invented); hence **C_W = 2‖W‖_∞ + Var(W) = 4** with every term proved; plus the derivative W′ = −20uv²e^{1−v} inside the support. Canonical-state sign invariance κ_ε = μ(d_low)·g_j = (−1)^{ω(d)} = μ(d) with all hypotheses explicit binders (not structure fields), and the one-prime threshold-crossing invariance. The exact T⁰−T² decomposition into the odd family plus the even collar 1_{d ≤ Y(dr) < 2d}, the r = 2u reindexing facts (same n, same κ, same weight, B_src(2m)=B_src(m)), and deep-even cancellation `t0t2DeepEvenCancellation45`, with a firewall theorem witnessing that this is *not* a complete signed-floor closure. Interior divisor-lattice Möbius collapse `interiorLocalMobiusCollapse45` via the local prime-factor identity and multiplicativity over `q.primeFactors` (finite; no infinite Euler product). The exact signed source `R_signed = −4 Σ_{d odd}(E_d[V0,d] − E_d[V2,d])` with −4 *derived* from the two affine sign families times the T⁰−T² comparison sign. Exact rational budget 14164610/10¹⁵ + 985835/10¹² < 10⁻⁶ (sharper pole value kept, slack preserved) and the ordered-field budget compiler. The boundary certificate checker: coverage soundness over 42.9 ≤ L ≤ 62.5, per-box budget check, and the aggregate bound. Tail envelope 9360L(1+L)e^{−L/2} strictly decreasing on [4,∞) and the endpoint decimal envelope(62.5) < 10⁻⁶ proved *inside the kernel* from 7889/6144 ≤ exp(1/4) and 37147500·10⁶ < (7889/6144)¹²⁵ — so both MONOTONICITY and ENDPOINT DECIMAL are kernel-proved, with no numerical socket needed.

**Repair found (§4).** The literally requested identity Σ_{d∣q} μ(d)B_src(d)β(q/d) = S₂·μ(q) is **false** once ω(q) ≥ 2: kernel-proved counterexample q = 15, S₂ = 2, B_loc ≡ 0, β_loc ≡ −2 gives 4, not 2. The correct global form S₂^{ω(q)}·μ(q) is proved, and the requested shape holds exactly under the explicit hypothesis S₂^{ω(q)} = S₂ (in particular on a one-prime fibre). Both forms are stated; nothing was silently reinterpreted.

**Partial / external, as declared.** Boundary datatype BUILT (7 source-native causes, record reconstructing the omitted fibre) and the interior-or-boundary dichotomy kernel-proved, with a firewall counterexample showing the collapse fails on a truncated fibre; physical exhaustiveness of the cause list is PARTIAL and isolated as a stated (unproved) obligation. Secondary pole: analytic residue EXTERNAL / NOT FORMALIZED, only the downstream shoulder implication proved; the socket contains mathematical fields only and no floor conclusion. Compact slab 42.9–62.5 is CONDITIONAL; **no actual numerical certificate exists** (`bankedCertificates = []`), and the domination socket is never inhabited — a single clearly-labelled structural demo with an empty class list only shows the checker is non-vacuous. Mertens interface uninhabited; Maynard socket untouched and uninhabited; numerical E_T not banked; E_T, E_L, global effectivity and Erdős #287 remain open.

**Audit.** `lake build` PASSES (all 8428 jobs, `RequestProject.Main` included). `#print axioms` is run on all 92 principal new declarations: every one reports no axioms or a subset of `propext, Classical.choice, Quot.sound`. No `sorry`/`sorryAx`, no custom `axiom`, no `unsafe`, `native_decide`, `implemented_by`, `opaque` or `skipKernelTC` in any new file; no lint warnings in the new files. The status ledger, its firewalls and its row-backing theorems are machine-checked. First exact remaining node: the boundary numerical certificate (no event-box data for 42.9 ≤ L ≤ 62.5, and no inhabitant of the domination input). All work committed and pushed.

# Summary of changes for run eccaa4cc-2cfa-4ca3-b6aa-a412e582fb3d
All requested September-3 work is complete, append-only, and building. Nothing existing was deleted, rewritten, or weakened; Erdős #287 is **not** claimed and stays open.

**Priority A — 24-window finite extension: KERNEL-PROVED.**
No pre-existing Lean draft or certificate data for the interval `4000000001 … 67108856338751594` was in the repository, so the chain was reconstructed and is now replayed entirely in the kernel:
- `RequestProject/CurrentProgramme/Erdos287September3PrattEngine.lean` — a recursive (Pratt/Lucas) primality-certificate engine: a fuel-driven binary modular exponentiation `powMod` with a **proved** correctness theorem, and `Erdos287.Pratt.prime_of_certificate`. This was necessary because trial division cannot reach the ~10^16 primes the new windows need.
- `…Erdos287September3PrattCertificateBank.lean` — 72 leaf primes (`norm_num`, all `< 10^9`) plus **52 recursive Pratt certificates**, bottom-up, up to `33554428169375797`. No oracle, no `native_decide`.
- `…Erdos287September3FiniteExtension24Window.lean` — the **24 contiguous windows** (`L_{i+1} = U_i + 1`, no gaps) and `Erdos287.Gap2CE.no_of_M_le_extendedCeiling`, `Erdos287.no_Erdos287Counterexample_of_max_le_extendedCeiling` — the *same* predicates and interval blocker as the existing 4·10^9 bank, with the ceiling extended to exactly **67108856338751594**; plus `arithmeticCoverage_exceeds_twoExp375 : 38643198608805673 < extendedCeiling`. Firewall recorded: this is finite arithmetic only and does not close the medium analytic branch.

**Priority B — 2-adic Möbius pairing: KERNEL-PROVED.** `…Erdos287September3TotTwoAdicMobiusPairing.lean`: `μ(2a) = −μ(a)` for odd `a`, the canonical coefficients `kappaEps`/`sigmaEps`, the exact odd-divisor source identity `oddDivisorTotSourceIdentity` (stated before any triangle inequality, with the two pairing equations as explicit hypotheses, discharged for the canonical coefficient), the split `totLaneSourceSplit : T = T⁰ − T²` for supplied weights, and an algebraic witness that a termwise triangle bound destroys the `μ(a)/μ(2a)` cancellation.

**§3 fixed-residue arithmetic: KERNEL-PROVED.** `…Erdos287September3TotFixedResidueArithmetic.lean`: `p = 2dr+s ⇒ p ≡ s (mod d)`, `p = 4du+s ⇒ p ≡ s (mod 4d)`, and the converse integrality `p ≡ s (mod d), p odd, d odd, s = ±1 ⇒ 2d ∣ p − s` (parity hypotheses not weakened). Firewall: fixed-residue source ≠ analytic prime-distribution theorem.

**§5–§6 conditional compiler.** `…Erdos287September3TotFixedResidueConditionalCompiler.lean`: an **uninhabited** external AP socket exposing residue, modulus (`q1·d`, `q1 ∈ {1,4}`), finite interval endpoints, prime discrepancy, numerical error function/bound and activation threshold — with no endpoint-supremum field and no stored `E_T` conclusion — and the implication-only `totLaneFixedResidueConditionalBound45`, with the slot index `D ×ˢ {1,4} ×ˢ {−1,+1}` (four slots per modulus: two signs once, two families once).

**Priority C (optional): KERNEL-PROVED.** `…Erdos287September3CanonicalSplitFourInterval.lean`: abstract monotone crossing lemma, two thresholds per window, coefficient = signed sum of ≤ 4 interval indicators, with the numerical exponent content isolated and computed exactly (`d ≤ n^(1/2) ↔ d² ≤ n`).

**Status/audit/report.** Added `RequestProject/Status/CurrentStatusErdos287September3SourceBank.lean` (append-only ledger with the requested rows, firewall theorems and five rows backed by the theorems they label) and `…/AxiomAuditErdos287September3SourceBank.lean`; `RequestProject/Main.lean` gained the nine imports; full details in `ERDOS287_SEPTEMBER3_FINITE_AND_2ADIC_SAFE_BANK_REPORT.md` (window table, certificate counts, firewalls, axiom summary). The generator scripts are in `scripts/` and are untrusted — every statement they produce is re-proved by the kernel.

STRICT OUTPUT — 24-WINDOW FINITE CHAIN: KERNEL-PROVED · FINITE CEILING: 67108856338751594 · COVERS ceil(2 exp(37.5)): KERNEL-PROVED · 2-ADIC MÖBIUS PAIR: KERNEL-PROVED · ODD-DIVISOR TOT SOURCE: KERNEL-PROVED · d FIXED-RESIDUE: KERNEL-PROVED · 4d FIXED-RESIDUE: KERNEL-PROVED · TOT SOURCE SPLIT T0-T2: KERNEL-PROVED · CANONICAL FOUR-INTERVAL: KERNEL-PROVED · AP ANALYTIC SOCKET: UNINHABITED · ENDPOINT-SUPREMUM ASSUMED: NO · MAYNARD THEOREM ASSERTED: NO · CONDITIONAL E_T COMPILER: KERNEL-PROVED (implication only) · NUMERICAL E_T: NOT BANKED · E_L: OPEN/CONDITIONAL · GLOBAL EFFECTIVITY: OPEN · ERDOS287: OPEN · LAKE BUILD: PASS (8418 jobs) · SORRY/SORRYAX: NONE · NEW CUSTOM AXIOMS: NONE (all new declarations use only propext / Classical.choice / Quot.sound or fewer) · OVERCLAIM AUDIT: PASS.

# Summary of changes for run f7a1242f-400f-4a54-b51d-ff89318e9bd0
## What was added (append-only; nothing existing was deleted or rewritten)

**New Lean modules**

- `RequestProject/CurrentProgramme/Erdos287September2TaggedTwoLaneSource.lean` — the tagged two-lane source `RawIndex = ({tot} × TotDiscIndex) ⊎ ({u} × UDiscIndex)`: lane dichotomy, fibre disjointness, finite census split, equivalence with the plain disjoint union, the algebraic lane-split identity for supplied weights, the recorded (external) intended semantics `tot ↦ T_X`, `u ↦ L_X`, the explicit witness that **source-tag disjointness is not physical n-support disjointness**, and the selected-E **typing guard** (the Tot occurrence type has no selected-E field, so no constructor can attach it).
- `RequestProject/CurrentProgramme/Erdos287September2OneSlotPerron.lean` — `c = X⁻²⁰⁰`, `T = X²⁰⁰`, `T/c = X⁴⁰⁰`; the one-slot Perron mass bound `(1/π)·arsinh(X⁴⁰⁰) < 128·log X` for `X ≥ 3`; `⌈1/(1−γ)⌉ = 2` for `γ = 1/2 − 5·10⁻²²`; `N = kℓ + r + s ≤ 112` (sharp) with `ℓ = 12`, `k ≤ 6`, `r,s ≤ 20`; nonempty coordinate subsets `≤ 2¹¹² − 1`, plus the record that this ceiling is not an effectivity closure.
- `RequestProject/CurrentProgramme/Erdos287September2LedgerAdaptersAndCompilers.lean` — the typed Perron/nuclear ledger socket and the hard-U → shared-Ford literal source-equality socket (**both left uninhabited**, with firewalls: the ledger contract is a genuine constraint and does not store its conclusion; the selected-E clause of the adapter certificate is load-bearing); the direct-provider / b-diagonal **conditional** bypass with an unasserted antecedent; the conditional `E_L` bound; `C_pair = 11`; the renamed generic lemma and the genuine survival bridge (below); `2·X_N2 > 4·10⁹`; the four-error algebraic interface with its budget-is-an-input firewall.
- `RequestProject/Status/CurrentStatusErdos287September2TwoLaneMaster.lean` (18-node later status layer, §0 vocabulary, firewalls, five rows explicitly backed by the theorems they label) and `RequestProject/Status/AxiomAuditErdos287September2TwoLaneMaster.lean` (`#print axioms` on every principal declaration). `RequestProject/Main.lean` gained the five imports. Report: `ERDOS287_SEPTEMBER2_TWO_LANE_MASTER_SAFE_BANK_REPORT.md`.

## Requested semantic correction (done)

- The old generic lemma is renamed **`fourLossSurvivalPositivity`** and documented as real arithmetic only, explicitly *not* a sieve-survival bridge.
- The genuine **`PrimePairSieve.primePairSieveSurvival45`** was added over the banked window data (`Q = X/(2M)`, `I(M) ⊆ (Q,2Q]`, `H = |I(M) ∩ ℤ| ≤ Q+1`, `z = H^(49/100)`, long sector `H − 1 > H^(49/100)`), with the finite chains `q > Q ≥ H − 1 > z` and, for `s = ±1`, `M ≥ 1`, `2Mq + s ≥ 2Mq − 1 > q > z`, and the exact consequence: if `q` and `n = 2Mq + s` are both prime then neither is divisible by any prime `p < z` — every simultaneous-prime pair survives the z-sieve. The window hypotheses are proved consistent (so the bridge is non-vacuous), and a firewall records that surviving the z-sieve is strictly weaker than primality. No Bordignon–Lee analytic sieve theorem is formalized or asserted.

## Audit finding (statement corrected, original recorded)

The requested chain `asinh(X⁴⁰⁰) < log(2X⁴⁰⁰) < 401 log X` has a **false first step**: since `√(1+t²) > t`, one always has `arsinh t > log(2t)`. This negation is kernel-proved as `arsinh_gt_log_two_mul`; the chain was repaired via `√(1+t²) ≤ (3/2)t`, giving `arsinh t ≤ log(5t/2) < 401 log X` for `X ≥ 3`, and hence the intended conclusion `< 128 log X` (using `401 < 128π`) unchanged.

## STRICT OUTPUT

```
TWO-LANE TAGGED SOURCE:        KERNEL-PROVED
SELECTED-E TYPE FIREWALL:      KERNEL-PROVED
ONE-SLOT PERRON:               KERNEL-PROVED (chain repaired; false step recorded)
N<=112 ARITHMETIC:             KERNEL-PROVED
COMPLETE PERRON LEDGER:        UNINHABITED
E_T:                           PAPER_CLOSED_EXTERNAL
HARD-U SHARED-FORD ADAPTER:    UNINHABITED
E_L:                           CONDITIONAL / OPEN
b-DIAGONAL BYPASS:             CONDITIONAL (antecedent not asserted)
E_M:                           PAPER_CLOSED_EXTERNAL
N2 (analytic lane):            PAPER_CLOSED_EXTERNAL
PRIME-PAIR-SIEVE-SURVIVAL45:   KERNEL-PROVED (elementary inclusion bridge only)
CURRENT N2 FINITE SPLICE:      FAIL (2·X_N2 > 4·10⁹ kernel-proved)
FOUR-ERROR ASYMPTOTIC FCL:     CONDITIONAL
GLOBAL EFFECTIVITY:            OPEN
ERDOS287:                      OPEN
TWIN/HSTAR CONTAMINATION:      NONE (no such import or dependency)
LAKE BUILD:                    PASS (8409 jobs, 0 errors, no new warnings)
SORRY / SORRYAX:               NONE
CUSTOM AXIOM / unsafe / native_decide / implemented_by / skipKernelTC: NONE
AXIOMS OBSERVED:               propext, Classical.choice, Quot.sound (or fewer)
OVERCLAIM AUDIT:               PASS
INDEPENDENT CHECKER/COMPARATOR: NOT RUN (not claimed)
```

The Properties table was updated with the new deliverables (all listed theorems marked proved; the two sockets and the status ledger recorded as definitions).


# Summary of changes for run cfae4aad-f6af-42fa-acec-226300b76646
Paused as requested — no new proof work was started this round, and no file in the project was changed (the working tree is clean and identical to the state you handed over; all reports, including the last round's, are untouched on disk).

What I did: cleared the Run1B (d*wp / Fourier provider) entries out of the Properties table so it tracks only #287 material. Fourteen entries were removed, covering the whole 1B layer:

- effective-modulus layer: the gcd(A♯, r♯) coprimality fact and the effective-modulus reciprocal-phase identity;
- finite Fourier matrix: row orthogonality and the operator-norm statement;
- small-modulus Fourier: Parseval, the L¹ ≤ √n·L² bound, and the small-modulus compiler;
- residue-class energy: the bilinear L² bound and the class-multiplicity bound;
- large-modulus contraction compiler;
- the Möbius polyphase input, the d*wp source type, the source-exhaustive router inhabitation, and the conditional 1B compiler.

What I deliberately kept in the table (these are #287-side, not 1B): the N2 effective-constants results (`two_XN2_exceeds_finite_bank`, the Ω_H provenance fact), the shared other-parent adapter items (`adapters_are_independent`, `hardU_adapter_uninhabited_in_general`, `sharedOtherParent_conditional`, the hard-U adapter obligation), the September-2 status ledger, and everything from earlier rounds. Their recorded statuses are unchanged (the previously proved ones are still marked proved).

Nothing about Erdős #287 is claimed as solved, and no statement in the project was weakened, added, or removed. Ready to resume on the #287 top-layer / prime-power exclusion package whenever you want.

# Summary of changes for run 19101e0d-5031-4f91-ad0d-92d8927699d7
## Work completed this session

The append-only safe bank was resumed from the complete repository; historical files and statuses were preserved, nothing was deleted or restated. The remaining items — a full re-verification of the build and the axiom audit, and completion of the user-facing Properties table for the new package — are now done. No new `sorry`, `axiom`, `unsafe`, `native_decide`, or `implemented_by` occurs anywhere in the new modules.

### Files added in this task (all under `RequestProject/`)
`CurrentProgramme/Run1BAdditiveCharacters.lean`, `Run1BDwpSourceType.lean`, `Run1BEffectiveModulus.lean`, `Run1BFiniteFourierMatrix.lean`, `Run1BResidueClassEnergy.lean`, `Run1BLargeModulusCompiler.lean`, `Run1BSmallModulusFourier.lean`, `Run1BCenteringAndSourceRouter.lean`, `Run1BConditionalCompiler.lean`, `NeutralFordSharedOtherParent.lean`, `Erdos287N2EffectiveConstantsBank.lean`; `Status/CurrentStatusErdos287September2Frontier.lean`, `Status/AxiomAuditErdos287September2Frontier.lean`; imports added in `Main.lean`; report at `ERDOS287_RUN1B_DWP_PROVIDER_SEPTEMBER2_SAFE_BANK_REPORT.md`.

### STRICT FINAL OUTPUT (RUN1B d*wp provider layer)

- LAKE BUILD: **PASS** (8404 jobs)
- NEW WARNINGS: **NONE** (5 pre-existing unused-variable warnings only, in older files)
- EFFECTIVE MODULUS IDENTITY: **KERNEL-PROVED** (`eAdd_effective_modulus_inverse`, `gcd_ASharp_rSharp`)
- FOURIER MATRIX ORTHOGONALITY: **KERNEL-PROVED** (`Kmat_row_orthogonality`, `Kmat_operator_norm_sqrt`, normalisation explicit: unnormalised kernel, operator norm √rSharp)
- LARGE-rSHARP COMPILER: **CONDITIONAL KERNEL-PROVED** (`largeModulus_contraction`, from `bilinear_l2_bound` + class-multiplicity bounds)
- SMALL-rSHARP FOURIER: **KERNEL-PROVED** (`fourier_inversion`, `fourier_parseval`, `fourier_l1_le_sqrt_l2`, `recipPhase_expansion`)
- MOBIUS POLYPHASE INPUT: **PAPER-CLOSED EXTERNAL** (explicit input structure; proved to be a genuine, non-vacuous constraint)
- d*wp PROVIDER: **PAPER-CLOSED EXTERNAL** (never labelled kernel-proved; the source record provably does not carry the contraction as a field)
- RUN1B SOURCE EXHAUSTIVE INPUT: **INHABITED** (finite seven-class router: total, deterministic, surjective)
- RUN1B FINAL STATUS: **PAPER-CLOSED EXTERNAL** analytic provider + **CONDITIONAL KERNEL-PROVED** compiler
- ULTRA-NEAR-HALF: **OPEN EXTERNAL**
- SHARED OTHER: **CONDITIONAL**
- TWIN ADAPTER: **CONDITIONAL**; ERDOS287 ADAPTER: **CONDITIONAL**, its source-equality obligation **UNINHABITED in general** (proved)
- TWIN PRIME: **OPEN**; ERDOS287: **OPEN**
- SEMANTIC FAILURES: **NONE FOUND** — counterguards proved for: no desired conclusion inside an Input field, no projection-only theorem mislabelled, no True-like propositions, adapters mutually non-importing
- CUSTOM AXIOM: **NONE**; SORRYAX: **NONE** (99 `#print axioms` checks report only `propext` / `Classical.choice` / `Quot.sound`, or no axioms at all)
- OVERCLAIM AUDIT: **PASS**

### September-2 frontier status layer

One authoritative ledger over 29 nodes with statuses KERNEL_PROVED / PAPER_CLOSED_EXTERNAL / CONDITIONAL_KERNEL / STRICTLY_REDUCED_OPEN / OPEN_EXTERNAL / EFFECTIVITY_OPEN / SUPERSEDED. Recorded and machine-checked: N2 constants bank with `2·X_N2 ≤ 4·10⁹` **FALSE** (finite splice does not close); Ω_H provenance **UNRESOLVED** with no silent default; b-diagonal downgraded to **STRICTLY REDUCED OPEN**; Gate 1A **off the critical path** and absent from the dependency graph; effectivity rows **OPEN** (M₀ within the finite bank **NOT PROVED**); external validation (independent checker, comparator) recorded as **NOT RUN** rather than assumed passed. Erdős #287 and Twin Prime remain **OPEN** in the ledger, and firewall theorems prevent any status row from being read as a proof claim.

STOP.

# Summary of changes for run 654de260-4ec4-4d9f-a379-22b63d68b029
All work is append-only, committed and pushed. No historical file was deleted or rewritten; no external analytic theorem was proved; no source/analytic socket was inhabited; Erdős #287 is **not** claimed.

## Files added

**287A / shared-other45 addendum**
- `RequestProject/CurrentProgramme/Erdos287SharedOtherRawArchitecture.lean` — dependent raw packet `RawPacket X = RawDataTot X ⊕ RawDataU X`; the Tot-constructor exclusion firewall (no `k`, `J`, HB leaves, `𝓔`, `E*`, shared `gcd`, `Δ`) both as a field-name disjointness fact and as the semantic "no hidden data" theorem; the U constructor carrying exactly `k`, `J`, literal HB grammar, `𝓔`, deterministic `E* = E*(𝓔)`, `u`/`v`, dyadic/Perron skeleton, source signs; exact generated coefficients `A_η(a;τ)`, `B_η(b;τ)`; the determinant line `rq − 2ab = s` with `b = b₀+rℓ`, `q = q₀+2aℓ` (invariance, forward and exact converse) plus the census determinant `ℓq − (πzy)c = 2`; the centred two-copy identity `|S|² = PP̄ − PM̄ − MP̄ + MM̄`; exact coefficient preservation.
- `RequestProject/CurrentProgramme/Erdos287SharedOtherConductorAndSocket.lean` — proof-local conductor/shared-gcd data indexed by *two* copies (`q_i = g_i d_i`, `h_i = d_i t_i`, `e = gcd(g₁,g₂)`, `g_i = e n_i`, `Δ = t₁n₂ − t₂n₁`), coprimality of the reduced factors; the Δ-router (routing only) with three exact biconditionals, totality/uniqueness and a "routing only" witness; `Ford722OtherParentGeneratedUniformityInput`, uninhabited, whose contract is stated in the generated `(A_η, B_η)` and carries the newest census metadata (prime extraction `m = πz`, complement opening `n = yc`, census determinant, `d ≥ 3` two-atom `4/9` router, coarse depth exactly 2, two distinct linear HB f-leaf atoms, coefficient pattern); the `k = 0` `β_g` firewall showing that profile does not determine `A_η`.
- `RequestProject/CurrentProgramme/Erdos287SharedOtherAdaptersAndCompiler.lean` — the finite/source portion of the Tot reconstruction; the Type-I socket whose conclusion is exactly `E_T = o(X/log X)` (`E_T` closure is derived only from it, and the `o(X/log X)` predicate is shown non-automatic); `SharedOtherParentInput → E_L bound`; the two mutually independent adapters `TwinOtherParentAdapter` (parametric, never inhabited here) and `Erdos287HardUAdapter` (discharged from the shared input alone); the conditional asymptotic FCL from the shared source together with the paper-closed `E_T`, `E_2`, `E_M` inputs.
- `RequestProject/Status/CurrentStatusErdos287SharedOtherFrontier.lean` and `RequestProject/Status/AxiomAuditErdos287SharedOtherFrontier.lean` — the new status layer (strictly later than every earlier layer, earlier ledgers re-checked in place) and its axiom audit.

**Completion of the preceding two-lane layer** (was in flight): `Erdos287TwoLaneMasterCompilerV2.lean` (its tautological owner field repaired into genuine supplied data plus an agreement pin), `Erdos287HeathBrownSourceRecords.lean`, `Erdos287N2FiniteSublemmas.lean`, `CurrentStatusErdos287TwoLaneFCLFrontier.lean`, `AxiomAuditErdos287TwoLaneFCLFrontier.lean`.

`RequestProject/Main.lean` gained the corresponding imports. Report: `ERDOS287_SHARED_OTHER45_ADDENDUM_REPORT.md`.

## Leanify / repair
Twenty-eight pre-existing linter warnings were fixed at the root — unused `simp` arguments removed across `TopLayer`, `Cnum`, `Window`, `Blocker`, `BadPrimes`, `SFTAudit`, `CeilingCRT`, `FixedCertificateSmoothParity`, `SemanticFirewallsErdos287`; one genuinely unused hypothesis dropped from `topExp_le_one_of_lt_sq` (and its call site updated); two unused lambda binders replaced. No linter was disabled and no `nolint` added. The five remaining warnings are the deliberately kept, docstring-documented hypotheses that the original problem statements request but the proofs do not need.

## Strict final output
```
LAKE BUILD:                 PASS
JOB COUNT:                  8391
NEW WARNINGS:               NONE (28 pre-existing repaired; 5 documented intentional remain)
SORRYAX:                    NONE
CUSTOM AXIOM:               NONE
AXIOMS OBSERVED:            propext, Classical.choice, Quot.sound (and subsets)
DEPENDENT RAW PACKET:       PASS
TOT EXCLUSION FIREWALL:     PASS
DETERMINANT LINE:           KERNEL-PROVED
CENTRED TWO-COPY IDENTITY:  KERNEL-PROVED
COEFFICIENT PRESERVATION:   KERNEL-PROVED
CONDUCTOR / SHARED-gcd:     KERNEL-PROVED
DELTA ROUTER:               KERNEL-PROVED (routing only)
TYPE-I E_T SOCKET:          PAPER-CLOSED EXTERNAL / UNINHABITED
N2 LAMBDA-COLLAR SOCKET:    PAPER-CLOSED EXTERNAL / UNINHABITED
BSRC / N1 / E_M SOCKET:     PAPER-CLOSED EXTERNAL / UNINHABITED
FORD 7.22 HARD-U SOCKET:    OPEN EXTERNAL / UNINHABITED
POSITIVE MARGIN SOCKET:     UNINHABITED
E_L COMPILER:               KERNEL-PROVED CONDITIONAL
TWO ADAPTERS:               KERNEL-PROVED, MUTUALLY INDEPENDENT
ASYMPTOTIC FCL:             KERNEL-PROVED CONDITIONAL
EFFECTIVITY SOCKET:         UNINHABITED
Erdos287ClosureInputs:      UNINHABITED
ERDOS287:                   OPEN
FIRST FORMAL RESEARCH SOCKET:
  Erdos287.SharedOtherParent.Ford722OtherParentGeneratedUniformityInput
PROOF CLAIM CERTIFIED:      NO
```
STOP.

# Summary of changes for run 31b168b4-a9c5-44cd-b8a1-9b3f442a08ab
Appended the full analytic-kernel import frontier as a new, strictly later status layer. Nothing was rewritten or deleted: all historical files and status layers are preserved. **Erdős #287 is NOT claimed proved**, no external analytic theorem was formalized or manufactured, and no analytic estimate was inhabited by axiom.

## Files added (append-only)
- `RequestProject/CurrentProgramme/Erdos287FullSourceAnalyticKernelInput.lean` — the typed external analytic input.
- `RequestProject/CurrentProgramme/Erdos287MasterSourceTypedPerronPackets.lean` — the compiler chain, de-regularisation identity, owner type and owner partition.
- `RequestProject/CurrentProgramme/Erdos287OneBoundedSourceFactor.lean` — the algebraic one-bounded `A·B` factorisation.
- `RequestProject/CurrentProgramme/Erdos287DeterminantOneCompiler.lean` — `rq − 2ab = s` → `b = b₀ + rt`, `q = q₀ + 2at`.
- `RequestProject/CurrentProgramme/Erdos287TwoCopyRouterAndOmega.lean` — the `Δ`-router and the proof-local shared-gcd `Ω` partition.
- `RequestProject/CurrentProgramme/Erdos287FullAnalyticKernelFCLChannels.lean` — analytic input → correlation bound, physical source pin, the four FCL error channels, reuse firewalls.
- `RequestProject/Status/CurrentStatusErdos287FullAnalyticKernelImportFrontier.lean` — the new layer `fullAnalyticKernelImportFrontier`.
- `RequestProject/Status/AxiomAuditErdos287FullAnalyticKernelImportFrontier.lean` — `#print axioms` on every principal new theorem.
- `RequestProject/Main.lean` — the eight new imports appended.
- `ERDOS287_FULL_ANALYTIC_KERNEL_IMPORT_FRONTIER_SAFE_BANK_REPORT.md` — the written report.

## STRICT FINAL REPORT
```
LAKE BUILD:            PASS
JOB COUNT:             8370
NEW WARNINGS:          none in the new modules (older files unchanged)
SORRYAX:               none
CUSTOM AXIOMS:         none — 87 audited new declarations depend only on
                       [propext, Classical.choice, Quot.sound] or a subset;
                       11 depend on no axioms at all
FULL ANALYTIC KERNEL:  EXTERNAL / PAPER-BANKED
ANALYTIC INPUT:        UNINHABITED (refutable at explicit data; proved not
                       derivable from the finite/source combinatorics)
MASTER-SOURCE-TO-TYPED-PERRON-PACKETS45: KERNEL-PROVED source/formal compiler
OWNER PARTITION:       PASS (exactly six owners; one owner per packet; no two
                       owners; disjoint, exhaustive; exact reassembly; Ω only
                       after two copies)
DET1 COMPILER:         PASS (shift, coprimality, exhaustiveness, uniqueness)
TWO-COPY ROUTER:       PASS (exhaustive + disjoint on Δ = t₁n₂ − t₂n₁)
PROOF-LOCAL OMEGA:     PASS (1 = Σ_H Ω_H(gcd(g₁,g₂)); genuine two-copy coordinate)
PHYSICAL P/N1/N2/U:    SOURCE-PIN OPEN (typed interface + adapter proved; the
                       pin predicate is uninhabited — nothing invented)
E_T / E_L / E_2 / E_M: DEFINED (only their combination identity is proved)
FCL:                   OPEN (budget inequality is an explicit, unconstructed input)
FCL→WINDOWPAIR:        KERNEL-PROVED CONDITIONAL (reused, not duplicated)
EFFECTIVE WINDOWPAIR:  UNINHABITED (asymptotic kept distinct; M₀ ≤ 4·10⁹ retained)
ERDOS287:              OPEN
FIRST EXACT FORMAL/SOURCE RESIDUAL: the literal physical fixed-certificate
                       source pin (then the FCL channel budget) — NOT the
                       regular-Perron analytics
PROOF CLAIM CERTIFIED: NO
STOP.
```

Scans of the new code found no `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe`, `opaque` or `implemented_by`. The metadata firewalls (`no_row_is_a_proof_claim`, `analyticBanked_is_not_kernelProved`) are themselves machine-checked, so no status value carries a proof implication. All work is committed and pushed.

# Summary of changes for run c64ebf2a-a8c0-42c5-93a9-1a12c55266a0
Append-only bank added; nothing existing was deleted, renamed or weakened. The only edit to a pre-existing file is ten new `import` lines at the end of the import block of `RequestProject/Main.lean`.

STRICT FINAL REPORT
```
LAKE BUILD:                      PASS   (full `lake build`, 8362 jobs, 0 errors)
NEW JOB COUNT:                   10     (8352 → 8362)
SORRYAX:                         NONE
CUSTOM AXIOMS:                   NONE
UNSAFE:                          NONE
opaque / native_decide /
  implemented_by / admit:        NONE
K0-SP2 SOURCE PARTITION:         KERNEL-PROVED
UNIFORM FRAGMENTATION SOURCE
  COMPILER:                      KERNEL-PROVED SOURCE/COMBINATORIAL (re-checked, unchanged)
REGULAR PERRON PARENT INTERFACE: DEFINED
REGULAR PERRON ANALYTIC INPUT:   UNINHABITED
FCL→WINDOWPAIR:                  KERNEL-PROVED CONDITIONAL
EFFECTIVE WINDOWPAIR:            UNINHABITED
ERDOS287:                        OPEN
PROOF-CLAIM CERTIFIED:           NO
FIRST OPEN ANALYTIC NODE:        287-K0-SP2-REGULAR-PERRON-SMOOTH-MOBIUS-CORRELATION45
```
Every principal new theorem was checked with `#print axioms`; each reports `[propext, Classical.choice, Quot.sound]` or "does not depend on any axioms". The audit is banked as a Lean file, so it re-runs on every build.

FILES ADDED
- `RequestProject/CurrentProgramme/Erdos287K0SP2SourceObject.lean` — the exact source object: greatest prime factor P⁺, the parameter package (σ*, γ* as rationals, conditions written in equivalent integer-power form so everything is decidable), the audited finite set S_X = {n : X/2 < n ≤ X, P⁺(n) ≤ n^σ*}, the truncated Möbius coefficient M_γ, and the two-sign source with W and D_s as explicit parameters. Finite identities: two-sign expansion, sector additivity, four-sector reassembly.
- `RequestProject/CurrentProgramme/Erdos287K0SP2FourClassPartition.lean` — `k0SP2_fourClass_partition_exact` (six disjointness statements, union = source, no row with two owners) with the regular complement defined by exact set difference, plus the exact source-level reassembly identity.
- `RequestProject/CurrentProgramme/Erdos287RepeatedBalanced7FiniteArithmetic.lean` — the divisor-count identity, via a genuine bijection between the divisors of a squarefree row and the subsets of its prime support: `depthMoebius_eq_alternating`, `depthMoebius_three_eq_Hrepeat`, `depthMoebius_three_eq_neg_choose` (= −C(r−1,3)), and the table 7↦−20, 6↦−10, 5↦−4, 4↦−1, 1≤r≤3↦0. The X^(6/7) count is kept as a named external input, uninhabited.
- `RequestProject/CurrentProgramme/Erdos287RegularPerronParent.lean` — the abstract regular-parent coefficient interface (support + Euler reconstruction fields, no complex exponentiation needed); `RegularPerronSmoothMobiusCorrelationInput` as an explicit fixed-budget inequality, left uninhabited; separate `PerronMainInput` / `PerronBoundaryInput` / `PerronTruncationInput` and the purely algebraic reconstruction schema.
- `RequestProject/CurrentProgramme/Erdos287RegularTemplateReassembly.lean` — a finite, scale-independent template index with the pointwise parent identity, `template_correlation_reassembly` (∑_π C_{s,π} = C_s^reg for every finite row set), the triangle-inequality firewall counterexample, and `Cfrag = 0` as metadata only.
- `RequestProject/CurrentProgramme/Erdos287Balanced7ScopeAndCauchyFirewall.lean` — scope classifier, the explicit seven-box adapter, `genericAdapter_uninhabited`, refutation of "same shape ⇒ owner"; and the first-Cauchy firewall (linear small-prefix factorisation recorded structurally, algebraic sign-consumption identities proved, analytic insufficiency recorded as metadata).
- `RequestProject/CurrentProgramme/Erdos287FCLErrorStrengthFirewall.lean` — `ArbitraryLogSaving` vs `FixedRelativeSaving`, their separation, and a re-export showing the finite FCL compiler's statement contains no all-A hypothesis.
- `RequestProject/CurrentProgramme/Erdos287FCLWindowPairBridge.lean` — `windowPairSupply_of_positiveFCLMass`: for M ≥ 20 and X = M/2, a prime q in the support (7M ≤ 20q ≤ 9M) with 2q ± 1 = r^a yields every literal field of `WindowPairSupply M` in both the plus case (x = 2q) and the minus case (x = 2q − 1). Non-vacuity is checked at M = 20 (q = 7, 2q − 1 = 13). Also the effectivity firewall separating a real "sufficiently large" threshold from a bounded Nat threshold.
- `RequestProject/Status/CurrentStatusErdos287RegularPerronSourceFrontier.lean` — the new authoritative layer `regularPerronSourceFrontier`, proved strictly later than `dualLevelSimultaneousCritical`; earlier layers retained by precedence, not deletion.
- `RequestProject/Status/AxiomAuditErdos287RegularPerronSourceFrontier.lean` — `#print axioms` on every principal new theorem.
- `ERDOS287_REGULAR_PERRON_SOURCE_FRONTIER_SAFE_BANK_REPORT.md` — the full report.

ONE CORRECTION TO THE REQUESTED CONTENT
The requested coefficient row "r ≤ 3 ⇒ 0" is false at r = 0: the empty row is n = 1, where the depth-3 truncated Möbius sum is μ(1) = 1. The banked table therefore reads `1 ≤ r ≤ 3 ⇒ 0`, and the r = 0 value is recorded explicitly as `depthMoebius_three_one : depthMoebius 1 3 = 1`. All other requested rows (7 ↦ −20, 6 ↦ −10, 5 ↦ −4, 4 ↦ −1) are exactly as stated.

EXPLICIT NON-CLAIMS
Erdős #287 is not proved and nothing here asserts it. No external analytic estimate is inhabited, no arbitrary-L^{-A} theorem is formalised, the FCL→WindowPair bridge is strictly conditional on an input that is never constructed, and all status values are metadata with no mathematical force.

# Summary of changes for run 61bb0102-8544-4b83-abe8-8751c37038f1
Both requested append-only layers are now banked, building and audited.  Nothing was deleted, renamed, weakened or rewritten; the only change to an existing file is the appending of eighteen `import` lines to `RequestProject/Main.lean`.

## Layer A — semantic repair + super-square-root frontier

New files under `RequestProject/CurrentProgramme/`: `Erdos287StrictCellSemanticRepair.lean`, `Erdos287RepeatedPrimePhysicalSource.lean`, `Erdos287WeightedSP2PhysicalSource.lean`, `Erdos287PhysicalBComparisonV2.lean`, `Erdos287PhysicalBridgeV2.lean`, `Erdos287CenteredQCellPhysical.lean`, `Erdos287Supersqrt3221Dictionary.lean`, `Erdos287SupersqrtAnalyticInterface.lean`; status/audit files `RequestProject/Status/CurrentStatusErdos287SupersqrtFrontier.lean` and `AxiomAuditErdos287SupersqrtFrontier.lean`; report `ERDOS287_SUPERSQRT_SEMANTIC_REPAIR_SAFE_BANK_REPORT.md`.

Content: `hStar` classified as a combinatorial surrogate with a separately typed, uninhabited `FordHPhysicalBinding` and the conditional value −20; strict-collapse classified as an abstract certificate with a physical binding kept explicit; the full weighted slot source `ω^phys_i(p) = sp2Omega·V_i(p/Y)·exp(i t_i log p)` reusing the repository `omegaBox`, with its exact support identity and an exact weighted integer pushforward (no `Ω♯ = 1` assumed); the repeated-prime sector included exactly (`Hrepeat r = −C(r−1,3)`, giving −20/−10/−4/−1/0) with the old weight-zero routing shown to change the total mass; the finite `Bsrc(S₂,P)` with `0 < Bsrc < 128`; V2 B-comparison interfaces carrying both `Cerr` and `z₀`, with old ⇒ V2 proved and the converse refuted; the exact centered q-cell, character orthogonality and seven-slot character product; the literal 2+5 split, the inverse-sampled 3221 dictionary, the five-box factorisation and outer finite norms; the sign-blind first-Cauchy firewall; and a super-sqrt data object with a one-field analytic interface left uninhabited.

## Layer B — fixed-budget V22 / FCL / effectivity firewall

New files: `Erdos287FixedBudgetV22Arithmetic.lean` (`Cvar(1) = 5`, `CextStar = 9/4`, `2·CextStar < 5`, `netLogExponent = −5/4 < −1`, plus the exact break-even at `5/2`), `Erdos287FixedDCutoffRepair.lean` (source-exact fixed cutoff at `D = log X`, `B0 = 1`; valid adapter from the stronger banked interface, converse refuted), `Erdos287FixedBudgetPhysicalWrapper.lean` (uninhabited physical wrapper and its conditional closure compiler), `Erdos287AllAFirewall.lean` (fixed-budget vs arbitrary-`A` correlation inputs; all-A ⇒ fixed proved, fixed ⇏ all-A refuted), `Erdos287FCLAlgebraicBridge.lean` (generic scaling bridge `B ≥ cB·X/log X`, `E ≤ cE·X/(log X)^{1+η}`, explicit threshold ⇒ `E ≤ δ·B`, feeding the banked positivity compiler; margin firewall with `δ = (1+Cc)/6`, `3δ < 1+Cc`; `N2` slack kept strictly additive), `Erdos287WindowPairExportEffectivity.lean` (complete window-pair export dictionary whose conclusion is literally `WindowPairSupply M`, eventual-vs-effective separation with the `≤ 4·10⁹` bound recorded separately, and the conditional end-to-end adapter to the public statement); status/audit files `CurrentStatusErdos287FixedBudgetEffectivity.lean`, `AxiomAuditErdos287FixedBudgetEffectivity.lean`; report `ERDOS287_FIXED_BUDGET_FCL_EFFECTIVITY_SAFE_BANK_REPORT.md`.

## Build and audit

`lake build`: **8352 jobs, 0 errors, 32 warnings** — all 32 pre-existing in older files, **0 from any new file** (the pre-existing baseline was 8334 jobs / 32 warnings). Every new module also builds individually.

Axiom audit: 136 declarations audited in the first layer (117 with axioms, 19 with none) and 55 in the second (47 with axioms, 8 with none). Every reported axiom set is a subset of `{propext, Classical.choice, Quot.sound}`. No `sorry`, `sorryAx`, custom `axiom`, `native_decide`, `unsafe` or `implemented_by` occurs in any new file. No external analytic statement is encoded as an axiom: `FordHPhysicalBinding`, `PhysicalCollapseBinding`, the weighted source adapter, `BalancedSevenSP2PhysicalBridgeV2`, the three V2 B-comparison inputs, the sub-sqrt and super-sqrt interfaces, the fixed-budget physical wrapper, `PositiveMarginSupply`, `CertificatePinned` and the window-pair export/effective-supply objects are all left uninhabited, each with an explicit counterguard where one is possible.

Erdős #287 itself is **not** proved and is recorded as OPEN in both status layers, as are the strong all-`A` supersqrt statement, the full-source analytic kernel, the window-pair supply and effectivity. All work is committed and pushed.

# Summary of changes for run db5e1e60-2410-4512-82bc-d52666e80b6c
Completed the requested append-only strict-cell canonical-singleton bank for Erdős #287. Nothing existing was deleted, renamed, weakened or relocated; the only change to an existing file is four appended `import` lines in `RequestProject/Main.lean` (diff versus the pre-pass commit: 6 files changed, 1412 insertions, **0 deletions**). Erdős #287 is **not** claimed to be solved, and the analytic singleton Type-II estimate is **not** proved.

FILES ADDED
- `RequestProject/CurrentProgramme/Erdos287StrictCellCanonicalSingleton.lean`
- `RequestProject/CurrentProgramme/Erdos287StrictCellProductWeightBridge.lean`
- `RequestProject/Status/CurrentStatusErdos287StrictCellCanonicalSingleton.lean`
- `RequestProject/Status/AxiomAuditErdos287StrictCellCanonicalSingleton.lean`
- `ERDOS287_STRICTCELL_CANONICAL_SINGLETON_SAFE_BANK_REPORT.md` (full report)

WHAT IS PROVED (kernel-checked, no placeholders)
1. `OmegaSharp` — the exact weighted prime-vector → integer pushforward Ω♯_C along `v ↦ ∏ᵢ vᵢ`, with fibre lemmas and vanishing off the image.
2. `omegaSharp_one_not_automatic` — countermodel: the balanced certificate `λᵢ = {2,3}` satisfies the banked SP-2 packet normalisation, yet the fibre over `2⁶·3 = 192` has mass `7`, so `Ω♯_C = 1` is never automatic.
3. `StrictCellHypotheses` with `strictCell_k_zero` (k = 0) and `strictCell_J_empty` (J = ∅) derived from the collapse field, plus a non-vacuity witness.
4. Balanced-seven divisor-depth theorem (`C(6,3) = 20` depth-3 patterns) and `hStar_eq_neg_twenty` (`H* = −20`). No `HStar` symbol existed previously; the already banked value `∑_{j≤3}(−1)^j C(7,j) = −20` was reused, not re-proved, and `hStar_eq_balancedSevenLowSum` records that the two readings agree.
5. `ford_coordCount_eq_nine`: `s = |U|+1`, `r = 8−|U|`, `N = s + r = 9` for every branch label.
6. `fordBranches_card`: `#{U ⊆ Fin 7 : |U| ≤ 3} = 64`.
7. `physicalPrimeCoords_card = 7` and `terminalUnitCoords_card = 2`, with the 7+2 = 9 partition.
8. `PhysicalK0Conditions720` (twelve fields) proved wholly from the strict-cell hypotheses via `physicalK0_of_strictCell`.
9. `dIndex_eq_empty` — no `d_{h,j}` variables for k = 0, with a guard showing the hypothesis is load-bearing.
10. `canonicalSingleton` — the deterministic selection i(U) (least coordinate outside U), with minimality and a uniqueness/pinning theorem.
11. Singleton Type-II *window* from the physical prime size bounds: `singleton_mem_window`, `complement_pushforward_bounds` ([Y⁶,Z⁶]), `pushforward_bounds` ([Y⁷,Z⁷]).
12. Exact mass factorisation (`omegaSharp_total_mass`, `productWeight_total_mass`) — no generic subsum inclusion–exclusion is required.
13. `perronContourCount_eq_zero` — zero Ford hard-condition Perron contours.
15. Counterguards `weight_not_product_separable` and `kernel_not_automatically_separable`: an arbitrary coefficient does not imply rank-one/product separation.
16.–17. Conditional on the bridge, the exact factorisation `K(m,n) = ξ(m)·κ(n)` with canonical deterministic factors `ξ(m)=K(m,n₀)`, `κ(n)=K(m₀,n)`; the six-prime complement definition and `complementDepth_eq_six`.
18. Deterministic finite interfaces: `finite_cauchy_schwarz`, `productEnergy_factorises`, `cell_cauchy_productEnergy`.

LEFT UNINHABITED (as required)
- `BalancedSevenSP2StrictCellProductWeightPhysicalBridge`, with explicit fields for the slot-box physical cell, product/fixed-nuclear vector weight, distinctness/repeated-prime routing, Ford-H binding, cutoff binding and physical B binding (plus kernel data). No inhabitant is constructed; `bridge_not_automatic` refutes it at explicit data, and `bridge_is_an_input_not_a_theorem` records that all census results are implications only.
- `SP2LabelledSingletonGeneratedTypeIIInput`, the exact analytic inequality; `typeII_input_not_automatic` refutes it at explicit parameters.

STATUS LAYER (new, later, controlling; earlier layers untouched)
GENERIC FORD723 CENSUS: SUPERSEDED as immediate physical frontier (superseded ≠ retracted, proved); SP2-LABELLED64-CANONICALSINGLETON-PACKETCENSUS45: kernel-proved conditional on the physical bridge; BALANCED7-SP2-STRICTCELL-PRODUCTWEIGHT-PHYSICAL-BRIDGE45: OPEN/UNINHABITED; SP2-LABELLED-SINGLETON-GENERATEDTYPEII45: OPEN ANALYTIC; ERDOS287: OPEN. Eleven `backing_*` theorems tie the single kernel-proved row to actual theorems, and scope guards record that no analytic Type-II claim and no closure of #287 is made.

BUILD AND AUDIT
- `lake build` succeeds: 8334 jobs, **0 errors**; the 32 warnings are pre-existing in older files, **0 from the new modules** (baseline was 8330 jobs / same 32 warnings).
- The audit module runs 83 `#print axioms` reports over every principal new theorem; across the whole build log every axiom set is contained in {propext, Classical.choice, Quot.sound}, with zero `sorryAx`.
- No `sorry`, custom `axiom`, `unsafe`, `opaque`, `native_decide` or `implemented_by` occurs as Lean code in the new files (those words appear only in docstring prose). All finite censuses (64, 7, 2, 9, 20, 6, 128) are closed by kernel `decide`.
- All work is committed and pushed; `ARISTOTLE_SUMMARY.md` was not edited.

# Summary of changes for run 82d56e05-e25e-485b-8dc9-5c54b836498c
Completed the append-only master-source-frontier pass for Erdős #287. Nothing was deleted, renamed, weakened or relocated; the only change to an existing file is ten appended `import` lines in `RequestProject/Main.lean`. Erdős #287 is **not** claimed to be solved, no `Erdos287ClosureInputs` inhabitant is constructed, and no theorem named `erdos287` exists.

FILES ADDED
- `RequestProject/CurrentProgramme/Erdos287MasterSourceInterface.lean`
- `RequestProject/CurrentProgramme/Erdos287ProofOmegaPartition.lean`
- `RequestProject/CurrentProgramme/Erdos287PerronSingleContour.lean`
- `RequestProject/CurrentProgramme/Erdos287TypedSourcePacketCompiler.lean`
- `RequestProject/CurrentProgramme/Erdos287PerronInterfaceCounterguard.lean`
- `RequestProject/CurrentProgramme/Erdos287BDiagonalDeltaQAbstract.lean`
- `RequestProject/CurrentProgramme/Erdos287PhysicalDictionaryInterfaces.lean`
- `RequestProject/CurrentProgramme/Erdos287SourceCoverageCompiler.lean`
- `RequestProject/Status/CurrentStatusErdos287MasterSourceFrontier.lean`
- `RequestProject/Status/AxiomAuditErdos287MasterSourceFrontier.lean`
- `ERDOS287_MASTER_SOURCE_FRONTIER_SAFE_BANK_REPORT.md` (full report with the required final block)

WHAT IS PROVED (kernel-checked, no placeholders)
- Master source: finite test model `unprojectedSource` with its deterministic bounds; the realisation interface `MasterPhysicalSourceRealisation` (parent identification, exact index family, exact coefficient factorisation, positive shared-gcd coordinate, coprimality data, outer variables) left **uninhabited**; the dictionary-vs-realisation firewall `sourceDictionary_ne_physicalRealisation` with an explicit finite countermodel where the dictionary is populated but the claimed physical equality fails, plus `no_realisation_zeroGcdSpec` and a toy realisable spec showing the interface is a genuine condition.
- Proof-local Ω (new namespace, not identified with historical Ω objects): `DyadicPartition` certificate (exact partition of unity, local support, bounded overlap) with `weight_le_one`, `one_le_overlapBound`, `reconstruction`; the exact insertion identity `unprojectedSource_eq_sum_projectedSource`; local finiteness `dyadicLocalFiniteness` (at most 3 dyadic scales with g/2 ≤ H ≤ 2g, sharpness shown); the physical insertion input left uninhabited with `abstractProofOmegaPartition_does_not_construct_physicalInsertion`.
- Single Perron contour: the exact real integral `∫_{-T}^{T}(c²+t²)^{-1/2} dt = 2·arsinh(T/c)` for c>0 (proved, not assumed), `arsinh x ≤ log(1+2x)`, the budget at c = 1/L, T = L^K (`2·arsinh(L^{K+1}) ≤ 2·log(1+2L^{K+1})`), the `SingleContourL1Bound` interface (inhabited) and deterministic compilers with cardinality explicit.
- Typed packets: `SourcePacketDecomposition` with the **explicit global** `totalNuclearMass ≤ nuclearBudget` field; compiler `‖source‖ ≤ nuclear·packetBound + errorBound` plus the log-budget specialisation; `packetwise_coefficient_bound_does_not_bound_total` proving the global field cannot be derived packetwise.
- Perron interface counterguard: `perContour_bound_does_not_imply_total_without_cardinality` and `no_global_total_from_perContour_bound` (FAIL verdict, finite countermodel), with the positive cardinality-explicit companion.
- Abstract Δ × q_a kernel: `deltaQ_unitaryFourier_bound` (reusing, not re-proving, the banked reciprocal unitary Fourier theorem), generic residue-aggregation `phase_fiberwise`, the exact finite aggregation compiler `‖S‖² ≤ n·M_Δ·M_q·E_A·E_B` with square-root form and the interval instantiation supplying `M = length/n + 1` (the 1+D/n, 1+E/n factors), and the Cauchy step over t.
- Physical bridges: `BDiagonalDeltaQPhysicalDictionary` (Archimedean factors, U_e(Δ), local harmonic profile, Perron labels, A0/C0 dependence, gcd mask, dyadic/source factors), `C0SourceRealisationBridge`, `TransverseSourceRealisationBridge`, `PhysicalSourceCoverage100` — all **uninhabited**, each with an emptiness theorem at the countermodel spec; the physical b-diagonal compiler is proved only conditionally on the dictionary plus explicit energy inputs.
- Coverage: `PhysicalOwnerMap` with no-double-spending and exhaustive-over-domain accounting, and the firewall that abstract ownership does not give 100% physical coverage.
- Status: a later, controlling append-only layer recording ERDŐS287 OPEN, first frontier UNPROJECTED-MASTER-PHYSICAL-SOURCE-REALISATION45 OPEN, next MASTER-SOURCE-TO-TYPED-PERRON-PACKETS45 OPEN, WindowPairSupply OPEN, the FAIL verdict on current Perron interface sufficiency, the b-diagonal abstract/physical split, and the supersession ledger for the two old claims — with six `backing_*` theorems tying every "proved" row to an actual theorem, the reconfirmed end-to-end compiler and the still-visible `supply` field. Earlier status layers were not rewritten.

BUILD AND AUDIT
- Every new module builds individually; default `lake build` succeeds with **8330 jobs, 0 errors**, 32 warnings — all pre-existing in older files, **0 from the new modules**.
- `AxiomAuditErdos287MasterSourceFrontier.lean` runs 100 `#print axioms` reports: 89 × {propext, Classical.choice, Quot.sound}, 1 × {propext}, 10 axiom-free. No `sorry`, `sorryAx`, custom axiom, `unsafe`, `opaque`, `native_decide` or `implemented_by` occurs as code anywhere in the new files (those words appear only in docstring prose).
- Diff versus the pre-pass commit: 12 files changed, 2268 insertions, **0 deletions**. All work is committed and pushed; `ARISTOTLE_SUMMARY.md` was not edited.

# Summary of changes for run 70ede315-c408-474e-af0b-42cac5fb2441
Completed the append-only public-tree reconciliation pass for Erdős #287. Nothing was deleted or rewritten; the only modification to an existing file is three appended `import` lines in `RequestProject/Main.lean`. Erdős #287 is **not** claimed to be solved.

REGRESSION
- Baseline `lake build` on the unmodified tree: success, **8317 jobs**, 0 errors, 32 cosmetic linter warnings (unused variables / unused simp arguments in pre-existing files).
- After this pass: `lake build` success, **8320 jobs**, 0 errors.
- Repository-wide scan for `sorry`, `sorryAx`, `admit`, custom `axiom`, `unsafe`, `opaque`, `native_decide`, `implemented_by`: no occurrence as Lean code anywhere; the words appear only in docstrings and `.md` prose.
- Axiom audit: 2276 `#print axioms` reports in the build log; parsing every reported axiom set yields exactly `{propext, Classical.choice, Quot.sound}`, with zero `sorryAx` and no user axiom. The end-to-end chain (`no_Erdos287Counterexample_of_closure`, `erdos287_seq_of_closure`, `Gap2CE.no_of_windowPairSupply`, `windowPairSupply_of_sophieWitness`, `no_Erdos287Counterexample_of_max_le_4e9`, `no_Erdos287Counterexample_of_prime_max`, `erdos287_seq_of_no_counterexample`) was re-printed in this pass.

FILES ADDED
- `RequestProject/Erdos287/OrderedSequenceBridge.lean` — the statement-equivalence layer.
- `RequestProject/Status/PublicTreeReconciliation20260901.lean` — the new append-only status layer (node classification, DAG, end-to-end firewall, extra semantic guards).
- `RequestProject/Status/AxiomAuditPublicTreeReconciliation20260901.lean` — `#print axioms` for all new declarations plus an end-to-end regression re-print.
- `ERDOS287_PUBLIC_FORMAL_RECONCILIATION_2026-09-01.md` and `ERDOS287_STATEMENT_EQUIVALENCE_2026-09-01.md`.

THEOREMS PROVED (all kernel-checked, no placeholders)
- Statement equivalence: `Erdos287SeqStatement` (published ordered form), `erdos287SeqStatement_of_statement`, the previously missing converse `erdos287Statement_of_seqStatement`, the equivalence `erdos287Statement_iff_seqStatement`, the adjacent-gap dictionary `gap_le_two_iff_orderEmb_gap`, the `ℚ`/`ℝ` reciprocal-sum dictionary `sum_recip_rat_iff_real`, and the enumeration lemmas `enum_mem`, `enum_lt_enum`, `exists_enum_eq`, `enum_succ_le`, `sum_enum_recip`. The problem statement is not weakened anywhere.
- End-to-end firewall: `reconfirm_endToEnd` (`Erdos287ClosureInputs → Erdos287Statement`), its ordered form `reconfirm_endToEnd_seq`, `closureInputs_supply_visible` (the `supply` field stays exposed), and genuine non-vacuity guards `not_windowPairSupply_zero/_one/_two`, `closureInputs_threshold_ge_three`, `windowPairSupply_forces_large_primePowers` (a window pair forces two consecutive positions in the top half of `[1,M]`, each carrying a prime power `> M/10`). The ledger `no_banked_interface_constructs_closureInputs` records — explicitly as metadata, not as an impossibility theorem — that none of the eight banked local analytic/source interfaces constructs a closure-inputs inhabitant.
- Current formal frontier: `nodeStatus`/`nodeKind` classify every listed node as kernel-proved, analytic-bank metadata only, conditional source interface, open, superseded or retracted, with `classification_of_open_nodes`, `analytic_nodes_not_kernelProved`, `kernelProved_node_count`. No unreleased claim (b-diagonal closure, Ω proof-local reconstruction, total Perron ledger, local analytic kernel closure) was promoted.
- Dependency DAG terminating at `Erdos287Statement`: `dependsOn`, `rank`, `dependsOn_rank_decreasing`, `dependsOn_irrefl`, `erdos287Statement_terminal`, and the guard `implication_does_not_close_target` (a proved implication never closes its target).
- Extra semantic guards where earlier coverage was prose-level: `plain_l2_ne_weighted_l2` (weighted vs unweighted Ω-norms), `packetwise_not_aggregate`, `interface_status_not_theorem`, `supply_is_input_not_output`.

STATUS
- WINDOWPAIR SUPPLY: OPEN. END-TO-END ERDŐS287: OPEN (only the implication is proved). No theorem named `erdos287` exists in the repository. Statement-equivalence audit: PASS. Semantic firewall audit: PASS.
- The four authoritative files (`Status/SemanticFirewallsErdos287.lean`, `Status/CurrentAuthoritativeStatusErdos287.lean`, `Status/Erdos287EndToEndStatus.lean`, `Erdos287/ClosureInputs.lean`) are byte-identical to their previous state; historical status files were not rewritten.
- No `sorry`, custom axiom, `unsafe`, `opaque`, `native_decide` or `implemented_by` remains. All work is committed and pushed.

# Summary of changes for run 0a482901-8cc2-4fd0-97db-6b9300048e52
Completed the append-only dual-level / simultaneous-critical extension of the Erdős #287 formal bank, plus the semantic re-anchoring hygiene layer. Everything is committed and pushed.

FILES ADDED (all new, nothing deleted or rewritten)
- `RequestProject/CurrentProgramme/Erdos287TransverseBezoutRowAffine.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseBezoutThreeAxisFourier.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseDualLevelReciprocity.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseDualLevelXiReduction.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseDualPairwiseFourier.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseAffineProductEnergyInterface.lean`
- `RequestProject/CurrentProgramme/Erdos287ReciprocalDensityDuality.lean`
- `RequestProject/Status/CurrentStatusErdos287SimultaneousCritical.lean`
- `RequestProject/Status/AxiomAuditErdos287DualLevel.lean`
- `RequestProject/Status/SemanticFirewallsErdos287.lean`
- `RequestProject/Status/CurrentAuthoritativeStatusErdos287.lean`
- `RequestProject/Status/AxiomAuditErdos287SemanticReanchor.lean`
- `ERDOS287_DUALLEVEL_SIMULTANEOUSCRITICAL_SAFE_BANK_REPORT.md`
- `ERDOS287_HOSTILE_SEMANTIC_REANCHOR_AUDIT.md`

FILES MODIFIED: only `RequestProject/Main.lean`, twelve appended import lines (no reordering, no deletions). Diff against the pre-delta commit: 15 files changed, 4095 insertions(+), 0 deletions(−) — the previous one-conductor/q_C bank is byte-identical and preserved, and the reciprocal Fourier theorem and one-conductor Γ reduction were reused, not re-proved.

UNCONDITIONAL RESULTS PROVED: Bézout-row affine CRT algebra (`gammaG_mod_m`, `gammaG_mod_r0`, affine slope and injectivity, `affineGcd_divisor_residue_class` with the exact interval count ≤ H/d+1); the three-axis frequency map with both fibre congruences, the exact fibre count (Q/m+1)(H₀/r₀+1), the finite L² inequality `bezoutRowThreeAxisFourier_bound`, and the exact eight-term `bezoutThreeAxis_contraction_identity`; the dual CRT split under exact coprimality, `additiveReciprocity_coprime` in integer/character form, `Cmqg` congruences, `Xi_affine_slope`; the Ξ reduction (constant gcd dividing every Ξ, reduced modulus with explicit divisibility, `xiRed_coprime`, `xi_divisor_affine_residue_unique`, plus a witness that constant and variable Ξ-gcds genuinely differ); dual frequency fibre counts and the three dual pairwise finite Fourier bounds with `dualPairwise_min_bound` and a countermodel showing min ≠ product; affine-product pushforward and collision identities; reciprocal-density product/ratio identities with their safe deterministic consequences and an exact monomial scale-saturation instance.

KEPT AS EXPLICIT INTERFACES (never discharged, each with a kernel-checked "not automatic" companion): grouped-q product energy, `XiGcdTailBound`, `AffineProductEnergyBound` (Cochrane–Shi type, with the conditional compiler `dualAffineProductFourier_of_energy`), `OmegaWeightedDivisorMomentBound`, and `SimultaneousCriticalPacket` whose analytic fields are provably unfilled. No asymptotic/physical item was converted into a theorem, and no theorem concludes `True`.

HYGIENE LAYER: authoritative status/precedence record, semantic object ledger, q-role split, x/X and pointwise-vs-aggregate countermodels, three-level C0 split, four-way Ω-norm split, coverage scope labels, Type-II naming split, `WindowPairSupply` classified as a sufficient compiler input, a one-way `Gap2CE` firewall with the explicit `{1}` countermodel, frontier DAG, retraction ledger (superseded ≠ false), resource/constant/source-normalisation ledgers, S2–S6 risk counts with guards, and five undischarged pre-closure blockers.

BUILD AND AUDIT: every new module builds individually; the default `lake build` completes successfully with 8317 jobs and 0 errors (the previous run's 8305 figure was not reused). `#print axioms` over 161 + 65 new declarations shows 53 + 41 axiom-free and the rest depending only on `propext`, `Classical.choice`, `Quot.sound`: no `sorryAx`, no custom axiom, no `native_decide`, `unsafe`, `opaque` or `implemented_by`; those words occur in the new files only inside docstring prose.

Erdős #287 remains OPEN, the b-diagonal face remains open and untouched, and the current first analytic residual is recorded as THREEFACTOR-TRANSVERSE-BRANCHI-SIMULTANEOUSCRITICAL-DUALLEVEL-AFFINEPRODUCT-MOBIUS45. `ARISTOTLE_SUMMARY.md` was not edited.

# Summary of changes for run 717cb9a6-645a-4a02-a1e8-74ae784b9ed4
Appended a new, kernel-checked transverse one-conductor / `q_C` bank to the Erdős #287 project. Strictly append-only: nothing existing was deleted, renamed, weakened, relocated or overwritten; `RequestProject/Main.lean` received seven appended `import` lines only. Full detail is in `ERDOS287_TRANSVERSE_ONECONDUCTOR_SAFE_BANK_REPORT.md`.

FILES ADDED
- `RequestProject/CurrentProgramme/Erdos287TransverseReducedConductor.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseOneConductorReciprocity.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseGammaReduction.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseQCUnitaryCompiler.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseDenseQCInterface.lean`
- `RequestProject/Status/CurrentStatusErdos287TransverseBezoutSingleCarrier.lean`
- `RequestProject/Status/AxiomAuditErdos287TransverseOneConductor.lean`
- `ERDOS287_TRANSVERSE_ONECONDUCTOR_SAFE_BANK_REPORT.md`

FILES MODIFIED: `RequestProject/Main.lean` (appended imports only, no reordering, no deletion).

NEW UNCONDITIONAL THEOREMS. Source factorisation: `TransversePacket` (with the divisibility fields `a₁ ∣ e`, `c₂ ∣ r₂`, so every quotient is justified), the exact quotient lemmas `E_mul_a1`, `R_mul_c2`, `twoCirc_mul_delta2`, `ECirc_mul_deltaE`, `BCirc_mul_deltaB`, `qBar_mul_deltas` (`q̄·δ₂δ_Eδ_B = q_C`), `qBar_dvd_qC`, `RHat_eq`, plus positivity. Primed packet reuses the same structure (`primed_packet_symmetric`). Cross-packet: `lcm_eq_mul_div_gcd`, `QStarRed_mul_dStar`, `QStarRed_exact_normal_form`, `QStarRed_eq_div`. Carrier metadata `carrierClass_table` (E°,R signless; B°,M₀ signed; z²,2° fixed) with `carrierClass_is_metadata`. `Rcarrier_harmonic_square_bound` with explicit constant 1. One-conductor: `exists_inverse_of_coprime`, `transverseGammaInt_modEq_m/_r` and the ZMod forms `transverseGamma_mod_m`, `transverseGamma_mod_r`; the Archimedean factor is a parameter (`reducedPhase`, `reducedPhase_norm`). Reduction: `transverseGamma_gcd_eq` (`gcd(Γ,rm)=gcd(B−A,r)`), `transverseGammaRed_coprime` (`gcd(Γ^red,m_P)=1`), `transverseGammaRed_isUnit`, with the bundled `OneConductorData`. `q_C` compiler: `inv_mul_factorisation_zmod(_nat)`, `transverseQCUnitaryFourier_bound`/`_l2_bound` (the previously banked reciprocal unitary Fourier theorem instantiated at `(m_P, Γ^red)` — no new Fourier proof), `transverseQCUnitary_omegaH_blind`. Finite sanity tests for the Γ congruences, the gcd reduction (Γ=104, g_P=2, Γ^red=52, m_P=15) and the composite-modulus inverse split.

NEW CONDITIONAL COMPILERS (every analytic input an explicit hypothesis): `transverseQCGroupedUnitary_of_productEnergy` (reuses the existing product-energy hypothesis shell) and `denseQC_closed_of_unitary_margin` together with the `DenseQCAdmissible` interface of explicit finite inequalities; the margin hypothesis is proved non-automatic and admissibility alone is proved not to give the bound.

SCOPE NOTE ON HYPOTHESES: the gcd normal form consumes `gcd(A,m)=1`; `gcd(r,m)=1` turned out not to be needed and is therefore not assumed, while `gcd(m,r)=1` is stated exactly where it is used (existence of the inverse `t`).

STATUS / FIREWALLS: C0 recorded only as ANALYTICALLY CLOSED CONDITIONAL ON FORMAL NORMALISATION; Ω_H and Perron/nuclear normalisation, source-length bounds and product-energy comparisons remain explicit interfaces; the naive full-CRT signless-pair DFT is recorded as retracted (no universal non-equality theorem asserted); the pair-existence label is preserved and marked superseded as first frontier, with `THREEFACTOR-TRANSVERSE-CRITICAL-BEZOUTNUMERATOR-SINGLECARRIER45` open as the current frontier; the b-diagonal row stays separate and open; Erdős #287 stays OPEN.

BUILD AND AUDIT: each new module builds individually (PASS); default `lake build` PASS with 8305 jobs and 0 errors. `#print axioms` is run for all 134 new declarations: every one depends only on a subset of `propext`, `Classical.choice`, `Quot.sound` (58 depend on no axioms). No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `implemented_by` occurs as code in any new file.

FINAL FORMAL VERDICT: SAFE APPEND-ONLY BANK UPDATED.

# Summary of changes for run 5fff01ff-dc20-488e-994e-09d148f8e653
Appended a new, kernel-checked C0 unitary-Fourier / transverse-carrier bank to the Erdős #287 project. Nothing existing was deleted, renamed, weakened or relocated; `RequestProject/Main.lean` received appended `import` lines only. Full detail is in `ERDOS287_C0_UNITARYFOURIER_SAFE_BANK_REPORT.md`.

FILES ADDED
- `RequestProject/CurrentProgramme/Erdos287ReciprocalUnitaryFourier.lean`
- `RequestProject/CurrentProgramme/Erdos287BalancedBUnitaryFourierCompiler.lean`
- `RequestProject/CurrentProgramme/Erdos287AffineBilinearReciprocalNumerator.lean`
- `RequestProject/CurrentProgramme/Erdos287C0PhysicalNormalisationInterface.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseCarrierInterface.lean`
- `RequestProject/Status/CurrentStatusErdos287C0UnitaryFourier.lean`
- `RequestProject/Status/CurrentStatusErdos287TransverseCarrier.lean`
- `RequestProject/Status/AxiomAuditErdos287C0UnitaryFourier.lean`
- `ERDOS287_C0_UNITARYFOURIER_SAFE_BANK_REPORT.md`
(Paths follow the repository's existing `CurrentProgramme/` + `Status/` layout rather than a new top-level directory.)

FILES MODIFIED: `RequestProject/Main.lean` (eight appended imports).

NEW UNCONDITIONAL THEOREMS (all proved, no placeholders)
- Full Fourier Gram `unitaryFourier_mulConj_sum` (`F_C F_C* = x·I`) and the exact column energy `unitaryFourier_column_energy`, for an arbitrary unit `C` and an arbitrary positive modulus — no squarefree or primality hypothesis; a composite-modulus instance is certified at `x = 12`, `C = 5`.
- `unitaryFourier_bilinear_bound`, `unitaryFourier_finset_bilinear_bound` (zero-extension / support-restricted form), the inversion permutation of the units (`isUnit_zmod_inv`, `zmod_inv_inv_of_isUnit`, `zmod_inv_bijOn_units`) and the principal new theorem `reciprocalUnitaryFourier_bilinear_bound`, with the alias `transverseTwoCarrierUnitaryFourier` (reused, not re-proved).
- Residue aggregation: `residueAggregate_l2_le_maxFiber`, the interval fibre count `interval_residue_fibre_card_le` (`≤ N/x + 1`, integer form) and `intervalResidueAggregate_l2_bound`; the regrouping `reciprocalPhase_fiberwise` and the compiler `balancedReciprocalFourier_compiler`.
- The exact four-term contraction identity `balancedFourier_contraction_identity`.
- Coprimality firewall `coprime_product_left/_middle/_right/_all`.
- Affine and bilinear moving-numerator algebra `affineBilinearNumerator_reciprocal_decomposition` and its character factorisation / rank-one reduction.

CONDITIONAL COMPILERS (every analytic input an explicit hypothesis)
`threeCarrierReciprocalFourier_of_productEnergy`, `c0_balanced_branch_bound_of`, `perronNuclear_total_of_normalisation`, `omegaHL2_of_pointwise_normalisation`, `transverseTwoCarrier_bound_of_unitSupport`, `transverseTwoCarrier_bound_with_fibre_weights`. Their conclusions are explicit finite inequalities; no conclusion is `True` and none asserts C0 closure. Each hypothesis shell (product-convolution energy, Perron/nuclear, Ω_H ℓ²) is proved both non-automatic and satisfiable, so nothing can be silently discharged. The existing Ω_H pointwise shell is reused rather than duplicated.

INTERFACES / METADATA
`TransverseCarrierPacket` with unfilled `Prop` fields, `UsableTwoCarrierPair`, the bare trichotomy datatype (no exhaustiveness claimed), a `ResearchStatus` datatype with the requested status values, the `x` vs `X` firewall (`inv_sqrt_comparison_not_automatic`), the acyclic constant-selection order, and preservation theorems for the earlier ledgers. C0 is recorded only as "ANALYTICALLY CLOSED CONDITIONAL ON FORMAL NORMALISATION"; the b-diagonal row stays open and separate (`no_double_spending`); Erdős #287 stays open.

BUILD AND AUDIT
Each new module builds individually: PASS. Default `lake build`: PASS (8298 jobs, 0 errors). `#print axioms` for every new declaration reports only subsets of `propext`, `Classical.choice`, `Quot.sound`; several depend on no axioms. No `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by` or `native_decide` occurs as code in any new file. Not proved and not encoded: the carrier factorisation of `Q_*^red`, the `B_*^red` dependence, two-long-carrier existence, and any single-carrier residual classification.

# Summary of changes for run dd15ae7d-1759-4b7b-8bc7-0f355114010b
Appended the requested C0 source-lift / reduced-projective bank as new files only; no existing module was edited or weakened, and no statement claims C0 closed or Erdős #287 proved.

FILES CREATED
- `RequestProject/CurrentProgramme/Erdos287A0C0SourceLift.lean`
- `RequestProject/CurrentProgramme/Erdos287ReducedProjectivePair.lean`
- `RequestProject/CurrentProgramme/Erdos287BPrimeH0Energy.lean`
- `RequestProject/CurrentProgramme/Erdos287ConditionedInverseConvInterface.lean`
- `RequestProject/Status/CurrentStatusErdos287C0SourceLift.lean`
- `RequestProject/Status/AxiomAuditErdos287C0SourceLift.lean` (placed in `Status/` to match the existing `AxiomAudit*` convention)
- `ERDOS287_C0_SOURCELIFT_SAFE_BANK_REPORT.md`

FILES MODIFIED
- `RequestProject/Main.lean` — six appended `import` lines only.

UNCONDITIONAL THEOREMS (all kernel-checked)
- Source data: `Erdos287.SourceLift.SourceRow` (signed `s, s', Δ₀, Δ₀' : ℤ`; remaining slots `ℕ` with positivity fields) and `u, u', Γ₁, Γ₂, β₂, A0row, C0`.
- Primitive forms: `erdos287_gamma1_primitive`, `erdos287_gamma2_primitive`, `erdos287_A0row_primitive`, `erdos287_C0_primitive`, plus `erdos287_u_pos`, `erdos287_u'_pos`, `erdos287_b_pos`.
- Row representative: `erdos287_Q2_dvd` (`x ∣ d₁' v x`), `erdos287_A0pre_sub_A0row`, `erdos287_A0pre_dvd_sub`, `erdos287_A0pre_congr_A0row` (`A0pre ≡ A0row [ZMOD x]`), `erdos287_A0pre_congr_A0row_row`.
- Raw→reduced: `erdos287_F_pos`, `erdos287_F_ne_zero`, `erdos287_Praw_factor`, `erdos287_Rraw_factor`, `projective_collision_iff_of_row_factor`, `erdos287_raw_projective_collision_iff_reduced`, `projective_collision_invariant_under_row_scaling`, `row_factors_may_differ`.
- Depth record: `erdos287_Pnat_slot_product`, `erdos287_Rnat_slot_product`, `erdos287_numerator_depth`, `erdos287_denominator_depth` (both 8), `erdos287_fixed_depth_exponent` ((8+8)²−2 = 254).
- Finite energy: `product_fibre_l2_bound_of_fibre_card`, `productFibre_card_le_of_second_mem`, `product_fibre_l2_bound_of_second_cardinality`, `bprime_h0_global_energy`, `product_fibre_l2_bound_of_filtered`, `bprime_h0_global_energy_congruence_filter`.
- Firewall witnesses: `conditionedInverseConv_hypothesis_not_automatic`, `conditionedInverseConv_hypothesis_satisfiable`, `omegaH_normalization_not_automatic`; ledger theorems `banked_children_are_unconditional`, `open_owners`, `global_rows_not_closed`, `no_analytic_row_is_banked`, `depth_bound_not_formalised`, `sourcelift_pass_does_not_imply_c0_closure`, `commonX_ledger_still_preserved`.

CONDITIONAL THEOREMS (explicit named hypotheses only)
`energy_transfer_of_depth_bound` and `bprime_h0_global_energy_with_depth_bound` (hypothesis `d₁' ≤ Lparam^K`), `erdos287_C0_after_conditioned_transfer` (hypothesis `ConditionedInverseConvHypothesis`), `omegaH_energy_of_normalization` (hypothesis `OmegaHNormalizationHypothesis`). `d₁' ≤ L^K`, the Ω_H normalisation and the conditioned transfer are never asserted; both shells are proved non-automatic.

BUILD AND AUDIT
`lake build` on the default target: PASS (8290 jobs, 0 errors). A token search over all new files finds no `sorry`, `axiom`, `unsafe`, `native_decide`, `opaque` or `implemented_by` as code (only in docstring prose in the audit file). `#print axioms` on every new declaration reports only subsets of `propext`, `Classical.choice`, `Quot.sound`; several depend on no axioms.

HOSTILE-AUDIT POINTS
Casts are explicit with no `Nat` subtraction; sign slots carry no positivity; `F = b u'` is only cancelled via the proved `F ≠ 0`; the collision equivalence is stated for two independent rows with independent factors (`row_factors_may_differ` witnesses `F₁ ≠ F₂`); the energy lemma bounds fibre cardinality (via injectivity of `p ↦ p.2` on fibres over `n ≠ 0`), not a pointwise divisor maximum.

STATUS FREEZE (recorded in the ledger and proved there): banked children A0C0-PRIMITIVE-SOURCEFORM45, A0C0-SOURCELIFT45, A0C0-BPRIME-ABSORPTION45, BPRIME-H0-GLOBALENERGY45, PROJECTIVE-RAW-TO-REDUCED45, fixed depth (8,8); OPEN analytic owner EXACTPRODUCT-CONDITIONED-INVERSECONV-LEVELLS45; OPEN source pin SHAREDGCD-OMEGAH-NORMALISATION-SOURCEPIN45; EXACT PRODUCT COLLISION / DOUBLE TYPE II / C0: PARTIAL; ERDOS287: OPEN.

# Summary of changes for run e3eda94c-ae28-4753-ad56-d37dec60d2c5
## COMMON-x / fractional-linear C0 bank — appended, kernel-checked, build green

The new bank is appended strictly after the existing HYBRID-2 / critical-rectangle bank. No previously banked module was edited, no previously proved theorem was altered or weakened, no historical status layer was replaced or deleted. Full detail is in `ERDOS287_COMMONX_FRACTIONALLINEAR_SAFE_BANK_REPORT.md`.

### FILES ADDED
- `RequestProject/CurrentProgramme/Erdos287CommonXArithmetic.lean`
- `RequestProject/CurrentProgramme/Erdos287FractionalLinearC0.lean`
- `RequestProject/CurrentProgramme/Erdos287CommonXCollisionFirewall.lean`
- `RequestProject/Status/CurrentStatusErdos287CommonXFrontier.lean`
- `RequestProject/Status/AxiomAuditErdos287CommonX.lean`
- `ERDOS287_COMMONX_FRACTIONALLINEAR_SAFE_BANK_REPORT.md`

### FILES MODIFIED
- `RequestProject/Main.lean` — five new `import` lines appended only. No import path of any existing module changed.

### UNCONDITIONAL THEOREMS (all kernel-checked, no analytic hypothesis)
`Erdos287.CommonX` — §2 common-x conductors: `commonX_gcd` (`gcd(a₁x,a₂x) = x·gcd(a₁,a₂)`), `commonX_mul`, `commonX_lcm`, `commonX_gcd_coprime`, `commonX_lcm_coprime`, `commonX_dvd_left`, `commonX_dvd_right`, `commonX_dvd_gcd`, `commonX_gcd_mul_lcm`. §3 centered-κ CRT: `kappa_crt_exists`, `kappa_mod_small`, `kappa_mod_long`, `kappa_unit_long`, `kappa_sub_one_coprime_long`, `kappa_sub_one_gcd_long_eq_one`, `gcd_kappa_sub_one_fullConductor`, `gcd_kappa_sub_one_fullConductor_of_crt`. §4 graph-diagonal firewall: `graph_diagonal_forces_full_gcd`, `gcd_eq_natAbs_of_dvd`, `graph_literal_diagonal_impossible`, `graph_diagonal_impossible_of_centered`. §7–§8: `commonDivisor_residue_compatible`, `commonDivisor_residue_cancel_unit`, `commonDivisor_residue_iff_unit`, `centered_kappa_satisfiable`, `xRowDiagonal_not_excluded`.

`Erdos287.FractionalLinear` — §5–§6: `fractionalLinear_to_linear`, `oppositeRow_linearized`, `oppositeRow_unique_residue`, `oppositeRow_unique_residue_of_source`, `oppositeRow_unique_residue_zmod`, `kappa_fractionalLinear_of_source`, `kappa_fractionalLinear_of_source_zmod`, `denominator_ne_zero_of_unit`. §11 local change of variables: `affine_leftInverse`, `affine_rightInverse`, `affine_bijective`, `affine_pole_iff`, `sum_affine_reindex`, `sum_affine_reindex_nonzero`.

Conservatism points honoured: the full-conductor gcd equality carries its literal hypotheses (`κ−1 = d·s` with `s` coprime to `qLong`) rather than being overstated; cancellation by `b` exposes `IsUnit b` explicitly; congruences are written as literal divisibilities so no modular inverse is chosen implicitly.

### CONDITIONAL / STATUS-ONLY
`Erdos287.CommonXFrontierStatus`: ledger data (`CommonXNode`, `CommonXLabel`, `stage`, `commonXLedger`, `DiagonalKind`, `DiagonalStatus`, `diagonalLedger`) plus eighteen bookkeeping theorems, including the three demanded non-implications (`commonX_arithmetic_pass_does_not_imply_c0_closure`, `fractionalLinear_pass_does_not_imply_kloosterman_estimate`, `local_kloosterman_arithmetic_does_not_imply_spectral_closure`), `no_false_promotions`, `status_does_not_encode_xRow_exclusion` (the graph/x-row separation, backed by the witness theorem, not by fiat), `transverse_status_rows`, `bdiagonal_status_rows`, and `hybrid2_ledger_still_preserved` / `caseB_ledger_still_preserved`. The Type-I / Type-II rows carry labels deliberately distinct from `provedUnconditional`, so they are records of the research status and cannot read as proofs of an analytic estimate.

### NOT FORMALISED
Double-Type-II Kloosterman saving; level-averaged Kuznetsov / spectral closure; Weil bound; transverse analytic closure; b-diagonal analytic closure (numerical vertex dictionary absent); Ω_H source normalization. None is admitted or assumed.

### AUDITS AND BUILD
- Axiom audit: all 58 new principal declarations depend only on a subset of `propext`, `Classical.choice`, `Quot.sound`; several depend on no axioms at all. No new custom axiom.
- Token audit: no `sorry`, `axiom`, `unsafe`, `native_decide`, `opaque` or `implemented_by` as a code construct in any new file (only the docstring sentence listing the forbidden tokens). Decidable ledger facts use `decide +kernel`.
- `lake build` on the default target: **PASS**, 8284 jobs, 0 errors.

FORMAL FIRST RESIDUAL: `SharedGcdOmegaHNormalizationSourcePin`
RESEARCH FIRST ANALYTIC RESIDUAL: `CommonXFractionalLinearDoubleTypeIIKloosterman45`
C0 / TRANSVERSE / b-DIAGONAL: researchStrictlyReducedOpen
ERDOS287: OPEN

# Summary of changes for run dcdd0861-ffe6-4fe2-afa9-fb4fd3080e2b
The HYBRID-2 / critical-rectangle bank is appended, kernel-checked, and the full repository builds. Full detail is in `ERDOS287_HYBRID2_CRITICALRECT_SAFE_BANK_REPORT.md`.

FILES ADDED:
- `RequestProject/CurrentProgramme/Erdos287Hybrid2Arithmetic.lean`
- `RequestProject/CurrentProgramme/Erdos287Hybrid2AnalyticCompiler.lean`
- `RequestProject/CurrentProgramme/Erdos287Hybrid2CriticalRectangle.lean`
- `RequestProject/CurrentProgramme/Erdos287Hybrid2ShortEdgeFirewall.lean`
- `RequestProject/CurrentProgramme/Erdos287BDiagonalProductMod.lean`
- `RequestProject/Status/CurrentStatusErdos287Hybrid2Frontier.lean`
- `RequestProject/Status/AxiomAuditErdos287Hybrid2.lean`
- `ERDOS287_HYBRID2_CRITICALRECT_SAFE_BANK_REPORT.md`

EXISTING FILES MODIFIED:
- `RequestProject/Main.lean` — seven new `import` lines appended only. No prior mathematical module edited; no previously proved theorem altered; no source firewall replaced.

UNCONDITIONAL THEOREMS:
`Erdos287.Hybrid2`: `mobius_opening_of_squarefree`, `mobius_opening_needs_squarefree`, `coprime_left_of_mul_coprime`, `coprime_right_of_mul_coprime`, `coprime_both_of_mul_coprime`, `isCoprime_both_of_mul_isCoprime`, `isCoprime_of_isInverseMod`, `reciprocal_cancel_common_factor`, `isCoprime_ell_of_inverse`, `baseConductor_gcd`, `fullConductor_gcd`, `fullConductor_needs_coprime`, `pairwise_factors_dvd`, `lcm_dvd_e`, `mul_eq_gcd_mul_lcm`, `g0_mul_g0prime_dvd_e_mul_difference`, `g0_mul_g0prime_does_not_divide_difference`, `sum_inv_Icc_le_one_add_log`, `ell_sum_harmonic`, `ell_sum_harmonic_two_min`, `eta_sq_expand`, `eta1_nonneg`, `rectangle_side1`, `rectangle_side2`, `rectangle_product`, `rectangle_intersection`, `topShell_e_lower_bound`, `noncontraction_shortEdge_or_rectangle`, `hybrid2_survivor_union`, `rectangle_alone_does_not_capture_all_survivors`, `shortD_is_not_automatic`.
`Erdos287.BDiagonal`: `isCoprime_of_dvd_mul_sub_one`, `bdiag_crt_inverse_congr`, `bdiag_phase_product_modulus`, `bdiag_moebius_mul`, `bdiag_moebius_levelPair`, `bdiag_squarefree_split`, `bdiag_reduced_conductor`, `bdiag_reduced_unit`, `bdiag_survivor_union`.
Ledger (`Erdos287.Hybrid2FrontierStatus`): `caseB_strictly_before_hybrid2_frontier`, `primitiveFractionCritical_not_frontier`, `omegaNormalization_is_formal_first_residual`, `hybrid2_analytic_descendants_all_open`, `hybrid2_longEdge_passedThrough_only_if_appropriate`, `erdos287_open`, `only_arithmetic_rows_are_unconditional`, `hybrid2_survivor_union`, `hybrid2_longEdge_pass_does_not_capture_survivors`, `caseB_ledger_still_preserved`, `primitiveFraction_ledger_still_preserved`.

CONDITIONAL THEOREMS:
`Erdos287.Hybrid2.fixedEll_bound`; `Erdos287.Hybrid2.hybrid2_bound`; `Erdos287.BDiagonal.bdiag_delta_contraction_conditional`.

EXPLICIT ANALYTIC HYPOTHESES:
- `fixedEll_bound`: `hArch : Bell ≤ Carch * sqrt Sell`; `hPacket : Pell ≤ L1^2/(ell*M1)`; `hLS : Sell ≤ (D/ell + Q)*(1 + M1/(ell*Q))*Pell`.
- `hybrid2_bound`: `hArch : Btot^2 ≤ Carch^2*Etot`; `hPacket : Etot ≤ Lell^2*Wsep`; `hLS : Wsep ≤ 1/D + 1/M1 + 1/Q + Q/(D*M1)`.
- `bdiag_delta_contraction_conditional`: `hArchB`, `hPacketB`, `hLSB` (same shapes).
- Source gcd identities of §5 exposed as hypotheses `h1`, `h2` (option B). No equivalent literal separated-frequency large sieve exists in the repository, so `hLS` is passed rather than instantiated. None of these is an axiom.

SHORT-D: FORMALISED OPEN
SHORT-M: FORMALISED OPEN
SHORT-Q: FORMALISED OPEN
(exact pigeonhole with explicit constants `C_short = C_rect = 4`; no closure proof was available, none invented)

LONG-EDGE RECTANGLE: FORMALISED PASS (algebraic compiler `rectangle_side1/2`, `rectangle_product`, `rectangle_intersection`); ledger node stays `conditionalOpen`.

g0g0' DIVISIBILITY: FORMALISED PASS. The stronger `g0*g0' | (b2-b1)` was not formalised — it is false and is explicitly refuted.

b-DIAGONAL ALGEBRA: FORMALISED PARTIAL (exact CRT phase collapse, Möbius product, gcd reduction all PASS; the Δ-large-sieve contraction is conditional only).

AXIOM AUDIT: every one of the 63 new declarations depends only on `propext`, `Classical.choice`, `Quot.sound`; several depend on no axioms at all. No new custom axiom.

UNSAFE-TOKEN AUDIT: no `sorry`, `axiom`, `unsafe`, `native_decide`, `opaque` or `implemented_by` in any new file (only prose mentions inside docstrings). Decidable facts use `decide +kernel`.

FULL BUILD: PASS — `lake build` on the default target completes with 8279 jobs and 0 errors.

OMEGA_H: SOURCE PIN (unchanged; B and G polynomial margins also unchanged)

ERDOS287: OPEN

FIRST EXACT FORMAL RESIDUAL: `SharedGcdOmegaHNormalizationSourcePin` (Ω_H normalisation source pin), with the conditional analytic frontier being the union `Hybrid2ShortD ∪ Hybrid2ShortM ∪ Hybrid2ShortQ ∪ Hybrid2LongEdgeTwoSidedRectangle ∪ BDiagonalDeltaProductModRectangle`.

§12 note: the top-shell comparability lower bound on `e` is formalised (`topShell_e_lower_bound`); the exponent-level consequence for `kappa` is recorded as NOT YET FORMALISED, since the source-exact dictionary it needs is not present in the repository.

STOP.

# Summary of changes for run 207d670f-9cdd-4c86-b15d-ef7ea07a5160
## What I did

I re-verified the CASE-B primitive-fraction bank you sent and then added the statements from it that were **not** yet available as literal Lean theorems. The work is append-only: no previously banked module was edited, and the only change to an existing file is three new `import` lines in `RequestProject/Main.lean`.

### Files added
* `RequestProject/CurrentProgramme/CaseBPrimitiveFractionReproof.lean` — the new mathematics
* `RequestProject/Status/CurrentStatusErdos287CaseBFrontier.lean` — reproof rows + frontier ledger
* `RequestProject/Status/AxiomAuditErdos287CaseBReproof.lean` — `#print axioms` for every new declaration
* `ERDOS287_CASEB_PRIMITIVEFRACTION_REPROOF_BANK_REPORT.md` — the delta report

### New theorems proved (all kernel-checked)
* `Erdos287.CaseBReproof.separation_of_distinct_pairs` — spacing in the form a large sieve actually uses: the hypothesis is that the two standard representatives `(m,t)` are *distinct* (injectivity, which needs only `(t,m)=1`, supplies the nonzero numerator), conclusion `≥ d/(4G²)`, `G = dM`. Unconditional.
* `Erdos287.CaseBReproof.caseB_pipeline_QH_bound` — the end-to-end composition energy → fixed `d` → `S1`/`S2` → global `Q_H`, giving `|Q_H| ≤ B(1+B/G)L·(A c₁(1+log⌊X/H⌋) + 8c₁G²/H)` with the coefficient-energy bound inserted verbatim instead of an abstract hypothesis. The analytic inputs (`hLS`, the `E_g` bound, the Ω_H support/mass normalisation) remain explicit hypotheses, and the extra comparability `G ≤ M` is stated openly.
* `Erdos287.CaseBReproof.normalised_ratio_le_of_comparable` — the `AB ≍ X` source firewall: from `c₀X ≤ AB` the four-term decomposition survives, with the comparability constant appearing on the `G²/(HX)` term only.
* `Erdos287.CaseBReproof.kappa_le_of_critical_range` (with `rpow_max_eq`, `loglog_div_log_tendsto_zero`, `kappa_le_eventually`, `kappa_le_max_zero`) — the exponential critical range in exact form, `κ ≤ max(2θ−1, θ−α) + K·loglog X/log X`, plus the `o(1)` version `κ ≤ max(0, 2θ−1, θ−α) + ε`.
* `Erdos287.CaseBReproof.projector_S1_at_two_G` — the audited `X = 2G` truncation, `S1 ≤ c₁(1 + log(2G/H))`.
* Frontier ledger (`CaseBFrontierStatus`): `frontier_no_closed_rows`, `frontier_unique`, `primitiveFractionCritical_strictly_before_frontier`, `primitiveFractionCritical_not_frontier`, `chain_is_strictly_increasing`, `frontier_erdos287_open`, `caseB_ledger_preserved`. These are bookkeeping statements about the ledger only — `passedThrough` records that a strictly later reduction exists, not that any node is closed — and they assert no mathematical content about the descendant nodes.

### Verification
* Full build of the default target: **PASS** (`Build completed successfully`, 8272 jobs), which also re-checks every previously banked CASE-B module.
* No `sorry`, `axiom`, `unsafe`, `native_decide`, `opaque` or `implemented_by` in the new material.
* Axiom audit: every new declaration depends only on `propext`, `Classical.choice`, `Quot.sound`; several ledger rows depend on no axioms at all.
* Every hypothesis of the pipeline theorem was checked to be load-bearing.

### Unchanged status
The Ω_H normalisation and the `B`/`G` polynomial margins remain **source pins** — nothing was promoted, `SMALL-B` and `SMALL-G` stay open, and Erdős #287 remains **OPEN**. Nothing in this delta claims otherwise.


# Summary of changes for run 22bf2afd-9633-4f07-b525-d9b7294d5167
## CASE-B one-level primitive-fraction large sieve — audit banked

I did not assume any of the incoming statuses: Sections 2–10 were re-derived from scratch in Lean, and each row is backed by a kernel-checked statement. The build succeeds and there is no `sorry`, `axiom`, `unsafe`, `native_decide` or other placeholder in the new material; every new declaration depends only on `propext`, `Classical.choice`, `Quot.sound`.

### Files added
Exact mathematics (`RequestProject/CurrentProgramme/`): `OneLevelPrimitiveFractionSpacing.lean` (§2), `OneLevelCoefficientEnergy.lean` (§4), `OneLevelProjectorS1S2.lean` (§6), `OneLevelWeightedLargeSieve.lean` (§§3, 5), `OneLevelPrimitiveFractionGlobal.lean` (§§7–10).
Status/audit (`RequestProject/Status/`): `CurrentStatusErdos287PrimitiveFractionCaseB.lean`, `AxiomAuditErdos287PrimitiveFractionCaseB.lean`.
Report: `ERDOS287_CASEB_ONELEVEL_PRIMITIVEFRACTION_SAFE_BANK_REPORT.md`.
Only change to a pre-existing file: seven new `import` lines in `RequestProject/Main.lean`. Historical ledgers are imported and re-checked, not edited (`historical_status_preserved`).

### STRICT OUTPUT

```
SPACING: PASS (unconditional)
  primitiveFraction_inj, spacing_lower_bound, spacing_uniform,
  primitiveFraction_separation.  Standard representatives 0 ≤ t < dm force the
  integer shift to 0; only (t,m)=1 is needed, not (t,dm)=1.
  separation ≥ 1/(d m1 m2) ≥ d/(4G²), G = dM.

WEIGHTED LARGE SIEVE: PASS (reduction; analytic input carried as a hypothesis)
  0 ≤ ρ ≤ ‖V‖_∞ with no friability estimate; ∑ρ|S|² ≤ ‖ρ‖_∞ ∑|S|².
  exact factor = A + 4G²/d, from δ = d/(4G²);  no extra log, no X^ε.
  The classical separated-frequency inequality itself is NOT formalised here;
  it appears only as the explicit hypothesis hLS.

COEFFICIENT ENERGY: PASS
  exact bound = ∑_{M≤m<2M} E_{dm}/m² ≤ dB(1+B/G)L^{C_E}, implied constant 1,
  from ∑1/m ≤ 1 and ∑1/m² ≤ 1/M.  No hidden log.  E_g ≤ (gB+B²)L^{C_E} is an input.

FIXED-d (§5): PASS.  (A + 4G²/d)(dK) = (Ad + 4G²)K exactly; all powers of d verified.

S1: PASS
  exact bound = ∑_{d≤X}|λ_H(d)|/d ≤ c₁(1 + log⌊X/H⌋) ≤ c₁(1 + log(X/H)),
  i.e. c₁(1 + log(2G/H)) for X = 2G.  The inner Möbius sum is genuinely truncated
  at ⌊X/H⌋; no d ~ H assumption is used anywhere.

S2: PASS
  exact bound = ∑_{d≤X}|λ_H(d)|/d² ≤ 2c₁/H.

OMEGA_H SOURCE NORMALISATION: SOURCE PIN
  supp Ω_H ⊆ {e~H}, |Ω_H| ≪ 1, ∑|Ω_H|/e ≪ 1, ∑|Ω_H|/e² ≪ 1/H are not theorems
  anywhere in this repository (λ_H is defined for arbitrary Ω).  Carried as the
  hypotheses hsupp, hmass.  Only the lower support and the e⁻¹ mass were needed.

GLOBAL Q_H: PASS
  exact bound = |Q_H| ≤ B(1+B/G)L^{C_E}·( A c₁(1 + log⌊X/H⌋) + 8c₁G²/H )
  envelope    = |Q_H| ≤ 8c₁·B(1+B/G)(A + G²/H)·L^{C_E+1}

NORMALISED RATIO: PASS (exact identity, X = AB)
  |Q_H|/(AB²) = L₁/B + L₁/G + L₀G²/(HX) + L₀G/(HA); four terms independent.

B POLYNOMIAL: SOURCE PIN
G POLYNOMIAL: SOURCE PIN
  No statement A ≥ X^{η_A}, B ≥ X^{η_B}, G > X^{1/2−η₀} occurs in the repository;
  none was manufactured.

1/B: OPEN   1/G: OPEN
  The mechanism is proved unconditionally ((log X)^K/X^η → 0, hence L^K/B ≤ ε
  eventually whenever B ≥ X^η), but its input is an unresolved pin, so
  SMALL-B and SMALL-G obstructions are NOT banked as closed.

H-CRITICAL RANGE:
  H ≤ L^{C_E+K_*}·max(G²/X, G/A),  K_* = 6 + 2η + C_route;
  exponentially κ ≤ max(0, 2θ−1, θ−α) + o(1).

PROMOTED THEOREMS:
  DET1-ONELEVEL-PRIMITIVEFRACTION-SPACING45  : PASS (exact, unconditional)
  DET1-ONELEVEL-dRESTRICTED-LS45             : PASS (conditional reduction)
  DET1-ONELEVEL-COEFFENERGY45                : PASS (conditional on E_g input)
  DET1-ONELEVEL-PROJECTOR-S1S2-45            : PASS (conditional on Ω_H pin)
  DET1-ONELEVEL-PRIMITIVEFRACTION-GLOBAL45   : PASS (conditional on the above)
  ERDOS287 CLOSED                            : NOT BANKED

ERDOS287: OPEN

FIRST EXACT RESIDUAL:
  287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-PRIMITIVEFRACTION-CRITICAL45
  range: H ≤ L^{C_E+K_*} max(G²/X, G/A)
  retains: μ(m); primitive t mod dm; reciprocal-b source; friable a;
           exact signed λ_H(d)/d² projector.
```

Two audit notes on the source statements as given: the sieve factor carries the explicit absolute constant 4 (`A + 4G²/d`) coming from `δ⁻¹ = 4G²/d`, and the S1 factorisation only yields `1 + log(2G/H)` if the inner Möbius sum is kept truncated at `⌊X/H⌋` — both are reflected in the banked statements. No work was done beyond this audit.


# Summary of changes for run 5c7ec803-72e5-4b06-9236-9c455af6a33f
Banked the requested **ONE-LEVEL MÖBIUS append-only delta** for Erdős #287 (§§0–16). The delta is strictly additive: no protected module was rebuilt or edited, and the only change to a pre-existing file is nine new `import` lines in `RequestProject/Main.lean`.

## Files added

**Exact algebra** (`RequestProject/CurrentProgramme/`):
- `LevelPairProductModulus.lean` — §§1–3, §5
- `LevelPairFixedDRigidity.lean` — §4
- `LevelPairReciprocalNormalForm.lean` — §6
- `LevelPairPrimeAssignment.lean` — §§7–8
- `SharedGcdGramSquare.lean` — §§9–10
- `PrimitiveTRamanujanFirewall.lean` — §12
- `SharedGcdOneLevelMobiusSocket.lean` — §§11, 13

**Status / audit** (`RequestProject/Status/`):
- `CurrentStatusErdos287OneLevelMobius.lean` — §14
- `AxiomAuditErdos287OneLevelMobius.lean` — §15

**Report**: `ERDOS287_ONELEVEL_MOBIUS_SAFE_BANK_REPORT.md` — §16.

## Principal theorems proved

- **Product-modulus compression**: `moebius_levelPair_compress`, `moebius_levelPair_eq_moebius_n` (μ(g1)μ(g2)=μ(n)), `lcm_levelPair_eq` (lcm(g1,g2)=g0·n), `levelPair_norm_eq` (1/(g1g2)=1/(g0²n)).
- **`gcd_D_n_eq_one`** — proved *directly* from primitivity, with the older `gcd(D,Λ) ∣ g0` recorded separately.
- **Divisor split / reindexing**: `unitary_split_coprime/_dvd`, `levelPair_divisorSplit`, `levelPair_reindex_fixed_n`, `levelPair_reindex`. No asymptotic dyadic ranges formalised.
- **Fixed-D rigidity**: `t1_congr_mod_r1`, `t2_congr_mod_r2`, `fixedD_solution_iff` (exact iff for `t1=xD+r1u`, `t2=yD+r2u`), `fixedD_u_period_g0` (`u mod g0`), `fixedD_primitive_reduces_to_g0_side`.
- **Farey kernel**: `fareyDifference_eq_D_div_g0n` (`t1/g1 − t2/g2 = D/(g0n)`) and `fareyDifference_split_invariant` — independence of the split `r|n`. No analytic property of Φ_A formalised.
- **CRT reciprocal normal form**: `exists_crtBeta`, `gcd_two_g0_beta_eq_one`, explicit numerator `crtNumerator` (Ξ_r), `reciprocal_phase_normalForm`, `reciprocal_normalForm_of_inverse`.
- **Fixed-n prime assignment**: `fixed_n_two_state_product` — banked as a fixed-`n` factorisation only; **no** multiplicativity in `n` asserted.
- **Non-multiplicativity firewall**: `localFactorK_not_multiplicative` — one explicit finite counterexample, K(15)=4 ≠ 1 = K(3)K(5). No universal negation.
- **Shared-gcd Gram-as-square** (highest-priority bank): `sum_lambdaH_divisors` (Möbius inversion of Ω_H), `sharedGcd_gram_square`, and the one-level form `sharedGcd_oneLevel_gram`; plus `abs_lambdaH_le`, `lambdaH_harmonic_mass_le`, `omega_support_mass_le`. Only the exact convolution inequality is banked; the asymptotic `≤ C/H` is left as research metadata.
- **Primitive-t Ramanujan firewall**: `ramanujan_prime_not_dvd` (c_p = −1), `ramanujan_prime_dvd` (c_p = p−1), `moebius_mul_ramanujan_prime`, and the re-exported divisor normal form. The ζ(1+w)/ζ(2+2w) Euler-product claim is **not** formalised.
- **Status ledger** (§14, all rows as specified): `no_closed_rows`, `erdos287_open`, `uniform_k0_open_fcl_not_reached`, `amplitude_exponents` (near-density 1/2, final amplitude 1/4), `cauchyConfiguration_superseded_not_closed`, `largeSharedG0_retracted_and_nearFreq_open`, `energy_subpolytope_provisional_not_closed`, `oneLevelMobiusGram_is_first_exact_residual` (uniqueness of rank 1), `signed_levelPair_gram_strictly_reduced`, `exact_rows_are_theorems`, `gram_square_and_one_level_are_theorems`, `nonmultiplicativity_firewall_is_explicit`, `historical_sharedG0_status_preserved`.

## Analytic firewall

Both new analytic interfaces are left **UNINHABITED** by design, each with an explicit refutation showing the hypothesis is genuine and not automatic:
- `SharedGcdOneLevelEnergyInput` (§11) — the subpolytope is **not** marked closed; only the satisfiability of the constraint set (`exists_valid_energyLedger`) is formal.
- `SharedGcdOneLevelMobiusGramInput` (§13) — retains primitive `t`, the reciprocal `b` source, the friable `a` source and the harmonic/Perron parameters; primitive `t` is **not** completed inside the socket.

All pre-existing analytic sockets remain uninhabited.

## Build and axiom audit

- Targeted builds of both new Status modules: success.
- Full `lake build`: **Build completed successfully (8262 jobs), 0 errors.** No new warnings; the warnings present are pre-existing in historical modules, deliberately left untouched.
- The audit module runs `#print axioms` over **90** audited declarations. Every one depends only on `propext`, `Classical.choice`, `Quot.sound` (several on strictly fewer; one on none). A filtered scan for any axiom outside the allowed list returns nothing.
- Source scan of all ten new files for `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `implemented_by`: **no occurrences** (only prose hits inside comments).

## Commits

Seven commits, all pushed to `origin`; working tree clean.

**FINAL: ERDOS287 OPEN. CURRENT FIRST EXACT MAIN-LINE RESIDUAL: 287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-MOBIUS-GRAM45.**

# Summary of changes for run b63c35a5-f054-4172-b072-f088bae33c4c
Completed the append-only SHARED-g₀ / reduced-denominator / Cauchy-repair formal delta for Erdős #287. Nothing historical was rebuilt or superseded; the only change to an existing file is ten added `import` lines in `RequestProject/Main.lean`. `ARISTOTLE_SUMMARY.md` and `CurrentStatusErdos287PrimitiveLocalProfile.lean` were not edited, and both `ShortLiftEulerAnalyticInput` and `PrimitiveLocalProfileGramInput` remain uninhabited.

**New files (all `sorry`-free and building):**

- `RequestProject/CurrentProgramme/LocalProfileHarmonicTwists.lean` (§1) — the exact finite harmonic-twist identity `mProfile_harmonic_twist_expansion`: m_{g,b}(Δ) = Σ_{ℓ | rad(2bg)} (1/ℓ)·twistInner ℓ, over the repository's own `mProfile`, via `moebius_coprime_twist_sum`. The asymptotic L¹-cost claim is deliberately not formalised.
- `RequestProject/CurrentProgramme/SharedG0PrimitiveUParam.lean` (§2) — `sharedG0_u_param_iff`, `sharedG0_u_period`, the primitive exclusions `primitive_not_dvd_t1/_t2`, `excludedU_eq_iff_dvd_D` (the two forbidden residues coincide iff p | D), and `card_excludedU` = ν_p(D).
- `RequestProject/CurrentProgramme/SharedG0PrimitiveURouter.lean` (§3) — `primitiveUSum_eq_complete_sub_excluded` (exact local factor), the two elementary bounds `norm_primitiveUSum_le_modulus` (|U_p| ≤ p) and `norm_primitiveUSum_le_two` (|U_p| ≤ 2 when p ∤ C), the deduction `abs_prod_local_le` (|∏_p U_p| ≤ 2^ω(g₀)·gcd(g₀,C)), and the CRT factorisation `primitiveUSum_crt_split` in exact two-factor form U_{mn}(C) = U_m(Ca)·U_n(Cb).
- `RequestProject/CurrentProgramme/SharedG0UnitSectorGcd.lean` (§4) — `sharedGcd_reciprocalDiff_eq_originalDiff`: gcd(g₀, (2b₁)⁻¹−(2b₂)⁻¹) = gcd(g₀, b₁−b₂), plus the unit-twisted version. The coprimality side condition is derived rather than assumed.
- `RequestProject/CurrentProgramme/SharedG0BPairAveraged.lean` (§5) — `gcd_eq_sum_totient_divisors`, the exact-floor interval count `pairCountCongruentModulo_le`, and the finite precursor `bpair_gcd_sum_le_divisorCount`: Σ gcd(g₀,b₁−b₂) ≤ B²τ(g₀) + B·g₀.
- `RequestProject/CurrentProgramme/PrimitiveReducedDenominator.lean` (§6) — `lcm_sharedG0_eq`, `gcd_D_lambda_dvd_g0` (proved via coprimality with r₁ and r₂ separately, so valuation-safe with no squarefree hypothesis), `reducedDenominator_eq` and `reducedDenominator_ge` (den(D/Λ) ≥ r₁r₂ = g₁g₂/g₀²).
- `RequestProject/CurrentProgramme/PrimitiveNearFreqCount.lean` (§7) — reuses the banked Farey machinery: `nearFreqSet_eq`, `nearFreq_D_mem_Icc`, and the exact count `nearFreqSet_card_le`: N_near ≤ g₀ + 2g₀⌊g₀r₁r₂H/A⌋. No analytic saving is claimed.
- `RequestProject/CurrentProgramme/SharedG0CauchyConfigurationSocket.lean` (§9) — the uninhabited `SharedG0CauchyConfigurationInput` over a `CauchyLedger` carrying the five ledger quantities, with audit item A (averaged router, θ_U < 1) and audit item B (root consistency, the 1/4-vs-1/2 dichotomy) formalised, a trivial conditional consumer, and `sharedG0CauchyConfiguration_not_automatic` refuting it with explicit data.
- `RequestProject/Status/CurrentStatusErdos287SharedG0Repair.lean` (§11–12) — the new ledger with kernel-checked integrity theorems: no closed row, ERDOS287 open, UNIFORM k=0 open, FCL not reached, both analytic children `repairPending`, the hard-denominator child `pendingChild` (conditional, rank 0, not inhabited), LOCALPROFILE-GRAM45 `strictlyReducedBlocked`, the Cauchy configuration the unique first exact residual, every exact row backed by the actual quoted statement of §§1–7, and the historical LOCALPROFILE/BLOCK20 ledgers re-checked as unmodified. The short-lift Euler row carries `nancVerifiedPassUninhabited` — a research-metadata label only; no analytic statement is proved in Lean.
- `RequestProject/Status/AxiomAuditErdos287SharedG0Repair.lean` (§13) — `#print axioms` for all 64 new principal declarations.
- `ERDOS287_SHAREDG0_CAUCHY_REPAIR_SAFE_BANK_REPORT.md` (§14) — the full report.

**Build:** each new module builds cleanly (no errors, no warnings), and the full `lake build` completes successfully (8253 jobs).

**Placeholders:** none. No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, or `implemented_by` in any new file; the only textual match in the repository is the prose of the audit file's own docstring.

**Axioms:** every audited declaration depends on a subset of `propext`, `Classical.choice`, `Quot.sound`; three of the ledger theorems depend on no axioms at all.

All work is committed and pushed. ERDOS287 remains OPEN; the current first exact research residual is 287-K0-SP2-DET1-SHAREDG0-CAUCHY-CONFIGURATION45.

# Summary of changes for run 73505396-e329-44ca-9d1a-3ad8016591e6
Delivered the PRIMITIVE-CONDUCTOR / SHORT-LIFT → PRIMITIVE-LOCALPROFILE delta as an append-only layer. Everything is exact algebra / finite combinatorics; no analytic number theory is claimed, and Erdős #287 is **not** claimed solved.

**Files added** (no historical file modified; `RequestProject/Main.lean` received import lines only):
- `RequestProject/CurrentProgramme/PrimitiveRamanujanAlgebra.lean` (§A)
- `RequestProject/CurrentProgramme/PrimitiveRamanujanReassembly.lean` (§B)
- `RequestProject/CurrentProgramme/ShortLiftLocalProfile.lean` (§C)
- `RequestProject/CurrentProgramme/PrimitiveDMultiplicity.lean` (§D)
- `RequestProject/CurrentProgramme/PrimitiveFareyNearCollision.lean` (§E)
- `RequestProject/CurrentProgramme/PrimitiveLocalProfileGramSocket.lean` (§F)
- `RequestProject/Status/CurrentStatusErdos287PrimitiveLocalProfile.lean` (§G)
- `RequestProject/Status/AxiomAuditErdos287PrimitiveLocalProfile.lean` (§H)
- `ERDOS287_PRIMITIVE_LOCALPROFILE_SAFE_BANK_REPORT.md`

**FORMALLY PROVED.** The Ramanujan sum is built from the repository's own additive phase e(x)=exp(2πix): c_g(N)=∑_{t<g, gcd(t,g)=1} e(tN/g). From that definition: the complete additive sum ∑_{t<g}e(tN/g)=g·1_{g∣N}; `ramanujan_eq_divisor_sum` (DET1-PRIMITIVE-RAMANUJAN-DIVISOR-NORMALFORM45) c_g(N)=∑_{r∣gcd(g,N)} r·μ(g/r); `ramanujan_unit_shift` (DET1-PRIMITIVE-T-RAMANUJAN45) c_g(a+s·w)=c_g(2ab+s) for 2b·w≡1 (mod g); `moebius_mul_moebius_div` (μ(g)μ(g/r)=μ(r) for squarefree g=rk, gcd(r,k)=1) and `ramanujan_moebius_normalForm` (DET1-RAMANUJAN-MOBIUS-SIMPLIFICATION45) μ(g)/g·c_g(N)=∑_{rk=g, r∣N} μ(r)/k. §B: the branch identity ∑_{kd=n} μ(d)1_{gcd(2b,k)=1}1_{gcd(b,d)=1}=[n=1] on the coprime sector (the r>1 cancellation), ∑_{d∣n,d<n}μ(d)=−μ(n) for n>1, and `primitive_ramanujan_reassembly` (DET1-PRIMITIVE-RAMANUJAN-REASSEMBLY45): reassembly returns exactly raw progression − additive zero mode — a representation loop, verified, not an estimate. §C: the finite/dyadic profile mProfile(g,b,D) with Ψ, plus the finite Euler product ∑_{d∣n,gcd(d,H)=1}μ(d)/d = ∏_{p∣n,p∤H}(1−1/p) = (∏_{p∣n}(1−1/p))·∏_{p∣n,p∣H}(1−1/p)⁻¹ (the finite-prime-product avatar of H_H/ζ). §D: the solution line t₁=t₁⁰+r₁u, t₂=t₂⁰+r₂u and DET1-PRIMITIVE-D-MULTIPLICITY45 (≤ g₀+1 solutions in the box; the sharp g₀ is also banked). §E: lcm(g₀r₁,g₀r₂)=g₀r₁r₂, the exact rational implication |t₁/g₁−t₂/g₂|≤1/A ⟹ |D|≤lcm(g₁,g₂)/A, and the exact finite count ≤ (2⌊lcm/A⌋+1)·g₀ with explicit integer floors.

**ANALYTIC / UNINHABITED.** `ShortLiftEulerAnalyticInput` (Dirichlet-series ∑_{gcd(d,H)=1}μ(d)d^{-s}=H_H(s)/ζ(s)) and `PrimitiveLocalProfileGramInput` (|Gram| ≤ C·X·log^{−3−η}X over valid primitive-conductor configurations retaining π, s, τ, g, primitive t, friable a, Möbius b, mProfile(g,b,Q/g), μ(g), smooth weights) are stated and never inhabited; each has only a trivial conditional consumer, plus explicit refuting data and a nonempty valid-configuration witness, so neither is vacuous or automatic. Nothing of the shape exp(−c√(log D)) is formalised. The asymptotic wrapper gcd(g₁,g₂)+g₁g₂/A is left unformalised; only the exact finite precursor is banked.

**STATUS LAYER (append-only).** New ledger: PRIMITIVE-CONDUCTOR-SHORTLIFT-GRAM45 = superseded-but-not-false (never closed, never false); PRIMITIVE-LOCALPROFILE-GRAM45 = analytic open / uninhabited / first exact main-line residual; UNIFORM k=0 = open; FCL = not reached; ERDOS287 = open; no closed row. The imported BLOCK20 ledger is unchanged and re-checked.

**BUILD / AXIOM AUDIT.** `lake build` succeeds (8243 jobs, 0 errors); each new module also builds individually and is warning-free (the only repository warning is the pre-existing note in a historical file). No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `@[implemented_by]` in any new file. `#print axioms` over every principal new declaration yields only subsets of {propext, Classical.choice, Quot.sound} (two status rows use none). All work is committed and pushed.

ERDOS287 OPEN. FIRST EXACT MAIN-LINE RESIDUAL: 287-K0-SP2-DET1-PRIMITIVE-LOCALPROFILE-GRAM45.

# Summary of changes for run a4b08109-0d68-4e6a-902d-e7011eadcb70
SOURCE-SEAL REPAIR:
Attempted literally in `RequestProject/CurrentProgramme/FixedCertificateBalancedSevenSourceSeal.lean`, starting from the repository's own fixed-certificate smooth-parity packet (no model object). Proved: the k=0 / J=∅ / P⁺(n) ≤ n^σ_* reduction to the truncated Möbius sum (`fixedCertificate_k0_Jempty_reduction`, `fixedCertificate_smoothCut_reduction`); the finite seven-box identity `H_*(P) = −20` through the repository definitions (`fixedCertificate_sevenBox_eq_neg20`); the weight dictionary with explicit exclusion of hidden Λ(p), log p, 1/log p (`omegaBox_dictionary`, `omegaBox_carries_no_vonMangoldt_factor`, `_no_log_factor`, `_no_inverse_log_factor`), keeping the affine log r from Λ = μ∗log separate (`vonMangoldt_sum_divisors_eq_log`); and `balancedSevenSeal_of_cellIdentity`, which derives the whole seal from one remaining hypothesis. The seal is NOT inhabited.

SOURCE-SEAL RESIDUAL:
`Erdos287.Block20.FixedCertificateSP2PacketMatchesCompilerPacket` — identification of the literal repository fixed-certificate SP-2 packet with the packet consumed by the Balanced7 compiler (the `cell_identity` field). Status remains SOURCE_OPEN, with `sourceSeal_residual_not_automatic` refuting automaticity.

BLOCK20 PACKING:
Procedural greedy rule formalised (`bigAtoms`/`smallAtoms`/`groupSmall`/`packSide`/`packBoth`) with exact conservation (`packSide_perm`: no atom lost or duplicated), deterministic singleton vs grouped provenance, no d/m straddling, non-final block mass ≥ σ_*/3, block mass ≤ σ_*, ≤ 2 leftovers. `Block20PackingValidity` is separate and inhabited constructively by `packBoth_validity`, with `block20Validity_not_automatic` showing it is not vacuous. Ledger: ν₀ = 16623/100000 exactly (never 1/6), σ_* = ν₀ − 2ε_*, `sigmaStar_ge : σ_* ≥ 0.1629054`, `nineteen_blocks_overflow : 19·(σ_*/3) > 1`, `eps_one_over_600_not_admissible`.

BLOCK20 COUNT:
≤ 20 (`nonfinal_block_count_le_18` plus at most two leftovers; `template_block_count_le_20`).

TRUNCATED MÖBIUS:
Exact finite divisor factorisation e = e_d·e_m proved (`truncMobius_coprime_split`, `truncMobius_gamma_split`); smooth/rough split at z₀ = X^(1/420) with `block20_gcd_smooth_rough` (gcd(d,m)=1) and `bigOmega_rough_le_420`.

BILINEAR SOURCE COMPILER:
`template_product_split` (∏ all = u·v), `template_predicate_split`, `template_mass_split`, `fixed_template_source_factorisation` (ξ_π(u)·κ_π(v) once external inputs are supplied), with the remaining joint predicate exposed as `joint_coprimality_predicate_not_factorisable`. ξ/κ are defined from the packed block grammar (`mobius_factor_occurs_once`, `ordered_block_convolution`), and the divisor-norm bounds are the uninhabited `GeneratedCoefficientNormInput`.

TYPE-II WINDOW:
Proved finite: ε_* ≤ selectedMass < ε_* + σ_* = ν₀ − ε_* (`typeII_window_from_first_crossing`, `typeII_window_endpoint`, `typeII_size_window`); E is template-fixed (`template_selection_not_recomputed`). The log-mass → literal X-power conversion is kept as an explicit input, not faked.

THREE-SMALL-PRIME STATUS:
SUPERSESSION CANDIDATE / SOURCE COVERAGE OPEN; explicitly NOT false (`threeSmallPrime_not_false`, `threeSmallPrime_class_is_nonempty`, conditional `threeSmallPrime_supersession_of_coverage`).

PERRON SOCKET:
`PerronConditionRemovalInput` — granular (source cutoff, truncated integral representation, kernel K(τ), vertical range, kernel L¹ budget, boundary-strip source and estimate, truncation error, exact reconstruction), uninhabited, with a proved conditional compiler to `SeparatedPrefixCoefficientFamily`; C_Perron = 1 recorded as external audit metadata only.

BOUNDARY ROUTER:
`PerronBoundaryRouterInput`, uninhabited, plus the firewall theorems `boundaryRouter_preserves_literal_source` and `smoothed_certificate_is_a_different_source` (no replacement of H_* by a smoothed certificate).

GENERATED TYPE-II SOCKET:
`Block20GeneratedTypeIIInput` quantifies only over actual Block20 templates, actual ξ_π/κ_π, the supported window, both signs, physical weights. Uninhabited. Conditional compiler `k0_uniform_fragmentation_compiler` to `K0UniformFragmentationConclusion`, which is not inhabited.

CURRENT MAIN-LINE ANALYTIC RESIDUAL:
287-K0-SP2-BLOCK20-GENERATED-TYPEII45

EFFECTIVITY RESIDUAL:
287-EXCEPTIONAL-MAINTERM-COMPARISON-ADAPTER45 (uninhabited adapter, all three routes left undecided, conditional compiler to `EffectiveSmallQLowConductorConclusion`).

FCL: OPEN
ERDOS287: OPEN

TARGETED BUILDS: all new modules built individually, 0 errors.

FULL BUILD: `lake build` — 8235 jobs, 0 errors. Only the pre-existing linter warning in the historical file `RequestProject/Erdos287/FixedCertificateSmoothParity.lean:60` remains; it was left untouched.

AXIOM AUDIT: `RequestProject/Status/AxiomAuditErdos287Block20.lean` prints axioms for every principal new declaration — all are subsets of {propext, Classical.choice, Quot.sound}. Trust scan of the new files: zero sorry, admit, axiom, opaque, unsafe, native_decide, @[implemented_by]. No analytic or source socket of this pass has an inhabitant anywhere in the repository.

FILES: added `RequestProject/CurrentProgramme/{FixedCertificateBalancedSevenSourceSeal, Block20PackingCompiler, Block20LargePrimePowerRouter, Block20GeneratedBilinearCompiler, PerronConditionRemovalCompiler, ExceptionalMainTermComparisonAdapter}.lean`, `RequestProject/Status/{CurrentStatusErdos287Block20, AxiomAuditErdos287Block20}.lean`, and `ERDOS287_BLOCK20_DELTA_SAFE_BANK_REPORT.md`. `RequestProject/Main.lean` received import lines only. No historical file was otherwise modified.

COMMITS: staged in phases (source seal; packing/bilinear compiler; Perron/generated Type-II/effectivity sockets; status + audit + Main imports + report).

PUSH: all commits pushed to origin.

FINAL FIREWALL: this formal layer certifies finite source algebra, deterministic Block20 packing, source dependency graphs and conditional compilers only. It does NOT prove 287-K0-SP2-BLOCK20-GENERATED-TYPEII45, Perron analytic error estimates, the exceptional comparison adapter, FCL, or Erdős #287.

ERDOS287 OPEN —
FIRST EXACT MAIN-LINE ANALYTIC RESIDUAL:
287-K0-SP2-BLOCK20-GENERATED-TYPEII45

# Summary of changes for run 2992f52e-6ca3-4d37-b918-35cb1438b1a0
The Balanced7 hostile-audit safe bank is complete, built, and pushed. All work was append-only: no historical V15–V24 / SP-2 / PostBalanced7Pro file and no summary file was modified.

**Files added**

`RequestProject/HostileAudit/`
- `BalancedSevenSP2SourceAdapter.lean` (§2) — `truncMobius_of_primeProduct`, `truncMobius_sevenBox_eq_neg20` (the literal finite identity `H_*(P) = 1−7+21−35 = −20`), `subsetAlternatingSum_eq_binomial`, `boxWeight` with `norm_boxWeight_le_one` / `boxWeight_eq_omegaBox` (|phase| = 1, 0 ≤ V ≤ 1), the seal structure `BalancedSevenSP2SourceSeal` (left **uninhabited**), `seal_rigidity`, `sp2SourceSeal_not_automatic`.
- `GeneralModulusInducedCharacter.lean` (§3) — `induced_character_pointwise` (χ_r(n) = χ*(n)·1_{gcd(n,j)=1}, no squarefreeness or gcd(f,j)=1 hypotheses), `inducedSpec_holds_for_nonSquarefree_modulus`, `coprimeIndicator_moebius_expansion`, `induced_character_moebius_form`.
- `TotientComplementaryFactor.lean` (§4) — `totient_mul_ge`, `totient_gcd_exact`, `complementary_factor_bound` (f > D ∧ R ≤ f·j < 2R ⇒ j < 2R/D), `divisorVariable_ne_complementaryFactor` firewall.
- `GeneralModulusConductorSplitLargeSieve.lean` (§5) — uninhabited `PrimitiveWeightedLargeSieveInput` and `DivisorSumPolylogInput`, plus the conditional `general_modulus_cell_bound` and `general_modulus_conductorSplit_compiler`.
- `SmallROwnerCapacity.lean` (§7) — `smallR_source_eq_principal_add_defect` and the exact defect identity, `smallR_owner_assignment` (principal → EulerPrincipal, defect → SmallRDirect), `smallR_modulus_capacity` (q ≥ X^{2/3}), uninhabited `SmallRPrincipalCapacityInput`.
- `ShortTResidueGeometry.lean` (§8) — `shortT_unique_forbidden_class` (∃! residue class when ℓ ∤ q), `shortT_constant_class_of_dvd`, the rational scale ledger 2/105 < 15/105, `smallPrime_not_dividing_YscaleProduct`; the Selberg estimate stays uninhabited as `BalancedSevenShortTSieveInput`.
- `ShiuHypothesisCompiler.lean` (§9) — exponent map 5/7, 3/4, margin 1/28; `shiu_shift_coprime` (gcd(±1, 2w′) = 1); uninhabited `BalancedSevenShiuInput` with a conditional consumer.
- `RawRawVarianceCompiler.lean` (§10) — `rawRaw_variance_bound` with the corrected `log^{-5}` saving, `rawRaw_saving_is_five_not_ten` (explicit refutation of `log^{-10}`), `cross_variance_bound` (`log^{-15/2}`) and the principal `log^{-10}` bound.
- `HardAmplitudeExponentCompiler.lean` (§11) — reuses `C_ext = 1`, `hard_amplitude_product` (M·W5 = X with M = X^{2/7}, W5 = X^{5/7}), `hard_cell_log_budget` (−5/2), `hard_dyadic_summation` (−3/2), uninhabited `HardAmplitudeAsymptoticInterface` for the o(1).
- `FullQExactReassembly.lean` (§12) — literal boundary ownership of the disjoint partition SmallQ / SmallR / Hard, `region_principals_sum_eq_full`, `no_region_owns_the_full_principal`, `fullQ_no_double_spending`, `even_q_is_impossible`, `q_coprime_twoP`.
- `EffectiveLowConductorExceptionalPNT.lean` (§15) — uninhabited `EffectiveLowConductorExceptionalPNTInput` (effective constants, exceptional-character secondary term, smooth Y-scale weight, f ≤ log^30 X, Mellin range, induction to q), the conditional consumer to `EffectiveSmallQLowConductorTarget`, and `effective_socket_is_not_siegelWalfisz`.
- `BalancedSevenHostileAuditCompiler.lean` (§13) — `BalancedSevenHostileAuditInputs` (exactly the eight audited fields), the conditional `balancedSeven_hostileAudit_compiler`, and `hostile_audit_is_not_a_lean_proof`.

`RequestProject/Status/`
- `CurrentStatusErdos287Balanced7HostileAudit.lean` (§14, §6, §16) — the new append-only ledger with the recommended rows, the two **RETRACTED** death certificates with their reasons, the downstream frontier rows, `ledger_is_honest`, `rawRaw_row_uses_the_corrected_exponent`; no `Status.closed` row, ERDOS287 and FCL remain `open_`.
- `AxiomAuditErdos287Balanced7HostileAudit.lean` (§17) — `#print axioms` over every principal new declaration.

`RequestProject/Main.lean` — import lines only. Report: `ERDOS287_BALANCED7_HOSTILE_AUDIT_SAFE_BANK_REPORT.md`, containing the mandated final block and final firewall.

**Build:** `lake build` succeeds — 8227 jobs, 0 errors. The only warning in the repository is the pre-existing linter note at `RequestProject/Erdos287/FixedCertificateSmoothParity.lean:60`, which was left untouched.

**Trust:** no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `@[implemented_by]` occurs in any new file (the only textual hits are prose in docstrings describing the scan). `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound` for the new principal declarations. Every analytic/source interface of this layer is uninhabited, each accompanied by a refutation theorem exhibiting explicit failing data.

**Verdicts.** BALANCED7 SOURCE SEAL: **SOURCE_OPEN** — the finite `H_*(P) = −20` identity and the smooth-box weight bounds are kernel-proved, but the literal identification of the compiler-consumed packet with the repository's fixed-certificate SP-2 packet could not be derived from the current definitions, so Balanced7 is **not** recorded as source-sealed. SMALLQ, SMALLR GENERAL MODULUS, SHORT-t, SHIU, RAW-RAW: hostile-audited external pass recorded as conditional compilers only. SMALLR OWNER and FULL-q OWNER: proved algebraically. BALANCED7: research/paper pass, not a Lean analytic theorem; Balanced7-effective open. FCL and ERDOS287 remain open, and nothing is claimed closed.

# Summary of changes for run 0b028c11-5b14-4718-88f5-d9d6ac7b179f
## Post-Balanced7 safe bank — completed (append-only)

The earlier BALANCED7 post-audit repair bank was already in place; this session completed the follow-on **conductor-split 34LS / SmallR owner / hard-δ / small-prime-prefix Type-II** pass. Everything is append-only: no historical V15–V24 / SP-2 bank, status row, report, or pass-1 module was modified.

### Files added (all under the requested `RequestProject/CurrentProgramme/` and `RequestProject/Status/`)

- `CurrentProgramme/SevenBoxPrimeWeights.lean`, `CurrentProgramme/PrimeTupleMultiplicity.lean` — prime-supported seven-box weights; exact labelled multiplicity `≤ k!`, giving `∑|a₃|² ≤ 6·∏E` and `∑|b₄|² ≤ 24·∏E` (repeated primes included, no injectivity assumed).
- `CurrentProgramme/ConductorSplitLargeSieve.lean` — character families supplied as data (no ambient character-API dependence), literal character sums, the **exact conductor split** (cover / disjoint / monotone / reassembly), and the Möbius expansion of the coprimality indicator.
- `CurrentProgramme/LowConductorSiegelWalfisz.lean` — internal cutoff `(log X)^30`, a proof that it is a *different function* from the physical cutoff `X^{1/3}`, an explicitly **ineffective** Siegel–Walfisz socket, and a finite aggregation consumer.
- `CurrentProgramme/SmallQ34LSCompiler.lean` — three-child `ε/3` bundle → SmallQ target bound, plus a proof that the outstanding obligation really is the normalisation child.
- `CurrentProgramme/SmallPrimePrefix.lean` — `z₀ = X^{1/420}`; smooth/rough factorisation with **existence and uniqueness**; the `Ω(d) ≥ 3` firewall; the truncated-Möbius **non-factorisation** obstruction (explicit counterexample `M₂(2)=0` vs `M₂(3)=1`); literal residual sum and its socket.
- `CurrentProgramme/PostRepairOwnerCompiler.lean` — refined owner map (6 owners / 9 cells, dedicated short-`t` and `Ω(d)≥3` owners), unique ownership, no double spending, conditional compiler.
- `CurrentProgramme/UniformFragmentationCompiler.lean` — K0 uniform fragmentation reassembly compiler, banked as REDUCED / CONDITIONAL and never activated.
- `Status/CurrentStatusErdos287PostBalanced7Pro.lean`, `Status/AxiomAuditErdos287PostBalanced7Pro.lean` — new append-only ledger with `no_closed_rows`, `erdos287_open`, `balanced7_open`, `k0_is_reduced_not_closed`, residual-ordering and honesty theorems; full `#print axioms` audit.
- `RequestProject/Main.lean` — import lines only, inserted inside the import block.
- `ERDOS287_POST_BALANCED7_PRO_SAFE_BANK_REPORT.md` — full report with the mandated final block and firewall.

### Verification

- **Build:** full `lake build` succeeds (8213 jobs, 0 errors). One pre-existing, unrelated linter warning in `RequestProject/Erdos287/FixedCertificateSmoothParity.lean:60` remains untouched.
- **Trust scan:** zero occurrences of `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `@[implemented_by]` in all new files.
- **Axioms:** every principal declaration of this pass depends only on `propext`, `Classical.choice`, `Quot.sound`.
- **Interfaces:** every analytic/source socket is uninhabited, each with an accompanying refutation theorem exhibiting explicit failing data.

### Status kept open

BALANCED7, FCL and Erdős #287 remain **open**; no `closed` row exists. The first exact residual is the SmallQ 3+4 coefficient/source normalisation; the first exact downstream residual is the `Ω(d) ≥ 3` small-prime-prefix Type-II input. The hard-θ `δ = 1/21` ledger is banked as rational/order arithmetic only.

Note on naming: the requested `TwinPrimeProject.*` namespace does not exist in this repository, so the established `Erdos287.*` convention was used (`Erdos287.PostBalanced7Pro`, `Erdos287.PostBalanced7ProStatus`); this is recorded in the report. The referenced research-ledger markdown file is not present in the repository, so Lean declarations were used as the sole authority for formal claims.


# Summary of changes for run 0c8f71d8-a099-4200-a479-de6e0f37f241
Continued the Erdős #287 repository in place, append-only. The comparison / aggregate-Euler safe bank (V23) was already banked and pushed; this session completed and banked the follow-on **V24 full-`q` Balanced7 provider-exhaustiveness layer**, chosen as the next consistent version identifier after V23. `ARISTOTLE_SUMMARY.md` was not modified, and the V20/V21/V22/SP-2/V23 layers are untouched.

**Files added** (all under `RequestProject/`):
- `Erdos287/PhysicalLogPrefactorRepair3221.lean` — repaired physical log prefactor `C_ext = 1`, machine-checked retraction of the old `C_ext = 0` normalization, `Q = X^{3/5}` numerology (net log exponent `−5/2`, signed margin `3`).
- `Erdos287/SP2LiteralPhysicalSource3221.lean` — literal one-sign SP-2 physical source, two-sign reassembly, and the non-circularity firewall that `2B(P)` is not recoverable from the principal q-cell.
- `Erdos287/EulerUniformityLayer3221.lean` — repaired Euler local factor with explicit bound `|f − 1| ≤ 6·p^{−7/4}` (real `w ≥ −1/4`), at most seven on-`P` corrections, `H_P(0) = 2B(P)`, plus an uninhabited analytic uniformity interface.
- `Erdos287/FullQStructuralPartition3221.lean` — cut `U = X^{1/3}`, exact SmallQ/SmallR/Hard cover, disjointness and reassembly, dyadic partition of unity with the proved firewall that smooth supports need not be disjoint, and provider ownership.
- `Erdos287/SmallQSmallRAdapters3221.lean` — literal sector sums with exact reassembly; uninhabited SmallQ and switched-SmallR Type-I adapter interfaces plus conditional consumers; proof that `q ↔ r` is not a symmetry of the sector decomposition.
- `Erdos287/HardDyadicProviders3221.lean` — `Q = X^{3/5}` cell metadata (with `Q·R = X`), hard dyadic census, and a *refuted* exhaustiveness interface.
- `Erdos287/BalancedSevenFullQCompiler3221.lean` — conditional full-`q` compiler and firewalls, including the proof that the antecedent bundle is currently satisfiable by no parameter set.
- `Status/Erdos287V24Status.lean`, `Status/AxiomAuditErdos287V24.lean`; `Main.lean` extended with import lines only; report `ERDOS287_FULLQ_BALANCED7_PROVIDER_SAFE_BANK_REPORT.md` with the mandated final block and final firewall.

**Build and trust:** `lake build` completes successfully — 8190 jobs, 0 errors; the only warnings are pre-existing linter notes in older files (zero warnings in the new files). A scan of every new file finds no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `@[implemented_by]`. `#print axioms` on all principal new declarations shows only `propext`, `Classical.choice`, `Quot.sound` (several depend on no axioms).

**Status recorded:** finite/structural layers PASS; aggregate-Euler uniformity, SmallQ and SmallR adapters remain external and uninhabited; provider exhaustiveness FAILS as a global claim (proved); `SP2-BALANCED7-FULL-Q45` OPEN (conditional compiler only); Balanced7 asymptotic and effective statuses kept separate, both open; post-Balanced7 census not activated; first exact residual `AFFINE287-SP2-SMALLQ-TYPEI-ADAPTER45`; **Erdős #287 remains OPEN**. All work is committed and pushed.

# Summary of changes for run ffa98343-83d2-4670-8663-8a6833eebf96
## What was done

Continued the Erdős #287 repository **in place, append-only**. Nothing earlier was deleted or rewritten, and `ARISTOTLE_SUMMARY.md` was not touched. Three layers are now banked: **V21** (two-high-projector / five-box sieve / source-normalization firewall), **V22** (source forensics + safe bad-character log re-ledger) and **SP-2** (direct Balanced7 source repair). Each has its own report with the mandated final block.

### V21 (completed)
Lean modules under `RequestProject/Erdos287/` — `TwoHighProjector3221`, `DoubleOrthogonalityFiveBox3221`, `BadCharacterCount3221`, `PrimeBoxNormalization3221`, `ShortShiftSieve3221`, `ShiuDivisorAverage3221`, `HighProjectorCutoff3221`, `PhysicalLogBudget3221`, `OuterTwoPrimeBlock3221`, `BalancedSevenV21Compiler`, plus `RequestProject/Status/Erdos287V21Status` and `AxiomAuditErdos287V21`. The missing deliverable, `ERDOS287_V21_TWO_PROJECTOR_SAFE_REPAIR_BANK_REPORT.md` (sections A–X + final block), has now been written.

Key proved content: the exact two-variable indicator identity giving `HH = AA − BA − AB + BB` with explicit no-omission / no-overlap / no-double-counting lemmas; the pre-projector variance reconstructed from the repository's own character source, with the ξ-form equivalence **proved** rather than assumed; five-box double orthogonality (`−2smW ≡ 1`, `−2smW′ ≡ 1`, `W ≡ W′ (mod q)`, `W − W′ = qt`, `q ∣ 2mW′+s`, `(q,W′)=1`, both signs); the safe finite bad-character count `#Bad ≤ D(D+1)/2 + 1 ≤ (D+1)²` (the `D·τ(q)` heuristic is **not** banked); the kernel-checked exponent ledger `39/35`, `31/35`, sum `2`; the symbolic four-channel log compilers with `BA/AB/BB` kept separate; the outer/inner seven-box partition and prime-density anti-double-spending firewall; the phase-alignment lemma repairing the circular provenance; and the conditional LOGVAR / Balanced7 compilers.

### V22 (new)
`BadCharacterLogLedger3221`, `Ford723BalancedSevenAdapter3221`, `PrimeBoxL1Normalization3221`, `TwoProjectorPhysicalClosure3221`, `Status/Erdos287V22Status`, `Status/AxiomAuditErdos287V22`, report `ERDOS287_V22_SOURCE_FORENSICS_SAFE_BANK_REPORT.md`. The safe `(D+1)²` count is pushed through the log arithmetic with abstract cutoff exponent: `Cvar(B0) = min(5, 15/2 − 2B0, 10 − 4B0)`, kernel samples `Cvar(1)=5`, `Cvar(2)=2`, `Cvar(3)=−2`. Closure criterion proved in exact form: `netLogExponent < −1 ⟺ Cvar > 2·Cext`, with the capacity table for `B0 = 1, 2, 3`.

### SP-2 (new)
`SP2DirectSourceAdapter3221`, `SP2PrimeBoxWeights3221`, `SP2ClosureCompiler3221`, `Status/Erdos287SP2Status`, `Status/AxiomAuditErdos287SP2`, report `ERDOS287_SP2_DIRECT_BALANCED7_SAFE_BANK_REPORT.md`. Source forensics found **no** `G_*`/`H_*` object; what exists is the fixed smooth-parity certificate (`truncMobius`, the `k=0, J=∅` packet), so the Ford-(7.23) adapter is recorded as `RETRACTED / NOT THE LITERAL SOURCE` (file preserved). Proved: the divisor-depth threshold pinning `r = 3`; `∑_{j≤3}(−1)^j C(7,j) = −20` and `64` of `128` subsets; and — the substantive repair — the pointwise law `|ω_i(p)| ≤ 1` for the literal weight `V_{i,λ}` as a **theorem**, not an interface field, with `L¹` mass equal to the cell cardinality. The closure compiler gives `−(2+5)/2 + 0 = −7/2 < −1` contingent on `Cext = 0`, with both `sp2_closure_margin` and `sp2_closure_fails_without_audit` making the contingency explicit.

## Required final block

```
FILES ADDED (V21): TwoHighProjector3221, DoubleOrthogonalityFiveBox3221,
BadCharacterCount3221, PrimeBoxNormalization3221, ShortShiftSieve3221,
ShiuDivisorAverage3221, HighProjectorCutoff3221, PhysicalLogBudget3221,
OuterTwoPrimeBlock3221, BalancedSevenV21Compiler, Status/Erdos287V21Status,
Status/AxiomAuditErdos287V21, ERDOS287_V21_TWO_PROJECTOR_SAFE_REPAIR_BANK_REPORT.md
FILES ADDED (V22): BadCharacterLogLedger3221, Ford723BalancedSevenAdapter3221,
PrimeBoxL1Normalization3221, TwoProjectorPhysicalClosure3221,
Status/Erdos287V22Status, Status/AxiomAuditErdos287V22,
ERDOS287_V22_SOURCE_FORENSICS_SAFE_BANK_REPORT.md
FILES ADDED (SP-2): SP2DirectSourceAdapter3221, SP2PrimeBoxWeights3221,
SP2ClosureCompiler3221, Status/Erdos287SP2Status, Status/AxiomAuditErdos287SP2,
ERDOS287_SP2_DIRECT_BALANCED7_SAFE_BANK_REPORT.md

FILES MODIFIED: RequestProject/Main.lean (import lines appended only)

V20 PRESERVED: YES
OLD HHH CLOSURE PROOF: RETRACTED (object and socket preserved)
TWO-HIGHPROJECTOR ALGEBRA: EXACT / ALGEBRAIC PASS
DOUBLE ORTHOGONALITY: EXACT PASS
BAD-CHARACTER SAFE COUNT: FINITE PASS, #Bad ≤ (D+1)^2
PRIMEBOX NORMALIZATION: pointwise law PROVED for V_{i,λ}; identification SOURCE_OPEN
CUTOFF COMPATIBILITY: SOURCE_OPEN / UNINHABITED
PHYSICAL LOG PREFACTOR: SOURCE_OPEN / UNINHABITED
SHIU INTERFACE: EXTERNAL / UNINHABITED (φ(2W)=φ(W) proved)
SHORT-t SIEVE INTERFACE: EXTERNAL / UNINHABITED (z = T^(1/20), dimension 1)
BA / AB / BB: SEPARATE CHANNELS, BOUNDS ARE HYPOTHESES, NOT THEOREMS
OUTER TWO-PRIME L2: ALGEBRA PROVED, DENSITY ANTECEDENT UNINHABITED
TWO-PROJECTOR CLOSURE: CONDITIONAL (compiler proved, no inhabitant)
3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45: OPEN / CONDITIONAL — NOT CLOSED
SIXTH MOMENT: OPEN STRONGER SUFFICIENT FALLBACK (not deleted, not marked false)
COMPARISON: SOURCE_OPEN
BALANCED7: OPEN
ERDOS287: OPEN
FIRST EXACT RESIDUAL: V21/V22 — BALANCED7-PRIMEBOX-L1-NORMALIZATION45;
  after SP-2 — COMPARISON-SMALLCOND-EXCEPTIONAL-SPLICE45
LAKE BUILD: SUCCESS — 8171 jobs, 0 errors; new modules emit 0 warnings
  (the warnings a from-source rebuild reports are pre-existing linter notes in older modules)
TRUST SCAN: ZERO occurrences of sorry / admit / axiom / opaque / unsafe /
  native_decide / @[implemented_by] in code across all new files (only prose mentions
  in docstrings); #print axioms on every principal new declaration returns only
  [propext, Classical.choice, Quot.sound]
PUBLIC-MAIN SYNC: Main.lean extended with imports only; full build clean
```

**Final firewall.** No source-open or external analytic interface was inhabited merely to make a compiler execute. Nothing in V21, V22 or SP-2 proves Erdős #287, and nothing proves Balanced7 unless the explicit analytic/source antecedents — the SP-2 source identification, the prime count, the sieve and Shiu inputs, the `Cext = 0` audit and the comparison splice — are separately supplied. Erdős #287 and Balanced7 both remain OPEN.


# Summary of changes for run 8a33d15a-18fa-43fa-b470-68e98c06199d
## Erdős #287 — V20 safe bank: completed and verified

The existing repository was continued **in place, append-only**. Nothing was deleted or rewritten; `ARISTOTLE_SUMMARY.md` was left untouched.

### Files added
- `RequestProject/Erdos287/HighConductorCharacterGram3221.lean`
- `RequestProject/Erdos287/FiveBoxCharacterFactorization3221.lean`
- `RequestProject/Erdos287/ConductorRouter3221.lean`
- `RequestProject/Erdos287/HighQuotientShiftedGram3221.lean`
- `RequestProject/Erdos287/HighConductorSixthMoment3221.lean`
- `RequestProject/Erdos287/BalancedSevenV20Compiler.lean`
- `RequestProject/Status/Erdos287V20Status.lean`
- `RequestProject/Status/AxiomAuditErdos287V20.lean`
- `ERDOS287_V20_HIGHQUOTIENT_HHH_SAFE_BANK_REPORT.md` (report sections A–V and the mandated final block)

### File modified
- `RequestProject/Main.lean` — import lines appended only.

### Principal results proved (all sorry-free)
- **Inverse-sampled character algebra:** `inverseSample_character_identity` (conj(χ(aₘ)) = χ(−2s)·χ(m), with `s²=1` and `2m` a unit stated explicitly), `affineSample_character_factor`, `cHigh_inverseSampled_expansion`.
- **Five-box factorisation:** `fiveBox_characterTransform_eq_prod_five`, `fiveBox_characterTransform_factor`, `pairBlockSum_eq_mul`, `sum_mul_sum5`.
- **Exact m-Gram (central V20 identity):** `inverseSampledVariance_eq_characterGram`, from `charSource_variance_eq_gram`; supporting `shortMGram`, `autocorr`, `autocorr_reindex`, `fixedModulus_samePrimitive_induced_unique`.
- **Diagonal / low-quotient children:** `characterGram_diag_split`, `autocorr_principal_highCoeff`, `lowConductor_card_le`, `lowQuotient_child_le`, plus the conditional compilers `highCondDiagonal_of_largeSieve`, `lowQuotient_child_of_diagonal_budget`.
- **Capacity firewalls:** `gram_parseval`, `autocorr_l2_sq_le`, `separateL2_compiler`, `separateGramL2_capacity_deficit` (12/35), `pointwiseBurgess_capacity_deficit` (51/112), `diagonal_power_room_rational`/`_rpow` (4/35).
- **Conductor-pair router:** `ConductorCell`, `RouterCondition`, `conductorCell_routed`, `router_case_A/B/C`, `router_threshold_identity` (5/14 + 31/80 = 417/560).
- **HHH frontier:** `SurvivingHHHConductorCell`, the exact object `hhhGram` (no analytic assumption in its definition, non-vacuity witnessed by `probeHHHData_gram`), the open socket `HighQuotientFiveBoxShiftedGram3221Input`, and the reassembly compiler `logVar_of_four_channels`.
- **Sixth-moment bridge:** `injOn_affineSample`, `sixthMoment_holder_at`, `sixthMoment_holder_over_q`, `sixthMoment_power_margin` (1/105).
- **Same-B0 comparison firewall and Balanced7 compiler:** `highConductorCutoff`, `MuLogComparisonAtCutoff`, `comparison_cutoff_must_match`, `balancedSeven_of_v20_package`, `v20_package_cutoff_consistent`.
- **Non-vacuity / anti-circularity:** `largeSieve_not_automatic`, `pointwiseBurgess_not_automatic`, `hhh_input_not_automatic_v20`, `sixthMoment_input_not_automatic_v20`, `comparison_not_automatic_v20`, `logVar_cannot_construct_hhh`, `balancedSeven_compiler_cannot_construct_comparison`.
- **Machine ledger:** `controlling_analytic_residual_unique`, `sixthMoment_not_controlling`, `logVar_reduced_not_proved`, `capacity_firewalls_are_not_proofs`, `children_are_conditional`, `comparison_source_open`, `terminal_nodes_open` (kernel `decide`).

### Build and trust
- `lake build`: **success — 8148 jobs, 0 errors, 0 warnings.**
- Placeholder scan of all new Lean files for `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `@[implemented_by]`: **zero occurrences.**
- `#print axioms` on every principal new declaration reports either `[propext, Classical.choice, Quot.sound]` or no axioms at all. No external analytic or source interface is inhabited anywhere.

### Status
Erdős #287 is **OPEN** and Balanced7 is **OPEN**; nothing here claims either. The first exact analytic residual is the high-quotient five-box shifted character Gram (`3221-HIGHQUOTIENT-FIVEBOX-SHIFTED-GRAM45`), with the sixth-moment route recorded only as a stronger sufficient open alternative, and comparison recorded as SOURCE_OPEN.


# Summary of changes for run 92ea5d66-6a71-4baf-b85e-90be38cdaccc
## Erdős #287 — V19 pre-Poisson / high-conductor safe bank (append-only)

**Erdős #287 remains OPEN. Balanced7 remains OPEN.** Nothing added proves either, no analytic or source interface is inhabited, and no `axiom` was introduced.

### A. Regression
Pre-edit `lake build`: success, 8135 jobs, 0 errors, tree clean. Every named prerequisite was located and reused unchanged (`FactorialEulerPolarization`, `FactorialEulerLocal`, `FactorialPolarizationLinearity`, `PascadiParameterLedger`, `NormalForm3221`, `MovingPhaseProvider3221`, `FactorialEndpoint3221Adapter`, `Erdos287V18Status`, and the whole V17 3221 finite/exponent bank). No existing theorem was restated, weakened, renamed or deleted; the seven-prime polarization was not redone (the V17 grouping and exponents are reused verbatim). Post-edit build: **success, 8140 jobs, 0 errors**.

**Files changed** — added `RequestProject/Erdos287/PrePoissonDensity3221.lean`, `RequestProject/Erdos287/HighConductorVariance3221.lean`, `RequestProject/Erdos287/CharacterGram3221.lean`, `RequestProject/Erdos287/BalancedSevenV19Compiler.lean`, `RequestProject/Status/Erdos287V19Status.lean`, `ERDOS287_V19_PREPOISSON_HIGHCOND_SAFE_BANK_REPORT.md`; edited `RequestProject/Main.lean` (five import lines only).

### B. Frontier reset
A new V19 metadata ledger (`Erdos287.V19Status.ledger`) records the V18 DI/small-`Z` route as *superseded as controlling frontier* — not false — plus `SOURCE_MISMATCH`, `CONDITIONAL PROVIDER METADATA` and `RETIRED AS CURRENT ROUTE` for the other three nodes. `controlling_analytic_node_unique` proves the inverse-sampled high-conductor log-variance node is the **unique** `OPEN_ANALYTIC` node. No theorem converts a label into a mathematical claim, so no analytic falsity is derived from metadata.

### C–H. New Lean-proved content (all sorry-free)
* **Affine divisor identity** — `affineResidue_iff_dvd_two_mul_add`: for odd `q`, `m·w ≡ a (mod q) ↔ q ∣ 2mw + s`; plus `balancedSeven_affine_divisor_condition`, `exists_affineResidue`.
* **First Cauchy / μ-sign** — `firstCauchy_sign_consumption`, `postCauchy_weight_sign_invariant`, and the firewall `firstCauchy_loses_sign_information` (the signed weight is provably not retained).
* **High-conductor residue source** — `residueSum`, `residueSum_sum_over_classes`. Dirichlet-character machinery *is* available, so the projection is literal, not a placeholder.
* **RR/RK/KK** — `normSq_sub_reassembly`, `highConductorEnergy_reassembles_crossTerms` (algebraic only; no claim that the physical comparison term is matched).
* **Divisor density** — `sampled_q_card_le_divisorCount(_affine)`; `τ(n)=X^{o(1)}` is *not* proved or assumed and is isolated as the uninhabited `DivisorGrowthInput`.
* **Second-copy density** — `secondCopy_shell_iff`, `congruence_interval_card_le` (`q·# ≤ (b−a)+q`), floor variant, `secondCopy_card_le_one_add_quotient`; exact ℤ arithmetic, no real intervals.
* **Combined compiler** — `sampledQuadBox_card_le`, with no `X`-exponent inside.
* **39/35 ledger** — `prePoisson_density_exponent = 39/35`, `cauchy_prefactor_exponent = 31/35`, `highCond_naturalScale_exponent = 39/35`, `naturalScale_matches_density` (`CAPACITY_ONLY`).
* **Retired-lane arithmetic** — `BC3221_capacity_deficit_arithmetic` (47/350 > 0), `DRZ3221_capacity_deficit_arithmetic` (11/84 > 0); metadata only, no external theorem formalised or assumed.
* **Variance socket** — `InverseSampledHighCond3221Data` (pure data, no free `Prop`), `Vhi`, and the load-bearing `samplePoint_iff_affineSampled` identifying `−s(2m)⁻¹` with `q ∣ 2mw+s`.
* **Character Gram** — `totient_mul_residueSum_eq_sum_char`, the proved projection `residueSum_eq_cLow_add_cHigh`, `gram_expansion`, `highResidue_energy_gram`, `inverseSampled_highResidue_gram`, `cHat_fiveBox_factorisation`, `cHat_twoBox_factorisation`. Identities only; no character-sum bounds.

### K/O/P. Socket, compiler, non-vacuity
`InverseSampledHighCondLogVar3221Input` (target `V_hi ≤ naturalScale / Lsave`, explicit positive saving) is **never inhabited**; it occurs only as a declaration and as a hypothesis. The compiler `cauchyPrefactor_of_firstCauchy → highCond_source_bound_of_logVar → factorialEndpoint_of_highCondLogVar → balancedSeven_of_highCondLogVar` keeps the budget explicit (`prefactor·(scale/Lsave) ≤ E²`) and the comparison channel independent (`E + err`). Non-automaticity proved: `highCondLogVar_not_automatic`, `cauchyPrefactor_not_automatic`, `balancedSeven_not_automatic`, `comparison_stays_independent` (reusing the V18 refutation).

### Q. Build / axiom audit
`lake build` succeeds (8140 jobs, 0 errors). The five new files contain **no** `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `@[implemented_by]` (the only textual hits are the words inside doc comments). `#print axioms` is run on all 45 principal new theorems; every one reports only `propext`/`Classical.choice`/`Quot.sound` or a subset, and two ledger theorems report no axioms at all. No `sorryAx`, no `Lean.ofReduceBool`.

### R–U
Final status table, first source open (`AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45`), first analytic open, and the next unique action are written in `ERDOS287_V19_PREPOISSON_HIGHCOND_SAFE_BANK_REPORT.md`.

```
GATE / BALANCED7: OPEN
FCL: OPEN
WINDOWPAIRSUPPLY: OPEN
ERDOS287: OPEN
```
```
FIRST ANALYTIC OPEN:
    3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45.
```

# Summary of changes for run afd7b265-8510-432f-8f62-3e3efb4cb741
## Erdős #287 — V18: fixed-degree-seven source / normal-form / small-`Z` compiler

**ERDŐS #287 REMAINS OPEN.** Nothing added here proves it, nor Balanced7, nor the factorial signed endpoint, nor the comparison match, nor any Kuznetsov/Deshouillers–Iwaniec/Pascadi estimate. No `axiom` was added and no analytic or source interface was inhabited.

### Regression guard
Baseline build 8131 jobs / 0 errors; final build **8135 jobs / 0 errors**. Every named prerequisite was located and reused unchanged (`FactorialEulerPolarization.lean`, `FactorialEulerLocal.lean`, `FactorialPolarizationLinearity.lean`, `PascadiParameterLedger.lean`, `Erdos287V16Status.lean`, plus the whole V17 3221 bank and `FactorialOmega7SignedEndpoint`, `MuLogComparisonLowCondMatch`, `BalancedSevenPacketInput`). Nothing was redefined, renamed, weakened or deleted; work is append-only apart from four import lines.

### Files changed
Added `RequestProject/Erdos287/NormalForm3221.lean`, `RequestProject/Erdos287/MovingPhaseProvider3221.lean`, `RequestProject/Erdos287/FactorialEndpoint3221Adapter.lean`, `RequestProject/Status/Erdos287V18Status.lean`, `ERDOS287_3221_SAFE_BANK_REPORT.md`. Edited `RequestProject/Main.lean` (imports only).

### Status repair (the moving-phase overclaim)
`PASCADI101-LEVELWISE-PHASE-LS45 PASS`, `PASCADI102-MOVINGPHASE45 PASS`, `PASCADI39-MOVINGPHASE-EXTENSION45 PASS` and `3221-SOURCE-MOVINGPHASE-DI45 CLOSED` are **retracted as controlling status** (provenance kept, nothing deleted): a repository-wide search finds no declaration mentioning a levelwise/moving phase and no phase provider is inhabited. They are replaced by a metadata-only four-regime dictionary (A, B published; C conditional provider; D open analytic), with the proved separations `largeRange_not_published`, `smallRange_is_conditional`. None of A–D is an axiom.

### New Lean-proved content (sorry-free)
* **Normal-form source pin** — `BalancedSeven3221NormalForm` records the schematic completed child as an exact equality on explicit finite data (coprime `q=rs`, phase, coefficients, Kloosterman leg literally equal to the banked `kloostermanLike` of modulus `s·c`, unit/gcd/zero-mode/low-conductor routing), with **no free `Prop` field and no inhabitant**. Search finding: a Kloosterman-shaped sum with its exact unit-change identity exists in the repository; **no** dispersion, Poisson/completion, additive character, gcd-extraction or low-conductor projection of the physical source exists. Status `SOURCE_BLOCKED`.
* **Phase algebra** — `phase_int_add`, `phase_fract`, `phase_congr`, `norm_phase`, and `phase_leg_congr` (mod-1 representative invariance on the pinned data); `kloostLeg_unit_change`, `modulus_above_cut`, `factorisation_is_data`. The ω-dependence classification is recorded, not forced, with counterguard `omega_product_strictly_stronger` (`1·6 = 2·3`). No literal ω formula and no value for `Z_3221` are claimed — `Z`, `R0,S0,M0,N0,C0`, `Qlevel` exist only as fields.
* **Small-`Z` range compiler** — `InSmallZRange`, `inSmallZRange_iff` (`N₀>0 ⇒ Z ≤ 1 ∨ Z N₀ ≤ Q`), dichotomy, disjointness, nonvacuity witness; unconditional levelwise algebra `levelValue`, `completedValue_eq_sum_levelValue`, `completedValue_norm_le`; and the compiler `diKuznetsov_of_perLevelSmallZ` from the **uninhabited** `PerLevelPhaseSmallZ3221Input` plus an explicit level-count budget to the existing analytic socket.
* **Large-range firewall** — `LevelwisePhaseLargeRange3221Input` (uninhabited, `OPEN_ANALYTIC`) kept strictly apart by the proved `smallZ_largeRange_firewall`: the two inputs can never both apply to the same source.
* **Endpoint adapter** — `FactorialEndpoint3221SourceAdapter` (`SOURCE_OPEN`, uninhabited) exposes the missing bridge; `factorialEndpoint_of_smallZ` and `balancedSeven_of_smallZ` are proved compilers that reuse the earlier balanced-seven implication unchanged and keep error channels separate (`E + err`).
* **Non-vacuity firewall** — `endpoint_not_automatic`, `comparison_not_automatic`, `perLevelSmallZ_not_automatic`: each open interface genuinely constrains its data, so no compiler can be made unconditional by parameter choice. The Hilbert–Schmidt/nuclear-rank firewall is preserved.

### Audit
`lake build` succeeds (8135 jobs, 0 errors). A repository-wide scan for `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `@[implemented_by]` finds **zero occurrences in Lean code** (all matches are documentation prose). `#print axioms` is emitted at build time for the 25 principal new theorems; each reports a subset of `[propext, Classical.choice, Quot.sound]` (one reports none). No user axiom.

### Final block
```
REGRESSION: PASS
BUILD: SUCCESS (8135 jobs, 0 errors)
SORRY: NONE
USER AXIOMS: NONE

FACTORIAL EULER: PROVED_ALGEBRAIC
EXPECTED-TERM LINEARITY: PROVED_ALGEBRAIC
3221 GROUPING: PROVED_FINITE
3221 EXPONENT LEDGER: PROVED_ALGEBRAIC / CAPACITY_ONLY
SOURCE-ASSISTED DIAGONAL: PROVED_FINITE / CAPACITY_ONLY
OFFDIAGONAL t: PROVED_FINITE / CAPACITY_ONLY
EH NO-WRAP: PROVED_FINITE
EH RATIO ENERGY: CONDITIONAL_FINITE
LITERAL 3221 NORMAL FORM: SOURCE_BLOCKED
omega FORMULA: SOURCE_OPEN
Z_3221: SOURCE_OPEN
SMALL-Z RANGE ADAPTER: CONDITIONAL_COMPILER
LEVELWISE LARGE-RANGE PHASE: OPEN_ANALYTIC
3221 ANALYTIC CHILD: OPEN_ANALYTIC
FACTORIAL ENDPOINT: OPEN_ANALYTIC
COMPARISON: SOURCE_OPEN
BALANCED7: OPEN
FCL: OPEN
WINDOWPAIRSUPPLY: OPEN
ERDOS287: OPEN
```
First source open: the dispersion/completion (Poisson) identity for the physical balanced-seven source. First analytic open: the per-level small-`Z` estimate for the pinned source (and, separately, the large-range input). Next unique action: derive a completed finite Fourier/Poisson identity for the `m`-box in terms of `levelValue`, `phase` and `kloostermanLike`, i.e. produce the first genuine inhabitant of the pinned normal form from repository definitions. Full details in `ERDOS287_3221_SAFE_BANK_REPORT.md`; all work is committed and pushed.

# Summary of changes for run 5d1858c9-721b-40a2-8db0-d6de33736eb4
## Erdős #287 — V17: 3221 source-assisted dispersion safe bank

**ERDŐS #287 REMAINS OPEN.** Nothing in this run proves it, nor Balanced7, nor the factorial signed endpoint, nor any Deshouillers–Iwaniec/Kuznetsov estimate. No axiom was added.

### Baseline / regression
Baseline `lake build`: 8123 jobs, zero errors. Final: **8131 jobs, zero errors**. No V15/V16 statement was edited; work is append-only apart from eight import lines in `RequestProject/Main.lean`.

**Search finding:** the named prerequisites `UnconditionalDivisorBound.lean`, `FixedDepthConvolution.lean` and `card_divisors_in_range_le_mul_rpow` **do not exist** in this repository, and there is no product-energy bank, no residue-class interval count, and no completed Fourier/Poisson identity. Nothing was assumed to exist: the finite divisor/energy facts were proved from scratch, the missing source objects were reported rather than fabricated.

### Files added
`RequestProject/Erdos287/Exponent3221Ledger.lean`, `BalancedSeven3221Grouping.lean`, `SourceAssistedDiagonal3221.lean`, `OffDiagonal3221.lean`, `EHNoWrap3221.lean`, `DIKuznetsov3221Interface.lean`, `BalancedSeven3221Compiler.lean`, `RequestProject/Status/Erdos287V17Status.lean`, `ERDOS287_3221_V17_SAFE_BANK_REPORT.md`. Edited: `RequestProject/Main.lean` (imports only).

### Main proved theorems
* **Regrouping** — `sevenfold_regrouping` (with `prod_apply_tuples`, the reusable exact expansion of an iterated Dirichlet convolution over ordered tuples): the ordered seven-prime sum of the V16 polarization equals `∑_{e·a·b·c=m} η α β γ` with exact convolution multiplicities. Numerically cross-checked at `m = 192` (both sides `1511208`). Multiplicity firewall discharged: `grouping_not_injective` (two distinct prime 7-tuples, same `(e,m,n,ℓ)`) and `alpha_not_one_bounded` (`α(6)=2`), with the correct majorant `alpha_norm_le_card_divisors` (`‖α(a)‖ ≤ τ(a)`).
* **Exponent/range ledger** — exact ℚ arithmetic: `E+M+N+L=1`, `W−Q=4/35`, `H=11/35`, `E+H=16/35<Q` with margin `1/7`, `Texp=4/35`, diagonal margin `2/35`, the defect `(N+L)−Q=−1/35`, and the transcribed margins `1/10, 2/21, 19/35, 4/35, 2/35`.
* **Diagonal** — `fiberwise_energy_le`, `productFibre_card_le` (`τ²`), `modulus_divisor_count_le` with the load-bearing zero guard `modulus_count_zero_case`, `diagonal_parent_bound`, `sourceAssisted_diagonal_finite`.
* **Off-diagonal** — `offdiag_existsUnique_t`, `offdiag_t_ne_zero`, `offdiag_abs_t_le` (`|t|·Q_min ≤ 2W_max`), all over ℤ.
* **No-wrap / hostile audit** — `ratio_eq_iff_cross` (unit sector), `nowrap_eq_of_dvd_of_abs_lt`, `ratioCollision_samePrime`, `ratioCollision_distinctPrimes_param` (`h₁=ce₁, h₂=ce₂`), `ratioCollision_card_bound` (`≤ #E·#H + (#E)²·#C`), `ehRatioEnergy_le_explicit`. Audit verdict: the claimed order `E·H` is reproduced **with no divisor factor and no `X^{o(1)}` loss**, so the claim is not retracted — but it is banked only as `CONDITIONAL_FINITE`, since every statement carries the literal no-wrap size hypothesis.
* **Dictionary / socket / compiler** — `BalancedSeven3221CompletedSource` (concrete data + conditions, no free `Prop` field, no physical inhabitant), `DIKuznetsov3221Input` (source-specific, never inhabited, not an axiom), counterguards `slot_dependence_counterguard`, `zeroMode_separation_guard`, `modulus_factorisation_not_unique`, and the compilers `factorialEndpoint_of_3221`, `balancedSeven_of_3221` (reusing the V16 theorem unchanged). The bridge the 3221 child cannot supply is made explicit as the SOURCE-OPEN `Endpoint3221Decomposition`, never inhabited.

### Comparison source audit
`SOURCE_BLOCKED`. Missing definitions named exactly: `B(n)`/`4B(n)`, `M_phys`, the principal local density, the small-conductor subtraction, the exceptional-character convention, physical unit/nonunit routing. Nothing invented; polarization not redone.

### Audit
No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `@[implemented_by]` in Lean code (all matches are documentation prose). `#print axioms` is emitted for the 68 principal new theorems; every report across the repository is a subset of `[propext, Classical.choice, Quot.sound]`. Full A–V report in `ERDOS287_3221_V17_SAFE_BANK_REPORT.md`. Everything committed and pushed.

```
REGRESSION: NONE
BUILD: SUCCESS (8131 jobs, 0 errors)
SORRY: NONE
USER AXIOMS: NONE

FACTORIAL EULER POLARIZATION: PROVED_ALGEBRAIC
3221 LABELLED GROUPING: PROVED_FINITE
3221 COEFFICIENT MULTIPLICITY: PROVED_FINITE
STANDARD Q<NL DEFECT: PROVED_ALGEBRAIC
SOURCE-ASSISTED DIAGONAL: PROVED_FINITE
OFFDIAGONAL t PARAMETER: PROVED_FINITE
t RANGE: PROVED_FINITE
EH<Q CAPACITY: CAPACITY_ONLY
EH NO-WRAP: PROVED_FINITE
EH RATIO ENERGY: CONDITIONAL_FINITE
COMPLETED SOURCE DICTIONARY: SOURCE_OPEN
DI/KUZNETSOV LITERAL SPLICE: OPEN_ANALYTIC
FACTORIAL ENDPOINT: OPEN_ANALYTIC
COMPARISON: SOURCE_BLOCKED
BALANCED7: OPEN
FCL: OPEN
WINDOWPAIRSUPPLY: OPEN
ERDOS287: OPEN
```

**First formal blocker:** the endpoint bridge, now explicit as `Endpoint3221Decomposition`. **First source blocker:** the completed post-Poisson identity (then the physical comparison objects; the `θ=7/32` inequality was supplied without a formula and was not transcribed). **First analytic blocker:** `3221-DI-KUZNETSOV-LITERAL-SPLICE45`. **Next exact action:** produce a completed finite Fourier/Poisson identity for the `m`-box in terms of the objects already defined here.

# Summary of changes for run 09089103-b26b-402b-8253-fef2b27ed0e8
## V16 formal update — resumed in place, `ERDŐS #287 REMAINS OPEN`

**Workspace guard: PASS.** Every V15 object named in the task was located before any edit (`coeff_balanced_eq_perm_sum`, `coeff_balanced_scaled`, `balancedMonomial`, `balancedSevenMonomial`, `labelledPolynomial`, `SquarefreeEncoding`, and both V15 interfaces `PolarizedOmega7SignedEoD`, `MuLogComparisonLowCondMatch`). No compiling V15 file was restarted, rewritten, weakened or renamed; work is append-only apart from five import lines in `RequestProject/Main.lean`. No axiom was added.

### Files changed
Added `RequestProject/Erdos287/FactorialEulerPolarization.lean`, `FactorialEulerLocal.lean`, `FactorialPolarizationLinearity.lean`, `PascadiParameterLedger.lean`, `RequestProject/Status/Erdos287V16Status.lean`, `ERDOS287_FACTORIAL_V16_REPORT.md`. Edited `RequestProject/Main.lean` (imports only).

### 1. Retirement
"Complete multiplicativity is required for the polarized seven-box encoding" is retired **as controlling** in the V16 status docstring; nothing proved under it is withdrawn or deleted.

### 2. New factorial Euler polarization — `PROVED_ALGEBRAIC`
Over an arbitrary characteristic-zero field (ℂ instantiated separately), never a bare semiring: `factorialEulerPolarization_seven` gives, for Ω(m)=7 and `F_z(p^e)=a_z(p)^e/e!` extended multiplicatively with `a_z(p)=(1/7)Σ z_i ω_i(p)`,
`7^7·[z_1⋯z_7] F_z(m) = Σ_{p_1⋯p_7=m, ordered} ∏_i ω_i(p_i)`,
**including repeated primes**. Supporting theorems: `mem_ordFact_iff` (the index set really is the ordered prime tuples), `count_eq_factorization`, `exists_perm_comp`, `image_perm_eq_ordFact`, `fiber_card_eq` (the factorials cancel exactly the permutations of equal prime occurrences — proved, not assumed), `factorialEulerPolarization_of_listing`, `exists_prime_listing`, plus the general N-slot version `factorialEulerPolarization`, the ℂ form, and non-vacuity at the extreme repeated case `128 = 2^7`. The identity was cross-checked numerically on `m = 12`, `N = 3` (both sides `227`).

### 3. Local Euler algebra — formal only
`localSeries_eq_rescale_exp` (`Σ_e F_z(p^e)T^e = exp(aT)` as formal power series), `derivative_localSeries` (`d/dT S = a·S`), and — so the Λ-data is a theorem, not a convention — `localSeries_ne_zero`, `localLambdaSeries_unique`, `lambda_coeffs_of_logDeriv`: any family satisfying the log-derivative equation is forced to be `a` at `e=1` and `0` for `e≥2`; with the `log p` normalisation, `localLambda_one`, `localLambda_of_two_le`, `localLambdaSeries_eq_C`. **No class-C claim**: the repository contains no class-C definition, so only the finite/formal prime-power coefficient identity is banked. No analytic convergence anywhere.

### 4. Expected-term linearity — `PROVED_ALGEBRAIC`
`factorialPolarization_commutes_linearMap` (+ seven-slot, arithmetic-function and weighted-projection instances). Abstract and conditional; covers principal-character, low-conductor-character and exceptional-character linear operators as instances. `M_fac = M_phys` is **not** proved.

### 5. Pascadi parameter ledger — `PROVED_ALGEBRAIC / PARAMETER_LEDGER`
`pascadi_parameter_eta_le_one_div_4000`, `one_div_seven_gt_one_div_4000`, `pascadi_Q_three_fifths_y_one_seventh_incompatible`, plus the exact margin `−3993/280`. Exact ℚ arithmetic; Pascadi's analytic theorem is not formalised and is not claimed to fail.

### 6–8. Interfaces and compiler
`FactorialOmega7SignedEndpoint` (`AFFINE287-FACTORIAL-OMEGA7-SIGNED-ENDPOINT45`) is stated and **never inhabited**; `MuLogComparisonLowCondMatch` stays uninhabited and source-blocked; the only theorem about `BalancedSevenPacketInput` is the implication `balancedSeven_of_factorialEndpoint_and_comparison`, which keeps the two error channels separate (`E + err`) and inhabits nothing.

### Audit
`lake build` succeeds: 8123 jobs, **zero errors**, and the build log contains no `sorryAx`. A repository-wide scan of all Lean sources for `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `@[implemented_by]` finds **zero occurrences in Lean code** (all matches are documentation prose). `#print axioms` is emitted at build time for the 32 principal new theorems; across the whole repository all 446 printed reports list only `[propext, Classical.choice, Quot.sound]`.

### Status
`OMEGA7-FACTORIAL-EULER-POLARIZATION45: PROVED_ALGEBRAIC` · `POLARIZED-EXPECTED-TERM-LINEARITY45: PROVED_ALGEBRAIC` · `PASCADI-Q3/5-Y1/7-PARAMETER-NOGO: PROVED_ALGEBRAIC/PARAMETER_LEDGER` · `AFFINE287-FACTORIAL-OMEGA7-SIGNED-ENDPOINT45: OPEN_ANALYTIC` · `AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45: SOURCE_BLOCKED/OPEN` · `BALANCED7: CONDITIONAL/OPEN` · `ERDOS287: OPEN`.

No statement was found false and no target failed. Full ledger in `ERDOS287_FACTORIAL_V16_REPORT.md`.

# Summary of changes for run 3a93e89b-e3c6-43b5-bcda-2e46b020bde4
## V15 resumed in place — verdict `ERDOS287_V15_MULOG_POLARIZATION_SAFE_BANK`, `ERDOS287: OPEN`

**Workspace guard: PASS.** All named V14 objects were located before any edit (`vaughan_identity_exact`, `vaughan_affine_pointwise` in `RequestProject/Erdos287/AffineVaughanIdentity.lean`; `AffineVaughanPrimeCell`, `lambdaU_eq_neg_truncMobius` in `AffineVaughanPrimeOuter.lean`; `AffinePrimeModulusTwoOuterPacket` and the determinant-one line theorems in `AffineTwoOuterSource.lean`; the three compilers in `AffineTwoOuterCompiler.lean`). No V14 theorem was deleted, weakened, renamed or rewritten; work is append-only apart from seven import lines in `RequestProject/Main.lean`. No user axiom was added.

### Files added
`RequestProject/Erdos287/AffineMuLogIdentity.lean`, `AffineMuLogHardSource.lean`, `AffineMuLogLine.lean`, `AffineMuLogExponentLedger.lean`, `BalancedSevenFinite.lean`, `BalancedSevenPolarization.lean`, `RequestProject/Status/Erdos287V15Status.lean`, `ERDOS287_MULOG_V15_REPORT.md`. Edited: `RequestProject/Main.lean` (imports only).

### Proved (sorry-free, kernel-checked)
- **Λ = μ ∗ log** (`vonMangoldt_eq_mobius_mul_log`), derived in an arbitrary commutative ring from `μζ = 1`, `log = Λζ`, instantiated with Mathlib's genuine von Mangoldt/Möbius/log/zeta; a `rfl`-check confirms it is the same statement as Mathlib's own `moebius_mul_log_eq_vonMangoldt`. Coefficientwise `Λ(N) = ∑_{qr=N} μ(q) log r` and its divisor form.
- **Affine source** at `N = 2mn ± 1` (`muLog_affine_pointwise`), using the V14 natural-number sign firewall; the named source object is defined only after the equality is proved.
- **Three-way `q`/`r` partition**: exhaustive, pairwise disjoint, with exact recombination for an arbitrary weight in any additive commutative monoid, then specialised to μ·log and to the affine argument. The hard piece is defined, never claimed small.
- **Determinant-one line** `qr − 2mn = ±1`: `r ≠ 0` and `q ≠ 0` proved (not assumed), `gcd(r,2m)=1` and `gcd(q,2n)=1`, forward and reverse directions, the iff, and multiplicity-one uniqueness of the line parameter.
- **Exponent ledger only**: `δ₀ = 1/6 − σ > 0`, `σ + 2/3 + 1/6 = 1 − δ₀`, hence `< 1`, plus `1/6 − ν₀ = 131/300000`. No `O`-estimate is stated as a theorem.
- **Balanced-seven binomial certificate** `∑_{j≤3} (−1)^j C(7,j) = −20`, derived from the already-banked general alternating partial binomial identity; no physical source bridge is claimed.
- **Repeated-prime finite router**: seven labelled slots with one imposed coincidence take at most six values (and the general `Fin n` form), plus `6/7 < 1` as a rational inequality only.
- **Squarefree labelled polarization** (main new algebra): over an arbitrary commutative semiring, the coefficient of `z_1⋯z_n` in `∏_j (∑_i ω_i(p_j) z_i)` is `∑_{σ∈S_n} ∏_j ω_{σ(j)}(p_j)`, each permutation exactly once; specialised to `n = 7` and to ℂ, with `7! = 5040`. The normalisation is separate: scaling by `c` gives `c^n`, and the `1/7` case gives the factor `1/823543 = 7^{-7}`.
- **Squarefree multiplicative encoding**, finite interface only: an abstract multiplicative arithmetic function with prescribed prime values and vanishing at exponent ≥ 2, with `f(p₁⋯p₇) = ∏ a(pᵢ)` under distinctness; shown inhabited by Mathlib's Möbius function so nothing downstream is vacuous.

### Open / uninhabited
`PolarizedOmega7SignedEoD` (`AFFINE287-POLARIZED-OMEGA7-SIGNED-EOD45`, OPEN_ANALYTIC) and `MuLogComparisonLowCondMatch` (`AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45`, SOURCE_OPEN) are stated as specifications and never inhabited. No Bombieri–Vinogradov, DGS, Pascadi, Kuznetsov, large-value, Gate1A/1B, WindowPairSupply or FCL statement is assumed or proved. V14's Vaughan route is recorded as a valid but nonminimal alternative — never as false.

### Audit
`lake build` succeeds (8118 jobs, no errors). A repository-wide scan for `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `@[implemented_by]` finds zero occurrences in Lean code (all matches are documentation prose). `#print axioms` is emitted at build time for all 36 principal new theorems; each reports only a subset of `[propext, Classical.choice, Quot.sound]`. The twenty hostile tests are answered one by one in the docstring of the V15 status file; all pass with no downgrades. Everything is committed and pushed.

**Erdős #287 remains OPEN.** Formalising the polarization algebra does not close the balanced-seven case of anything.

# Summary of changes for run 0d849f24-cf9b-47cd-9af8-65f6801a897e
## Erdős #287 — V14: exact Vaughan source / prime-modulus two-outer structural spine

**Erdős #287 remains OPEN.** Nothing in this run proves it, nor `AFFINE287-PRIME-MODULUS-MU-TWOOUTER45`, smallness of the k = 0 smooth-parity packet, FCL, Gate 1A/1B closure, `WindowPairSupply` for all large M, or the Twin Prime Conjecture.

### Workspace guard
All eight named files (the four singleton V13 files and the four earlier fixed-certificate files) were verified present before any mathematics. `ERDOS287_ARISTOTLE_WORKSPACE_MISMATCH` does not apply; work resumed in place, append-only.

### Files added
`RequestProject/Erdos287/FordGeneratedDepth.lean`, `AffineVaughanIdentity.lean`, `AffineVaughanPrimeOuter.lean`, `AffineTwoOuterSource.lean`, `AffineTwoOuterCompiler.lean`, `RequestProject/Status/Erdos287VaughanV14Status.lean`, `ERDOS287_VAUGHAN_V14_REPORT.md`. (One file more than the suggested plan: the Part-2 finite arithmetic is kept separate from the Vaughan algebra.)

### Files edited
`RequestProject/Main.lean` — six import lines only. No historical statement was modified.

### What was proved (all sorry-free, kernel-checked)
- **Ford depth (PROVED_FINITE):** `general_ford_depth_le_112`, `fixed_certificate_depth_le_76` (+ factored form), `k0_depth_le_40`, with sharpness witnesses. The three input bounds (s ≤ 20, k ≤ 6, ell ≤ 12) are explicit hypotheses classified as published external input; Ford–Maynard Lemma 7.17 is not reproved.
- **Exact Vaughan identity (PROVED_ALGEBRAIC):** `vaughan_identity_abstract` in any commutative ring from `μ∗1 = ε` and `Λ∗1 = log`, instantiated as `vaughan_identity_exact` in the Dirichlet ring with Mathlib's genuine von Mangoldt/Möbius/log/zeta — no coefficientwise postulate, no axiom. Pointwise divisor-sum form `vaughan_pointwise` with `I1/I2/II`, and `vaughan_pointwise_of_lt` proving the `Λ_{≤V}` term vanishes *from* the size hypothesis.
- **Affine specialisation (PROVED_ALGEBRAIC):** `AffineSign`, `affineNat`, `affineNat_cast` (the ℕ-subtraction firewall for s = −1), `vaughan_affine_pointwise`.
- **Outer router (PROVED_FINITE):** prime vs proper-prime-power partition of the Λ-support, exhaustive and disjoint, plus the rational exponent ledger 1 − (1/3)/2 = 5/6. The analytic prime-power bound is the uninhabited `PrimePowerOuterBound`.
- **Prime-outer source cell:** `AffineVaughanPrimeCell` with only finite factorisation data; elementary consequences (divisibility, p odd, p ≥ 3).
- **Cofactor fold (PROVED_ALGEBRAIC):** `lambdaU_eq_neg_truncMobius` for q > 1, tying the new `d > U` cutoff to the banked `truncMobius` `d ≤ T` cutoff explicitly; `lambdaU_prime = −1`.
- **Support no-go (PROVED_FINITE):** `prime_support_obstruction_to_balanced_convolution` and `vaughan_cofactor_balanced_factorization_impossible`, scoped strictly to the stated balanced-support hypotheses.
- **Prime-modulus orientation (PROVED_ALGEBRAIC):** congruence, unique residue class in `ZMod p` under the explicit invertibility hypothesis, and the two coprimality consequences of the unit shift.
- **Two-outer quotient/packet:** `deltaMuOne` with exact unfolding, and `AffinePrimeModulusTwoOuterPacket` as a finite interface with no analytic field.
- **Determinant-one line (PROVED_ALGEBRAIC):** coprimality from the unit shift, both directions as an iff, and uniqueness of the parameter.
- **Exponent kernel:** strict bound 1/6 < 1 − exp(M) − exp(P), explicit-margin form, and the endpoint equality stated separately.
- **Conditional compiler (PROVED_COMPILER):** `singletonTypeII_of_vaughan_twoOuter`, `smoothParity_of_vaughan_twoOuter`, `parentLeakage_of_vaughan_twoOuter`, keeping the Type-I, prime-power, two-outer and comparison channels separate (error `E_I + C·X^{5/6} + E₂`, never merged).

### Open / blocked
Uninhabited interfaces: `PrimePowerOuterBound`, `AffinePrimeModulusMuTwoOuterInput`, `VaughanTypeIGeneratedKappaInput`, `Affine287ToTwoOuterF3Adapter`. Source-blocked: `Affine287TwoOuterComparisonMatch`, and (unchanged) `K0CellIdentitySource`, `SingletonPacketReduction`. No Gate/F3 provider is inhabited by nomenclature.

### Audit
`lake build` succeeds (8111 jobs, no errors). A repository-wide search of all Lean sources for `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `@[implemented_by]` finds **zero occurrences in Lean code** — every match is documentation prose. `#print axioms` is emitted at build time for all principal new theorems by the V14 status file; each reports only a subset of `[propext, Classical.choice, Quot.sound]`.

### Failed targets
None. No statement was found false; the one honest caveat is that the Part-2 depth model `2s + k·ell` is a definition chosen to reproduce the audited constants, and the `76` bound follows from the halved high-prime budget supplied as a hypothesis.

The sixteen hostile checks are answered individually in the docstring of the V14 status file, and the full ledger, source map and theorem list are in `ERDOS287_VAUGHAN_V14_REPORT.md`. Everything is committed and pushed.


# Summary of changes for run 3f26f1c6-6a1d-42e1-a3b1-69c782fc5917
## Workspace check

All six named files were verified present in the working tree before any mathematics was done, so `ERDOS287_ARISTOTLE_WORKSPACE_MISMATCH` does not apply: `RequestProject/Erdos287/FixedCertificateFordData.lean`, `FixedCertificateThreeError.lean`, `FixedCertificateSmoothParity.lean`, `FixedCertificateOrderCounterguard.lean`, `KummerDegeneracyRouters.lean`, and `RequestProject/Status/Erdos287GoldV12Status.lean`. Work resumed in place on the existing branch.

**Erdős #287 remains OPEN.** Nothing here proves it, nor Gate 1A/1B closure, H8/H9 smallness, the seven-prime Kummer bound, full fixed-certificate leakage, or the Twin Prime Conjecture.

## Source archaeology (A) — key finding

`nu0`, `truncMobius`, `FixedCertificateSmoothParityPacket` (with its `cell_identity` field), the parent leakage compiler, the three-error transference theorem and the balanced-cell counterguard are all present and were reused unchanged. But there is **no** `gStar`, **no** `eps`/`epsilonStar`, and **no Ford factorisation or canonical split** anywhere in the tree, and no coagulation/forbidden-region abstraction. The full object-by-object map is in `ERDOS287_SINGLETON_V13_REPORT.md`.

## B — verdict: `K0_CELL_IDENTITY_SOURCE_STILL_EXTERNAL`

Because the canonical split is not encoded, the `k = 0`, `J = ∅` specialization could only be assumed, not proved. No fake Ford factorisation was created; `cell_identity` is left uninhabited; the missing statement is named exactly as `K0CellIdentitySource` and carried as an explicit antecedent by every downstream theorem.

## What was proved (all sorry-free, kernel-checked)

- **D — rational ledger** (exact ℚ, no floating point): `sigma_pos`, `epsilon_lt_sigma`, `epsilon_lt_sigma_div_three`, `sigma_lt_one_sixth`, `two_sigma_div_three_lt_one`, `two_sigma_lt_one`, `six_sigma_lt_one`, `seven_mul_sigma_gt_one`, plus `nu0R_eq_cast_nu0` tying the ledger to the previously banked ν₀ = 16623/100000, and `admissibleEps_nonempty`.
- **C — `exists_subset_sum_in_typeII_window`**, the purely combinatorial smooth-vector lemma, by the two-case argument. The requested coagulation statement was *not* built: no such abstraction exists in the repository, and the missing object is recorded rather than invented.
- **E — `FordSmoothFragmentCertificate`**, classified `CONDITIONAL_INTERFACE / PUBLISHED_SOURCE`, never inhabited. Lemma 7.17 is not reproved. A clearly-labelled toy witness certifies the specification is *satisfiable*, so no downstream conclusion is vacuous.
- **F — `canonical_singleton_typeII`**, `canonical_singleton_card_eq_one`, `singleton_supersedes_depth_five`. Verdict `CANONICAL_SINGLETON_E45_KERNEL_PASS`.
- **G — `singleton_real_power_window`** and its shifted form: the real-power translation was completed, so the "pending" fallback was not needed.
- **H — `SingletonClass`** (tag only) and `singleton_complement_depth_le_39`, which also certifies the complement equals depth − 1.
- **I — `SingletonGeneratedTypeIIInput`**, uninhabited; Λ, B, W, ξ, κ are abstract parameters, not claimed to be the analytic objects.
- **J — `smoothParity_of_singletonTypeII`, `parentLeakage_of_singletonTypeII`, `primeMassPos_of_singletonTypeII`**: `PROVED_COMPILER / CONDITIONAL_ON_OPEN_ANALYTIC_INPUT`. The three error channels stay separate; `E2` is never merged into the sign region.

## Hostile checks — one downgrade

Check 3 failed as stated and was downgraded honestly. The interface does not force a singleton side to be terminal, so the requested `1 ≤ 2σ/3` route needs an extra hypothesis; it is kept as `fragment_singleton_terminal_contradiction`. The route actually used is the unconditional, strictly stronger `fragment_seven_le_card` (`s + r ≥ 7`, from `1 ≤ (s+r)σ` and `6σ < 1`). Check 6 passes only because the terminal-position convention is recorded explicitly as a field. All ten answers are in the status file's docstring.

## Audit

`lake build` succeeds (8105 jobs). Repository-wide scans find **zero** Lean-code occurrences of `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `@[implemented_by]` — every match is documentation prose. All 41 principal new theorems print `[propext, Classical.choice, Quot.sound]`, emitted at build time by the status file.

## Files

Added: `RequestProject/Erdos287/FixedCertificateSingletonParameters.lean`, `FixedCertificateSingletonFragment.lean`, `FixedCertificateSingletonCompiler.lean`, `RequestProject/Status/Erdos287SingletonV13Status.lean`, `ERDOS287_SINGLETON_V13_REPORT.md`. Edited: `RequestProject/Main.lean` (four import lines only). No historical theorem statement was touched. Everything is committed and pushed.

## Final ledger

`K0-SMOOTH-LEAKAGE-SOURCE45: SOURCE_BLOCKED` · `MU-SPLITTABLE45: PUBLISHED_EXTERNAL_INPUT` · `CANONICAL-SINGLETON-E45: PROVED_ALGEBRAIC` · `SINGLETON-COMPLEMENT-DEPTH39: PROVED_FINITE` · `287-SMOOTH-PARITY-FRAGMENT-TO-SINGLETON-TYPEII45: PROVED_COMPILER` · `287-SMOOTH-PARITY-SINGLETON-GENERATED-TYPEII45: OPEN_ANALYTIC` · `SMOOTH-PARITY: CONDITIONAL_INTERFACE / OPEN_ANALYTIC` · `FCL: OPEN_ANALYTIC` · `ERDOS287: OPEN_ANALYTIC`.

# Summary of changes for run 65719825-9f98-4322-874e-6644b235a32e
## Erdős 287 — V11 finalization + V12 gold reproof / Leanify run

Everything is committed and pushed; `lake build` completes successfully (8101 jobs) with no `sorry`, `admit`, `axiom`, `opaque`, `native_decide`, `unsafe` or `@[implemented_by]` anywhere in Lean code (all matches are documentation prose). Every new theorem prints `depends on axioms: [propext, Classical.choice, Quot.sound]`.

**Terminal status: ERDOS287 OPEN.** Nothing here proves #287.

### Files added this run (append-only; only `RequestProject/Main.lean` was edited, import lines only)
- `RequestProject/Erdos287/FixedCertificateFordData.lean` — Part G1: ν₀ = 16623/100000 as an exact rational, the four branch definitions (two-variable coefficient kept as a parameter, since only its support is given), window arithmetic (`twoVarWindow_nonempty`, `twoVarWindow_width`), the shrink and `shrink_le`, plus the never-inhabited `CertificatePinned` / `PositiveComparisonMargin` predicates.
- `RequestProject/Erdos287/FixedCertificateThreeError.lean` — Part G2: four-region partition with **three separate errors**, `sum_a_P_identity4`, `sum_a_P_lower4` (`≥ (1+C)B − ET − EL − E2 − EM`), `sum_a_P_pos4`, `sum_a_P_pos4_fraction` (constant saving suffices), `transference4_nonvacuous`. N2 is never merged into the sign region.
- `RequestProject/Erdos287/FixedCertificateSmoothParity.lean` — Parts G3/I: `truncMobius`, `truncMobius_prime`, `truncMobius_eq_zero_of_le`, the `FixedCertificateSmoothParityPacket` interface, `smoothParity_prime_normalization`, `smoothParity_missing_source`, and the parent leakage compiler `parent_leakage_of_children` / `parent_leakage_two_children` / `parent_prime_mass_pos`.
- `RequestProject/Erdos287/FixedCertificateOrderCounterguard.lean` — Part G4: `alternating_partial_binomial` (∑_{j≤r}(−1)^j C(k,j) = (−1)^r C(k−1,r)), the balanced-cell model and cut lemma, `balancedCellWeight_ne_zero`, the explicit values at k = 7…12 (−20, −35, 70, 126, −252, −462; the k = 9 value matches the banked 70), and `finite_H8H9_only_census_fails`.
- `RequestProject/Erdos287/KummerDegeneracyRouters.lean` — Part F: the four formalizable strata as predicates, `generic_disjoint_strata`, `generic_not_square`, `generic_not_pmExceptional`, `repeatedRoot_router_nonvacuous`.
- `RequestProject/Status/Erdos287GoldV12Status.lean` — Part J route firewall + `#print axioms` for all new theorems.
- `ERDOS287_GOLD_V12_REPORT.md` — the full A–M report (source map in the requested format, verdicts, file/axiom audit, final ledger). The earlier `ERDOS287_GOLD_V11_REPORT.md` was also committed.

### Firewall finding
Neither the V11 nor the V12 dossier is present in the repository (no `.tex`/`.pdf`, no `H8`/`H9`/Ford-(7.23)/principal-mode/conductor identifiers). All literal source-transcription obligations are therefore reported SOURCE BLOCKED and nothing was reconstructed.

### FINAL LEDGER
```
LCBETA PLACEMENT: REPAIRED
LOG-COFACTOR-ASYMPTOTIC287: KERNEL PASS
FIXED-CERTIFICATE287-PIN: SOURCE BLOCKED
FIXED-CERTIFICATE-TRANSFERENCE287: KERNEL PASS
FIXED-CERTIFICATE-SMOOTH-PARITY PACKET: SOURCE BLOCKED
FINITE-H8/H9-ONLY-CENSUS: FAIL (counterguard compiles)
HIGH-ORDER COUNTERGUARD: KERNEL PASS
QUADRATIC-KUMMER FINITE COMPILER: KERNEL PASS
ROOT-STABILIZER ALGEBRA: KERNEL PASS
WEIL / INTERVAL COMPLETION: EXTERNAL INTERFACE
SEVEN-PRIME EXPONENT LEDGER: KERNEL PASS
KUMMER DEGENERACY ROUTERS: PARTIAL
SEVENPRIME-KUMMER: CONDITIONAL CHILD PASS
H8H9-SOURCE-TO-KUMMER45: SOURCE BLOCKED
287-FIXED-CERTIFICATE-SMOOTH-PARITY45 ANALYTIC ESTIMATE: OPEN
FIXED-CERTIFICATE LEAKAGE COMPILER: KERNEL PASS
287-FIXED-CERTIFICATE-LEAKAGE45 ANALYTIC ESTIMATE: OPEN
GENERATED-(7.23) FIXED-gStar SPECIALIZATION: MAY STILL BE NEEDED
ERDOS287: OPEN
```

```
EXACT FIRST OPEN AFTER THIS RUN:
287-FIXED-CERTIFICATE-SMOOTH-PARITY45 — the two fields of
Erdos287.SmoothParity.FixedCertificateSmoothParityPacket (first the source
obligation `cell_identity`, then the analytic bound).

NEXT MATHEMATICAL ACTION:
Obtain the literal Ford factorisation of G_{g*}(m;n) and prove that its k = 0,
J = ∅ cell equals ∑_{d | n, d ≤ n^(1/2−ε)} μ(d) on the smooth sector, i.e.
inhabit the `cell_identity` field.
```

The Properties table has been updated with the new V11 and V12 deliverables and their statuses.

# Summary of changes for run fbe73b56-3c29-4b1a-926b-1a4159cafede
**Erdős #287 is NOT solved, and nothing in the project claims it is.** All work is committed and pushed; `lake build` passes (8086 jobs) with no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide` or `@[implemented_by]` anywhere, and every new theorem depends only on `propext`, `Classical.choice`, `Quot.sound`. No existing theorem was edited, renamed, weakened or deleted; the full written audit (sections A–AD, the Q1–Q30 matrix, counterguard check and final verdict block) is `ERDOS287_END_TO_END_CLOSURE_REPORT.md`.

**Files added**
- `RequestProject/Erdos287/ProblemStatement.lean` — the exact public predicate `Erdos287Counterexample` (card ≥ 2, all denominators > 1, reciprocal sum 1, all gaps ≤ 2), the **one-way** bridge `toGap2CE`, the junk inhabitant `gap2CE_one` (`A={1}`) showing the historical type is strictly broader, `three_le_max`/`four_le_max`, the ordered-sequence form of the public statement (with `k ≥ 2` derived, not assumed), and two non-vacuity guards.
- `RequestProject/Erdos287/FiniteMasterReduction.lean` — the requested patch: sign-sensitive `PlusSophieWitness` (`M/3 < q ≤ (M−1)/2`, `2q+1` prime) and `MinusSophieWitness` (`M/3 < q ≤ ⌊M/2⌋`, `2q−1` prime), both with `q ≥ 5`, their floor-form equivalences, the master theorem `Erdos287Counterexample → SophieWitness (max A) → False`, the retained `39 ≤ M ≤ 250` sweep, and the new free blocker `maxDivisorPrime_blocker` (hence: no counterexample has a prime maximum, none has `M = 2q`). The hypothesis `q² > M` proposed for that blocker is unnecessary — it follows from `M < 3q`, `q ≥ 4` — so it was dropped rather than carried.
- `RequestProject/Erdos287/FiniteRemainder.lean` — the interval-certificate engine: the certified table `CVal` with `C_le_CVal` (from the banked `C 1 … C 9`), and `Gap2CE.blocker_window`, which turns one certificate into exclusion of a whole interval `[L,U]` of maxima.
- `RequestProject/Erdos287/FiniteRangeExtension.lean` — a chain of 34 certificates: **no counterexample with `3 ≤ M ≤ 4·10⁹`** (previously `39 ≤ M ≤ 250`). All primality is discharged by `norm_num` (largest prime used 1 546 710 859); elaboration ≈ 25 s.
- `RequestProject/Erdos287/ClosureInputs.lean` — `WindowPairSupply M`, proved to be implied by a Sophie witness (so the frontier is *weaker* than Sophie–Germain), the non-circular `Erdos287ClosureInputs` (explicit threshold inside the verified range + the supply statement; no field is or implies the conclusion) and the deterministic compiler `Erdos287ClosureInputs → Erdos287Statement`, plus its ordered form.
- `RequestProject/Status/Erdos287EndToEndStatus.lean` — axiom prints for all new theorems and for the preserved V1/V2 bank; also the rational check `1/6 > 1663/10000`.
- Appended to `RequestProject/TrustedBank/R9/Certificate.lean`: `lowSum_eq` (`∑_{j=0}^{4}(−1)^j C(9,j) = 70`) and the cancellation of the two halves — labelled explicitly as binomial identities, **not** `H(n) = 70`.

**Answers to the key questions.** Public statement: represented exactly. `Gap2CE`: broader, not equivalent; only the needed direction is proved. Unconditional finite range: `3 ≤ M ≤ 4·10⁹`. R9 leakage, `H(n)=70`, fresh `c₉`, convolution/multiplicity, `f+δ`, Full-Nine bridge, SW2 shell, Gate-1A/1B, the 287 generated-packet census, generated-(7.23), `C_FM`, Gate-0 Type I, (b.2), N2, prime mass: **not banked / open** — the Ford–Maynard source definitions (Def. 4.3, (7.17), Prop. 7.22, (7.23), Thm 8.3) exist in this repository neither as Lean objects nor as text, so instantiating them would have meant inventing a schematic substitute; nothing was fabricated and no uninhabited interface is used by a proved theorem. `GATE1A_REQUIRED_FOR_287`: unknown (answerable only by the census). No `erdos287` theorem is declared, since the closure structure has no inhabitant.

**Verdict:** `ERDOS287_ALL_INTERNAL_COMPILERS_CLOSED_EXTERNAL_ANALYTIC_INPUTS_REMAIN`. **First exact remaining blocker:** `Erdos287ClosureInputs.supply`, i.e. `∀ M ≥ M₀, WindowPairSupply M` — for every large `M`, two consecutive integers in `[⌈M/2⌉, M]` each divisible by a prime power `> M/10`; an almost-prime-pair statement of Ford–Maynard type, weaker than the Sophie-Germain-type supply used before, and not proved here.

# Summary of changes for run 1453135a-faad-46d6-a201-4be69b18608e
Confirmed receipt of the Erdős-287 material in the project and worked only from it (no external sources were loaded). Both requested runs were carried out proof-first; **#287 is not claimed solved**, and no statement is made anywhere about the supply of Sophie-Germain-type primes for large M. The full written audit is in `ERDOS287_SOPHIE_V1_V2_REPORT.md`.

**Files added** (append-only; no existing theorem edited, weakened or deleted):
- `RequestProject/Erdos287/SophieOptimal.lean` — V1 route
- `RequestProject/Erdos287/SophieBandCompiler.lean` — V1 band
- `RequestProject/Erdos287/V2SophieFinite.lean` — V2 finite/top-layer route
- `RequestProject/Erdos287/V2SophieBand.lean` — V2 band compiler
- `RequestProject/Erdos287/V2BandSupplyChecks.lean` — maximal band + finite sweeps
- `RequestProject/Status/Erdos287V2Status.lean` — status ledger with axiom prints
- `RequestProject/Main.lean` — import lines only

**Source pins (printed before proving).** TL_PIN: `Erdos287.topLayer_congruence` (`Erdos287/TopLayer.lean`), general layer, `Finset ℕ`/`ZMod p` types, cofactors `ordCompl[p] a`, nonemptiness via `1 ≤ topExp A p`, with corollaries `topLayer_card_ne_one`, `topLayer_two_obstruction`, `topLayer_three_obstruction`. ISOLATED_HOLES_PIN: `Erdos287.Gap2CE.holes_isolated` on the closed window `[N,M]`, hole = `∉ A`. No pin failure.

**V1 (threshold route).** `Gap2CE.N_le_of_M_lt_two_mul` (the archive's `e` is literally `Real.exp 1`, so `2 < e` is legitimate — no mismatch); `excludedPP_of_window_two`; `Gap2CE.plus_sophie_blocker`, `Gap2CE.minus_sophie_blocker` (both strictly stronger than the banked `safePrime_blocker`); `band_hypotheses`, `band_exact`, `window_ge_two_of_two_mul_le`; conditional band compiler stated with the supply as an explicit hypothesis (never an axiom). C(2) pin: definition, `C_two` proved by kernel `decide`, `C_spec` greatest — **C2_PIN_PASS**.

**V2 (finite/top-layer only, superseded inputs avoided).** `Gap2CE.halfRange_min_le` (`N ≤ ⌊M/2⌋`), `topExp_le_one_of_lt_sq`, `topHalf_prime_hole`, `q_and_two_mul_q_holes`, `Gap2CE.v2_plus_sophie_blocker`, `Gap2CE.v2_minus_sophie_blocker`, `v2Band_hypotheses`, `Gap2CE.v2_band_plus_blocker` / `v2_band_minus_blocker` / `v2_finite_compiler`, `Gap2CE.v2_exact_compiler`, `no_Gap2CE_M_eq_104`, `sophieWitness_sweep` and `no_Gap2CE_of_M_in_39_250`. The V2 files import only `TopLayer.lean` and `Counterexample.lean`, so neither the `e(N−1)<M` placement nor the `C` threshold is a dependency; both stay in the bank untouched as redundant historical lemmas.

**Repairs found.** (1) `halfRange_min_le` is false without `2 ≤ M`: `A = {1}` satisfies every field of the counterexample structure and there `N = 1 > 0 = ⌊M/2⌋`; the hypothesis was added. (2) The fixed bands `(3/4,4/5)` and `(7/10,24/25)` have real supply gaps — kernel-checked witness `v2Band_supply_gap_152` at `M = 152` — so the finite sweep uses the maximal admissible band `M/3 < q ≤ (M−1)/2`; its small-`M` gap ends at 38 (`not_sophieWitness_35`).

**New unconditional finite consequence.** No gap-≤2 counterexample has `39 ≤ M ≤ 250` (`no_Gap2CE_of_M_in_39_250`), by kernel `decide` over the maximal band. A wider scan was exploratory only and is flagged as unverified in the report.

**Kernel audit.** BUILD: succeeds (8080 jobs). SORRY/ADMIT: none in the new files, none anywhere in `RequestProject`. No `axiom`, `unsafe`, `native_decide`, or `@[implemented_by]`; all finite certifications use ordinary kernel `decide`. AXIOMS: every new theorem reports only `propext, Classical.choice, Quot.sound` (two report less), printed by the status file.

**Verdicts.** V1: `ERDOS287_SOPHIE_FINITE_COMPILER_PASS_WITH_REPAIRS`. V2: `ERDOS287_V2_FINITE_COMPILER_PASS_WITH_REPAIRS`.

**Exact surviving interface** (Lean: `Erdos287.Gap2CE.v2_exact_compiler` / `Erdos287.no_Gap2CE_of_sophieWitness`): for a hypothetical gap-≤2 counterexample with maximum denominator M, the existence of a prime q with M/3 < q ≤ (M−1)/2 and 2q−1 or 2q+1 prime yields a contradiction. This condition is finite and decidable for each fixed M and is verified for 39 ≤ M ≤ 250; nothing is claimed about its validity for large M. All work is committed and pushed.

# Summary of changes for run ca26ff1f-8d7d-4b5e-956c-2175ae3c0a68
**TRUSTED_BANK_DELTA6_PARTIAL_SOURCE_FIELDS_MISSING**

Gate 1A, Gate 1B, ACBV45 / RLS45 / mixed-start NSE, the R9 analytic-mass question and Erdős #287 all remain **OPEN**; nothing in the project claims otherwise. Work was done inside the existing Lean project (toolchain and Mathlib pin unchanged). The full report, in the requested A–O format, is `TRUSTED_BANK_DELTA6.md`.

**A. Build status.** `lake build` succeeds (8074 jobs). Archaeology before editing: build succeeded, no sorries, no stale status labels, one long-standing duplicated *definition* (`lcmUpto` / `lcmUpTo`, identical bodies) left as-is and re-flagged.

**B. Files added:** `RequestProject/TrustedBank/Gate1A/{ScaleLedger,RowConservation,AvgJDRInterface}.lean`, `TrustedBank/Gate1B/{CenteredRho,MobiusCollapse,SeparableWeights,StartInjectivity}.lean`, `TrustedBank/R9/Certificate.lean`, `TrustedBank/Erdos287/GoodPrime.lean`, `Challenges/Delta6Interfaces.lean` (open statements only), `Status/Delta6Ledger.lean` (ledger + bibliographic records), `Validation/Delta6HostileTests.lean`, `TRUSTED_BANK_DELTA6.md`. Modified: `Audit/BankStatus.lean` (axiom prints). No existing theorem edited, renamed, weakened or deleted.

**C. New kernel-proved results.** Gate 1A: exact rational scale ledger with `(natural)/(target) = M/H` and the three gaps `1/18, 1/36, 1/24` at V1/V2/V3; M-row conservation `∑‖X‖² = (∑|w|²)(∑‖x‖²)` with invariance under permutation, unitary maps, direct-sum relabelling and unit-modulus diagonals (establishing only that reorganisation does not erase the row L² mass); AVG-JDR closure as a *conditional* theorem. Gate 1B: the centered identity `ρ(dp) = ρ_d ρ_p + ρ_d/p + ρ_p/d` for coprime d,p; `μ(q/p) = −μ(q)` for squarefree q; the clean collapse to `−μ(q)Λ♯(q)` for product-separable weights; SOURCE-MMD on a clean cell; `SeparableWeightDecomposition` with cost inheritance; same-start injectivity. R9: `∑_{j=5}^{9}(−1)^j C(9,j) = −70` and hence certificate value `70·g(∅)` under the supplied formula. Erdős #287: `GoodPrime`, Good Prime Exclusion, the adjacent good-factor blocker, and the finite (abstract-J) log-cofactor blocker.

**D. Repaired / false statements.** None of the new statements was false. Three deliberate counterexamples are banked and each forces a hypothesis: non-coprime ρ-pairs (d=p=2), the repeated-prime sector (q=4) for the Möbius collapse, and a mixed-start collision showing `T < u` does not give a cross-start diagonal (so mixed-start stays open).

**E. Axioms.** Every new theorem reports only `propext, Classical.choice, Quot.sound` (one reports only `propext`; the C(1..8) certification still reports none). A full scan finds no `sorry`, `sorryAx`, `admit`, `axiom`, `unsafe`, `native_decide` or `@[implemented_by]` anywhere.

**K. Source fields missing** (never invented, always hypotheses or empty specification records): the Gate-1A source identity `Ctilde = H·S + negligible`, the actual nonseparable source weight (`SourceMMDRequirements`, no inhabitant), and the exact Ford `H_g` formula.

**M/N/O — first remaining inputs.** Gate 1A: the authoritative source identity, then SOURCE-AVG-JDR itself. Gate 1B: a separable decomposition (with cost) of the actual smooth weight plus the remaining source fields. #287: the global `LCB_η` adjacent supply with an effective threshold and finite verification below it.

All work is committed and pushed.

# Summary of changes for run 961652a0-7e81-4f59-90e5-e00c79ffb600
**Headline: TRUSTED_BANK_EXTENDED.** Erdős #287, Gate 1A and Gate 1B remain **OPEN**; nothing in the project claims otherwise.

Work was done inside the existing Lean project (toolchain `leanprover/lean4:v4.28.0`, Mathlib rev `v4.28.0`, both unchanged). Full details are in the new `TRUSTED_BANK_AUDIT.md`.

**Archaeology (state before the run).** `lake build` succeeded. The existing Erdős-287 package (18 files under `RequestProject/Erdos287/`, ~130 theorems) was sorry-free except for **three sorries in `RequestProject/Erdos287/Uniform.lean`**. No stale/retracted theorems; one duplicated *definition* (`lcmUpto` in `Universal.lean` vs `lcmUpTo` in `RoughPrime.lean`, identical bodies, confusable names) — left as-is and flagged rather than silently merged.

**The project is now completely sorry-free.** The three remaining sorries were closed: `Erdos287.C_le_lcm_mul_harmonic` (C(j) ≤ lcm(1..j)·H_j), `Erdos287.harmonic_le_nat` (H_j ≤ j), `Erdos287.C_le_U` (C(j) ≤ j·j!). The uniform window-exclusion and forced-hole results that rested on them are now unconditional.

**Banked this run** (all under `RequestProject/TrustedBank/`, all kernel-checked, none importing anything open):
- Bank A `FixedAffine/Basic.lean` — a₁·L₂(n) = a₂·L₁(n) + Δ over any commutative ring, good-prime root transport, and the unit −a₂/Δ sending the two forbidden roots to {0,1}.
- Bank B `FixedAffine/UnitTransport.lean`, `Interfaces/FiniteSumTransport.lean` — unit-multiplication bijectivity, sum/ℓ²-energy invariance, and the exact Kloosterman-shaped reindexing S(A,B;q) = S(Aλ, Bλ⁻¹; q).
- Bank C `Interfaces/ZeroSetTransport.lean` — fixed-unit twists preserve simultaneous zero sets, their cardinalities and weighted sums.
- Banks D+E `Erdos287/BoundedCofactor.lean` — the Bézout parametrisation e·Q − d·P = 1 with the full coprimality package, and the local criterion **admissible ⟺ d·e even**, tested on small examples.
- Bank F `FixedAffine/SingularFactors.lean` — local root counts ν(ℓ) = 1 / 2 and the (ℓ−1)/(ℓ−2) correction (no infinite Euler product).
- Bank G `FixedAffine/CofactorIntensity.lean` — J(n) ≤ J(2) with equality iff n = 2, hence {d,e} = {1,2}.
- Bank H `FixedAffine/SymmetricPacket.lean` — odd-character ± cancellation, instantiated for Dirichlet characters.
- Erdős #287: `Erdos287/CarryTower.lean` (lcm² ∣ ∏a and lcm ∣ ∏ pairwise differences, for reciprocal-sum-1 sets) and `Erdos287/TopLayerConsequences.lean` (generalized fixed-cofactor blocker with every numerical hypothesis explicit).

**Repairs found (section B).** (1) The requested blocker threshold `C(2j−1)` is **not sufficient on its own** — with p = j·q ± 1 and M < 2p the window ⌊M/q⌋ can equal 2j; the repaired theorems use `C(2j)`, and a sharp-window variant keeps `C(2j−1)` under the added hypothesis ⌊M/q⌋ ≤ 2j−1. (2) "lcm² ∣ product" and "lcm ∣ pairwise-difference product" are **false for general finite sets** (A = {2,3}, counterexamples banked) and true under the reciprocal-sum hypothesis, which is the form banked. No statement was weakened.

**Open lines, isolated in `RequestProject/Challenges/`** (Prop-valued targets and interface structures, so no `sorry` and no `axiom`, and never imported by the bank): Gate 1A SB-ν (`SubpolynomialFibre`, plus a proof of its invariance under fixed-unit twists); Gate 1B with the exact one-completion source, β = μ_D·Λ_P linear, the 1/104 margin arithmetic, and the Gate conclusion derived from an explicit convolution-BV interface (NPCF-2C38 recorded dead, not revived); the affine source glue; and a Ford-type blocker-supply dependency specification (Ford–Maynard is *not* postulated as a Lean fact). Note: the authoritative Gate-1A/1B source definitions are not present in this repository, so those challenges are stated against abstract interfaces — this is recorded in the files.

**Audit artefacts.** `RequestProject/Audit/BankStatus.lean` prints axioms for 94 banked theorems — every one reports only `propext, Classical.choice, Quot.sound` (the C(1..8) certification depends on none). `RequestProject/Validation/BankStatements.lean` restates 26 banked results in unfolded form for an independent comparator.

**Final status:** `lake build` completes successfully (8062 jobs); a scan of all Lean sources finds no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `skipKernelTC` or `@[implemented_by]`; new-file linter warnings were fixed at the root. All work is committed and pushed.


# Summary of changes for run 840a104e-1f96-4573-b622-5c483c1e8808
Continued Erdős #287, proof-first and machine-checked. #287 is NOT claimed solved. No prime-distribution / analytic input was used. Both follow-up requests were completed; the whole project builds (`RequestProject.Main`) and every new theorem depends only on the allowed axioms `propext`, `Classical.choice`, `Quot.sound`, with no `sorry`/`axiom`/`unsafe`/`native_decide`.

## Files added
- `RequestProject/Erdos287/NonAdjacentHoles.lean` — the distance-`d` hole investigation.
- `RequestProject/Erdos287/KernelAPBlocker.lean` — the Kernel AP-blocker.
- `RequestProject/Erdos287/NONADJACENT_HOLES.md` — written analysis answering all targets.
- `RequestProject/Main.lean` — imports the two new files.

## Part A — do two holes at distance d > 1 force a contradiction?
Verdict: **No — no non-adjacent-hole contradiction survives.** The gap-≤2 constraint (`holes_isolated`, symbolically `LocallyAdmissible`) is a nearest-neighbour rule whose only forbidden pattern is two *adjacent* holes; that is exactly why the existing `blockerPair_contradiction` works only at distance 1.

Theorems (all in namespace `Erdos287`):
- `twoHoleWord`, `twoHoleWord_has_two_holes`, `twoHoleWord_locallyAdmissible` (d ≥ 2 admits two holes at distance d — refutes the distance-d claim), `twoHoleWord_one_not_admissible` (d = 1 is the unique local contradiction), `no_nonadjacent_local_contradiction`, `distance_band_admissible` (covers the whole band d ∈ {2,…,246}).
- Stronger variants, all shown compatible: `many_holes_block` + `altWord_block_locallyAdmissible` + `altWord_holes_nonadjacent` (a block of 123 forced non-adjacent holes inside an interval of length 246); `mod3HoleWord` + `mod3HoleWord_locallyAdmissible` + `mod3HoleWord_both_parities` (dense holes in both parity classes); `gcd_controlled_models` (coprime and non-coprime endpoints); `exists_residue_in_interval` and `exists_crt_at_distance` (the CRT mechanism can *produce* two hole-forcing multiples at any prescribed distance d ≥ 1, but for d ≥ 2 they are non-adjacent, so `blockerPair_contradiction` never fires).

Local models (counterexamples) provided: `twoHoleWord` (distance d), `altWord` (one parity / dense block), `mod3HoleWord` (both parities) — each proven `LocallyAdmissible`.

## Part B — the Kernel AP-blocker
Formalized and proved. For a `Gap2CE` with M ≥ 8152 and a prime p, with `qₚ = ceilMod p` and kernel modulus `Qₚ = kernelMod p` (= q₂ for p = 2, else 2·qₚ):
- `Gap2CE.HoleForcing.of_dvd`, `Gap2CE.ceilMod_dvd_kernelMod`, `Gap2CE.one_le_kernelMod`, `Gap2CE.kernelMod_holeForcing`.
- `Gap2CE.AP_prime_kills_holeForcing_add` (the +1 companion of the existing −1 lemma).
- `Gap2CE.kernel_AP_blocker` — no prime r ∈ [N+1, M−1] has r ≡ ±1 (mod Qₚ) (stated as Qₚ ∣ (r−1) ∨ Qₚ ∣ (r+1)); and `Gap2CE.kernel_AP_blocker_modEq`, the same in literal `Nat.ModEq` form. Proof: Qₚ ∣ (r∓1) ⟹ qₚ ∣ (r∓1) so r∓1 is a ceiling hole, r is a prime hole by `primeFree`, giving two adjacent holes, contradiction.

## Status
- Build: succeeds. Placeholders in the new files: none. Pre-existing `sorry`s in the unrelated `Erdos287/Uniform.lean` were left untouched (out of scope). Minor lint warnings in other pre-existing files are unchanged.
- A note on faithfulness: `exists_crt_at_distance` needed the extra hypothesis `1 ≤ d` (without it the statement is false in a degenerate N > M / d = 0 case); the intended use is d ≥ 2.

# Summary of changes for run 04a37366-3621-404e-9539-e5aed97ab049
Formalized the Ceiling–CRT Pairing package and the Large-Ceiling / rough-prime reduction for Erdős #287, proof-first and machine-checked. #287 is NOT claimed solved. No analytic number theory, no Sophie-Germain / BP★ / Chen-P₂ / Bateman–Horn were used.

Files changed:
- `RequestProject/Erdos287/CeilingCRT.lean` (new) — ceiling-modulus package and AP reduction.
- `RequestProject/Erdos287/RoughPrime.lean` (new) — rough-prime top-layer exclusion.
- `RequestProject/Main.lean` — added imports of the two new files.

Definitions added (in namespace `Erdos287`, most under `Gap2CE`): `ceilMod p := p^(topExp A p + 1)` (the ceiling modulus qₚ), `HoleForcing Q`, `isCeilModOfPrime`, `minCeil` (= minₚ qₚ), `APPrimeInInterval`; and `lcmUpTo j := (Finset.Icc 1 j).lcm id`.

Theorems proved (Ceiling–CRT):
- `ceilingMultiples_are_holes` — if p prime, x∈[N,M], qₚ∣x then x∉A (Target 1).
- `exists_crt_adjacent` — CRT interval-residue lemma: coprime Q₁,Q₂≥1 with Q₁Q₂≤M−N give x∈[N,M−1] with Q₁∣x, Q₂∣(x+1).
- `coprimeHoleModuli_CRT_pair` (Target 2/4) — coprime positive hole-forcing moduli with Q₁Q₂≤M−N give a contradiction; alias `coprime_holeForcing_contradiction`.
- `coprime_ceilMod`, `ceilingCRT_contradiction`, and `ceilingCRT_pairing` (Target 3) — for distinct primes p,r: qₚ·q_r > M−N; alias `ceilMod_mul_gt`.
- `atMostOne_small_ceiling` (Target 4, ℕ form: not both qₚ²,q_r² ≤ M−N), `at_most_one_ceilMod_le_sqrt` (√ form), `ceilMod_two_three_gt` (q₂q₃>M−N), `max_ceilMod_two_three_gt_sqrt`.
- `minCeil_isCeilMod`, `minCeil_holeForcing`, `AP_prime_kills_holeForcing`, `AP_prime_kills_ceiling`, `AP_prime_kills_minCeil` (Target 5), `LargeCeilingReduction` (Target 6), `no_Gap2CE_of_APPrime` (optional Target 6).

Theorems proved (rough prime):
- `lcmUpTo_pos`, `num_div_nat_le`, `num_le_j_mul_lcm`, `C_le_j_mul_lcm` (the crude bound C j ≤ j·lcm(1..j)), and `roughPrime_topLayer_empty` — for prime ℓ with ℓ²>M and j=⌊M/ℓ⌋≥1, if ℓ > j·lcm(1..j) then no element of A is divisible by ℓ (reduced to the certified `primePower_window_exclusion` at exponent 1 via the crude bound).

Build status: the project builds successfully (`RequestProject.Main`).

Placeholders: none in the two new files — no `sorry`, `axiom`, `unsafe`, or `native_decide` (the C 0 base case uses ordinary kernel `decide`). Representative theorems were checked to depend only on the allowed axioms `propext`, `Classical.choice`, `Quot.sound`.

No statement was found to be false, so no counterexample was needed. Notes: in `roughPrime_topLayer_empty` the hypothesis ℓ²>M is kept because the problem states it but is not needed by the proof (documented in the docstring); likewise `ceilingMultiples_are_holes` keeps x∈[N,M] as requested though divisibility alone forces the hole. Pre-existing `sorry`s in the unrelated `Erdos287/Uniform.lean` were left untouched (outside this task's scope).

# Summary of changes for run d1ddc5ae-e548-4cee-ae41-d8843d248054
Audited the Chen / P₂ relaxation of the blocker-pair contradiction in the Erdős #287 kernel. Work is proof-first and machine-checked; #287 is not claimed solved. All results build and use only the allowed axioms (`propext`, `Classical.choice`, `Quot.sound`), with no `sorry`/`axiom`/`unsafe`/`native_decide`.

Verdict: No — one side of a blocker pair cannot be relaxed from a prime power to a P₂ (semiprime / controlled almost-prime) while still forcing a hole via the top-layer / prime-power exclusion theorem. The natural relaxation is false.

Files changed/added:
- `RequestProject/Erdos287/ChenP2Audit.lean` (new) — the formal audit.
- `RequestProject/Erdos287/CHEN_P2_AUDIT.md` (new) — the written audit answering Tasks 1–4.
- `RequestProject/Main.lean` — now also imports `ChenP2Audit`.

Task 1 (exact relaxed statements): `IsP2`; `ExcludedP2Naive M q` (the most favourable literal analogue of `ExcludedPP`: `q = p₁·p₂`, product window `⌊M/q⌋`, threshold `C(⌊M/q⌋) < p₁`); the relaxed exclusion primitive `P2ForcesExclusion`; and the relaxed blocker-pair theorem `RelaxedBlockerPair` (one side P₂, other side prime power).

Task 2 (attempt): the exclusion proof (`primePower_window_exclusion`) is intrinsically single-prime — divisibility by pᵉ forces the top p-adic layer, whose numerator is ≤ C(⌊M/pᵉ⌋) yet ≡ 0 (mod p). A semiprime provides no single dominant modulus, so the top-layer congruence has nothing to run against; the relaxation is not provable.

Task 3 (false — concrete configuration): `not_P2ForcesExclusion` refutes the primitive. Witness: A = {2,3,6} with ∑ 1/a = 1 (`p2_witness_sum`), M = 6, semiprime q = 6 = 2·3. Its favourable product window ⌊6/6⌋ = 1 gives C 1 = 1 < 2, so the naive P₂ rule predicts a hole at 6 (`p2_six_excludedNaive`), yet 6 ∈ A, so no hole is forced. `p2_window_illegitimate` isolates the fallacy: the argument only ever legitimately offers an individual prime factor's window ⌊M/pᵢ⌋, and both fail here (C(⌊6/2⌋)=11≥2, C(⌊6/3⌋)=3≥3); the relaxation illegitimately shrinks ⌊M/pᵢ⌋ to ⌊M/q⌋. The only sound way a P₂ forces a hole is when a prime factor is itself an excluded prime power (`P2_excluded_via_prime_factor`), which reduces to the existing prime case and is not a genuine relaxation.

Task 4 (Chen tail): No usable infinite tail. A Chen-type theorem yields infinitely many (prime, P₂) neighbours, but converting them to blocker pairs needs the P₂ side to force its hole (`RelaxedBlockerPair`/`P2ForcesExclusion`), which is false (`chen_no_usable_tail`). The prime side gives one hole, the P₂ side none, so no adjacent double hole arises. Since the P₂ relaxation fails, the sound blocker inputs remain the genuine prime-power / large-prime-factor pairs already certified. (Per the instructions, Bateman–Horn and Sophie-Germain are not needed here; the existing `safePrime_blocker` already handles the genuine large-prime case.)

Build: succeeds (`RequestProject.Main`, 8040 jobs). Pre-existing lint warnings in other files are unchanged; the new file is warning-free.

# Summary of changes for run a1eae949-bf51-4fea-812e-515df0bc4c32
Completed the requested audit of the "Fable SFT / follower-graph" proposal for Erdős #287 (no claim that #287 is solved), backing every conclusion with machine-checked Lean.

Verdict: Fable's SFT schema matches the certified kernel only partially. The kernel splits into a genuinely local (radius‑1 SFT) *gap layer* and an essentially *non‑local* arithmetic layer that depends on the global parameters N, M, q = pᵉ, ⌊M/q⌋ and the top‑layer maximum. A fixed finite alphabet with a scale‑invariant local rule captures the gap layer but not the arithmetic layer, so the literal SFT schema is not valid for the whole kernel.

First mismatch: the exclusion rule is not scale‑invariant and the alphabet is not finite. The same prime power q = 2 is excluded at M = 3 but not at M = 4 (`excludedPP_three_two` vs `not_excludedPP_four_two`), and the residue modulus ranges over all primes (`modulus_alphabet_unbounded`).

New files:
- `RequestProject/Erdos287/SFTAudit.lean` — formalizes the audit. Local layer: `Cell`, `LocallyAdmissible`, `Gap2CE.word`, `word_eq_hole_iff`, `Gap2CE.word_locallyAdmissible` (the gap constraint IS a nearest‑neighbour SFT forbidding the block (hole,hole)). Dichotomy (A): `Gap2CE.holes`, `Gap2CE.holes_card_le_A`, `Gap2CE.two_mul_holes_le` (boundedly many holes). Dichotomy (B): `altWord`, `altWord_periodic`, `altWord_locallyAdmissible`, `altWord_has_hole` (the local subshift has periodic "fakes", so local rules alone cannot refute a counterexample). Non‑locality obstructions: `modulus_alphabet_unbounded`, `excludedPP_three_two`, `not_excludedPP_four_two`.
- `RequestProject/Erdos287/SFT_AUDIT.md` — the written audit answering Tasks 1–4, including the recommended sound replacement (the interval / blocker‑pair‑chain certificate graph already formalized in `Erdos287/Chain.lean`: `ChainLink`, `chainFrom`, `BlockerChain`, `BlockerChain.refutes`).
- `RequestProject/Main.lean` — now also imports `SFTAudit`.

Task 4 required output:
- Schema match: partial (local gap layer yes; arithmetic layer no).
- First mismatch: scale‑dependence of exclusion + unbounded prime modulus (theorems named above).
- Theorems formalized: all listed above.
- Build: succeeds (`RequestProject.Main`, 8039 jobs).
- Placeholders: none — no `sorry`, `axiom`, `unsafe`, or `native_decide`; all audited theorems reduce to only `propext`, `Classical.choice`, `Quot.sound` (verified).

Note: this turn built on the reusable certificate framework added earlier in the session (`Blocker.lean`, `Fiber.lean`, `Universal.lean`, `BadPrimes.lean`, `Chain.lean`), which is likewise complete and placeholder‑free; the audit's recommended replacement graph is the `Chain.lean` API.

# Summary of changes for run 35c8cb58-6495-4e1c-af75-56e158c4889f
Certified the elementary structural / prime-power-exclusion package for Erdős #287. The project builds cleanly and is free of `sorry`, `axiom`, `unsafe`, and `native_decide`; every result depends only on the allowed axioms (`propext`, `Classical.choice`, `Quot.sound`), and the certified `C` values depend on no axioms at all. #287 itself is NOT claimed solved — the open blocker-pair (BP) input was deliberately left untouched, as requested.

## Files changed
- `RequestProject/Main.lean` — now imports the whole package (previously just options).
- `RequestProject/Erdos287/Defs.lean` (new) — definitions.
- `RequestProject/Erdos287/Cnum.lean` (new) — the numerator bound `C`.
- `RequestProject/Erdos287/TopLayer.lean` (new) — targets 1–2.
- `RequestProject/Erdos287/Window.lean` (new) — target 4.
- `RequestProject/Erdos287/Counterexample.lean` (new) — target 5.
- `RequestProject/Erdos287/PrimeFree.lean` (new) — targets 6–7.

## Theorems proved (by task target)
Definitions: `topExp`, `topLayer` (with `mem_topLayer`, `topLayer_subset`); `addF`, `sumP`, `numOf`, `denOf`, `C` (a kernel-reducing list computation).

1. `topLayer_congruence` — ∑ over the top p-adic layer of the mod-p inverse cofactors is 0 in `ZMod p`.
2. `topLayer_card_ne_one`; `topLayer_two_obstruction` (p ∣ m₁+m₂); `topLayer_three_obstruction` (p ∣ m₁m₂+m₁m₃+m₂m₃).
3. Bridge `sumP_spec`, `numOf_eq_num` (links the computation to `Rat.num`); explicit values `C_one…C_eight` and bundled `C_values` proving `C(1..8) = (1,3,11,25,137,137,1019,2143)` by kernel `decide`; `C_seven_witness` verifying `C 7 = 1019` is attained by `{1,2,3,4,5,7}` (via `norm_num`); plus faithfulness `num_le_C`, `C_attained`, `C_spec` (`IsGreatest`), and `C_mono`.
4. Helper `dvd_num_of_sum_inv_zero`; `primePower_window_exclusion`.
5. `Gap2CE` structure with `N`, `M`, `N_mem`, `M_mem`, `mem_Icc`, `holes_isolated`, `exp_lower` (e·(N−1) < M), `exp_upper` (M ≤ e²·(N+1)), and `N_gt_M_div_eight` (M ≥ 97 ⇒ M < 8·N, i.e. N > M/8).
6. `Gap2CE.primeFree` — for M ≥ 8152, no denominator is prime (via `primePower_window_exclusion` with e=1, `C_mono`, `C_seven`, and N > M/8, using (7+1)·C(7) = 8152).
7. `Gap2CE.blockerPair_contradiction` — two consecutive holes in [N,M] are impossible.

## Build / soundness status
- Build: succeeds (only lint warnings remain — see below).
- No `sorry`/`axiom`/`unsafe`/`native_decide`/`admit`. The C-value certifications use ordinary kernel `decide` on a bespoke reducing computation (`Rat` arithmetic does not reduce in the kernel, so a list-based reduced-fraction fold, proven equal to `Rat.num`, is used instead).
- No statement was found to be false, so no counterexample was needed.

## Notes
- `primePower_window_exclusion` keeps the hypothesis `hqM : p^e ≤ M` because the problem states it, but the proof does not need it (documented in its docstring); this yields one `unused variable` lint warning.
- A handful of `unused simp argument` lint warnings remain inside machine-generated proofs; they are informational only and do not affect correctness. Everything else is complete.