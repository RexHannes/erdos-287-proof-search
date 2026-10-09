# Erdős #287 — integrating `FCHS_AND_PARAMETER_REPAIR.md` and `AUDIT_REPORT.md`

**Verdict: REPAIR / TAIL OPEN.** Erdős #287 is still open. `Tail287Statement` is **not** proved.

## Do the supplied notes help close what remains?

Partly. They help with the **algebraic and interface** part of what is left. They do **not**
discharge any analytic input. Here is what changed in Lean.

| Note item | Status after this run |
|---|---|
| A. paying `FCHS` (`F ≤ cB₀`, `H ≤ dS`) | **proved** (`FCHS_le_B0CS2`, `FCHS_le_const_B0CS2`, `pascadiInner_le_two`, `pascadiInner_le_const`, `sqrt_pascadiInner_le`) |
| B. `g`-scaling with the last term kept | **proved** (`pascadi_g_scaling`, exact identity; `pascadi_g_scaling_le`, the `1/g` bound for `g ≥ 1`) |
| C. Pascadi's intermediate normalization | **proved** (`pascadi_normalized_identity`: the intermediate `FCHS/B₀` stage normalizes to `…FHS`, not `…FCHS`); `regr_normalizations_differ` |
| C. direction of `pascadiInner_ge_old` docstring | **fixed** in `W4Route.lean`. It now reads: old ≤ new, so a bound by the old RHS implies a bound by the new RHS, and not the converse |
| D. parameter ledger `ε = κ/2000`, `σ = κ/10⁶`, `δ = σ/4` | **proved** (`old_packet_margin_neg`: `-327κ/256000 < 0`; `new_packet_margin_eq/pos`: `63609κ/256000000 > 0`; `sigmaBase_le_eps_div_100`; `two_deltaSpec_lt_sigma`) |
| Audit §5.1: affine data fixed before constants | **interface repaired** (`PascadiCriticalCellProviderScoped`, `OrdinaryBVUremProviderScoped`: `A > 0`, `B ≠ 0`, `gcd(A,|B|) = 1`, roughness exponent fixed first) |
| Audit §5.2: base cap | the scoped providers use `f ≤ X^{κ/10⁶}` |
| Audit §5.3: roughness, masked SW, no distribution hypothesis on BV | the scoped providers require `RoughSupport α (X^ρ)` and `SWSeqMasked` (an SW condition with a coprimality mask `(n,d)=1`, in relative-centering form). The `U`-remainder provider now has a distribution hypothesis |
| Audit §5.4: `x ≍ MN` | the scoped providers require `X ≤ 4NM` (and `NM ≤ X`) |

Two further facts are proved:

- `pascadi_scoped_of_old` and `bvUrem_scoped_of_old`: each old, over-broad provider implies its
  scoped version. So the scoped providers are strictly weaker assumptions, and nothing proved
  before is lost.
- `scalarTypeII_bound_of_scopedProviders`: the full scalar Type-II bound follows from the scoped
  providers on the restricted actual-source range.

## What the notes do not (and cannot) supply

The following items are untouched by the notes and remain open, as either mathematics or
formalization:

1. **Proofs** of `PascadiCriticalCellProviderScoped` and `OrdinaryBVUremProviderScoped`. These
   are a beyond-half estimate (Kloosterman/spectral large sieve) and a BV/BDH-type estimate. No
   Lean proof term exists for either.
2. Proofs that the actual Heath–Brown sequences satisfy `RoughSupport` and `SWSeqMasked`. The
   exact roughness threshold used in the published reduction must also be confirmed. Here it is
   an arbitrary fixed `ρ > 0`, chosen before the constants.
3. The proof that the constructed complete base (slopes, presieve, spectator lcms) satisfies
   `f ≤ X^{κ/10⁶}`. The ledger only shows that this cap is consistent.
4. `W4DiagEstimate`, `W4RamEstimate` and `W4SpecEstimate` for the actual source, and the
   instantiation of `source_to_W4` on `physCell`.
5. Noncritical Heath–Brown routing, partial summation, and the `IsLittleOTarget` bounds for a
   concrete `PhysicalFamily`.
6. A constructed `OneSidedFrameworkFor F.R F.target` (the seven-block framework).

So the notes remove some algebraic and parameter objections. The first unsupported implication
is unchanged: the beyond-half critical-cell estimate (item 1) has no proof.

## Files

- new: `RequestProject/Erdos287/SourceChain/FCHSPropagation.lean`
- new: `RequestProject/Erdos287/SourceChain/Physical/TypeII/ScopedProviders.lean`
- new: `RequestProject/Erdos287/SourceChain/RepairAudit.lean` (`#print axioms`; every listed
  theorem uses only `propext`, `Classical.choice`, `Quot.sound`)
- edited: `RequestProject/Erdos287/SourceChain/W4Route.lean` (docstring only)
- edited: the aggregators `RequestProject/Erdos287/SourceChain.lean` and `.../SourceChain/Physical.lean` (imports)

None of the new files contains `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` or
`implemented_by`. The two scoped providers are `def … : Prop` statements and are **not**
claimed as proved.
