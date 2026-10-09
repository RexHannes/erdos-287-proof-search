# Implementation handoff — replace the refuted packetwise Urem route

This is a proof-construction specification accompanying `REPORT.md`. It is not a precompiled Lean patch. Preserve all existing declarations and the reported `not_ordinaryBVUremProviderScoped` theorem.

## 0. First verify version and the negative theorem

The reviewed source is archive (6), not the newer checkout containing `UremCounterexample.lean`.
Record the actual commit and inspect:

```lean
#print OrdinaryBVUremProviderScoped
#print not_ordinaryBVUremProviderScoped
#print axioms not_ordinaryBVUremProviderScoped
```

Export the exact witness choices and compare them to the admissible family in REPORT §2. Do not assume that the witness exploits missing SW; that is not established by the theorem signature. Do not weaken or hide the negative theorem.

## 1. Keep exact algebra, replace the analytic quantifiers

Preserve:
- `scalarTypeII_eq_cells`;
- `packet_typeII_eq_cells`;
- `physCoefAtom_reassemble`;
- `physAtom_provider_contract` and `physCell_contract`;
- `atom_factorization_actual`, `H_eq_of_T`, `total_variation_le`.

Retire the path that attempts to instantiate `OrdinaryBVUremProviderScoped` in the critical range.

The required replacement is a **grouped family estimate** on actual common `alphaSeq` data, not a theorem for arbitrary `α : Packet → ArithmeticFunction ℝ`:

```text
For each actual HB/dyadic/designated-pair group G and each precision A > 0,
there exist C and X0 (depending on fixed source data and A) such that,
for X >= X0,
    sum ξ in G, abs (physUrem ... (Pd.Gamma ξ) ...
                    (alphaSeq sharedCell) (actualBeta ξ))
        <= C * X / (log X)^A.
```

The proposed statement above is a mathematical contract, not valid Lean syntax and not a theorem already present in the archive.

**Gamma appears once.** It is already inside `physCoefAtom` and `physUrem`. If the proof uses a normalized coefficient and an external `|Gamma|`, prove that equality and do not multiply by Gamma again in the final statement.

## 2. Finite exact adapter

Implement REPORT §§3 and 5 first:

1. `physical_affine_unit_support`: from `WGood`, admissible designated pair, `f = a_j W q0`, and `(f,lr)=1`, derive `(AB,lr)=1`. A need not be a unit modulo f.
2. `urem_eq_relative_discrepancy`: expand the convolution, retain `resMask f c`, and prove (5.1), including all unit indicators and `1 / phi r`.
3. `relative_discrepancy_eq_projection`: prove (3.2) for a common sequence.
4. `relative_projection_energy_le`: prove (3.3), with no extra `phi f` factor.
5. `inverse_residue_map_occupancy`: prove the CRT bijection and the `M/(fl)+1` occupancy bound.
6. `urem_r_sq_le_relative_energy`: use the actual beta L2 norm, not a stronger unneeded pointwise polylog beta bound.
7. `packet_family_cauchy`: prove (5.4) with the reciprocal base norm retained.

These are finite theorems. They do not require an analytic provider and should be kernel-provable independently of the final tail claim.

## 3. Analytic theorem and actual instances

The analytic input is precisely Maynard I, arXiv:2006.06572v2, Lemma 13.8. It requires the full SW and divisor-norm hypotheses and allows fixed divisor weights on the complete modulus. It is not ordinary BV for arbitrary bounded coefficients.

For the paper-level proof, this input is a published theorem. For a provider-free Lean result, it must be imported from a genuinely matching formal theorem or faithfully formalized. Until then, label the Lean result conditional on this published analytic theorem, not on an unknown Urem estimate.

The exact source instances to construct are:

- common `alphaSeq` across packets in one group, after keeping all packet congruences outside alpha;
- rough constant/log/upper-truncated Möbius SW using REPORT §6;
- preservation of coprimality SW under `alpha * 1[(n,r)=1] / tau(r)^J`;
- `sum_m |beta_m|² <= M log^C X` from the existing five-variable divisor bound;
- packet mass `sum_{ξ:fξ=f}|Gamma ξ| <= C tau(f)^K` from the three-state spectator prime assignment count;
- reciprocal packet norm;
- fixed total scalar atom variation, using `H_eq_of_T` before interpreting `total_variation_le` as uniform in X.

Do not impose a new distribution assumption on the actual `alphaSeq` without proving it or explicitly marking its formalization as outstanding.

## 4. Safe fixed parameters

Keep κ fixed with `0 < κ < 1/100000`.
Use the existing actual T choice and critical range.
A conservative base cap compatible with the supplied atom proof is:

```text
epsilon = kappa / 2000
sigma   = kappa / 1000000
```

For `l <= N X^(-kappa)` and `f <= X^sigma`, prove:

```text
2 F L <= 2 N X^(-(kappa-sigma))
M/(F L) >= constant * X^(1/3-sigma),  when M*N is comparable to X.
```

These imply the relative BDH cutoff and occupancy hypotheses eventually at every required fixed log precision. Keep product-scale comparability explicit. Do not use only `N*M <= X` to infer a lower bound for M.

## 5. Compose the family estimate, not the false provider

Normalize coefficients atom by atom, apply the family inequality uniformly, then sum the scalar atom variation and actual group counts. Use `packet_typeII_eq_cells` specialized to the real groups.

The final Urem endpoint should have no argument of type `OrdinaryBVUremProviderScoped`. A temporary imported BDH theorem, if not formalized, must be named as a published-theorem dependency and not concealed in an opaque alias.

This restores the correctly stated Urem step. The next endpoint should expose all remaining independent requirements for the full tail:
- actual critical W4/spectral theorem, with physical base, phase and normalization;
- genuine source routing and prime/prime-power conversions;
- original base-only remainder;
- the constructed positive main-term and seven-block/window framework;
- exact normalization to `N_X I`.

Do not declare Tail287 by using the negated provider, a vacuous class, or a freely enlarged target.

## 6. Validation

Run the grouped-source examples outside sections carrying analytic assumptions. Print both theorem types and axiom dependencies. Report:

1. which old provider dependency was removed;
2. which finite identities are newly kernel-proved;
3. which published analytic facts are formalized and which remain external;
4. whether the new counterexample witness satisfies or violates the actual source hypotheses;
5. the exact strongest unconditional conclusion of the checkout.

Permitted terminal verdicts:
- `UREM FAMILY FORMALLY CLOSED` (all analytic inputs genuinely instantiated in Lean);
- `UREM PAPER REPAIRED; PUBLISHED ANALYTIC FORMALIZATION REMAINS`;
- `ACTUAL SOURCE FIT OPEN`, naming a precise failing condition and its witness.

A full `Tail287` verdict is permitted only if the separate spectral, routing, normalization and seven-block obligations have also been proved.
