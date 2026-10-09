# Aristotle implementation handoff — two proven-mathematics interfaces pending kernel proofs

Use the newest checkout, **not** the older user-supplied tar archive. Preserve `prop52_nat`, `ellX_tensor`, `physCoefAtom_reassemble`, `typeII_source_decomp`, `physOB_source_eq_T`, and all previously proved declarations.

## Proof dependency graph

```
kappa_sector (low Dplus if J even; low Dminus if J odd)
      + BoxAdm -> boxVec_vecHyp
      + high/low disjoint prime sets
      + sorted high tuple <= sorted upper endpoint vector
          | 
          v
actual_modulus_Dplus_Dtot
          |
          v
actual_modulus_Dplus_pascadi
          |
          +-> prop52_nat (integer support path; DO NOT use its per-d colour
          |                choice as a global factorized coefficient)
          |
          v
preserve atomColour (fixed over each box)
          + ellX_tensor + physCoefAtom_reassemble
          + typeII_source_decomp + physOB_source_eq_T
          |
          v
source-exact coefficient/range dictionary (still requires kernel proof)
          |
          v
actual growing-base/spectral provider (NOT supplied by Prop 4.4)
```

Parameter path, with δ=κ, `T>100/κ`, `0<κ<10^-5` and critical `X^(3κ)<=N<=X^(1/3+κ/2)`:

```
beta_eq -> beta_lt_kappa_div_100 -> Dlow_sq_le
           |                       |
           +-> atom_Nlo             |
           +-> atom_Nhi             |
           +------------> AtomParams S κ N
                                + Dlow_sq_le
                                  |
                                  v
                         atom_factorization_clean
                                  |
                                  v
                 Sys53 at margin κ/2
                                  |
                                  v
                 Prop 4.4 range margin ε=κ/2000
```

## Requested kernel theorem shapes

Exact names/types should be adapted to imports, but retain original source predicates.

```lean
-- Intended declaration (not yet compiled):
-- theorem actual_modulus_Dplus_Dtot (hS : S.Good)
--   {J : ℕ} {P : Fin J → Fin S.H} (hP : S.BoxAdm J P)
--   {b : ℕ} (hb : S.kappa J b ≠ 0)
--   {q : Fin J → ℕ} (hq : q ∈ S.tuples J P) :
--   Factor.InDplus S.Dtot (b * ∏ i, q i) := by ...
--
-- theorem actual_modulus_Dplus_pascadi
--   (hS : S.Good) (hκ0 : 0 < κ) (hκ1 : κ < 1/100000)
--   (hP : S.BoxAdm J P) (hb : S.kappa J b ≠ 0)
--   (hq : q ∈ S.tuples J P) :
--   Factor.InDplus (S.X ^ (3/5 - 50*κ)) (b * ∏ i, q i) := by ...
--
-- theorem actual_atom_params_closed
--   (hS : S.Good) (hκ0 : 0 < κ) (hκ1 : κ < 1/100000)
--   (hT : 100 / κ < (S.T : ℝ))
--   (hNlo : S.X ^ (3*κ) ≤ N)
--   (hNhi : N ≤ S.X ^ (1/3+κ/2)) :
--   AtomParams S κ N ∧ S.Dlow ^ 2 ≤ S.X ^ (κ/2) := by ...
```

The comments are theorem contracts, **not** compiled declarations or claimed proofs. Build and `#print axioms` after proof construction. Do not turn the ellipses into `sorry` or new axioms.

## Critical downstream audit

- `Dplus` is a sufficient condition for *existence of a legal factor allocation*. A per-modulus arbitrary factor choice must not replace box-fixed atom colouring.
- Pascadi Prop 4.4 has fixed integer residue `a` and requires one-bounded independent coefficients, roughness, SW, and its exact length inequalities. The growing actual base `f` is a separate theorem; do not smuggle it through the proposition.
- If the only downstream use of actual `Dplus` was Prop 5.2, the previously established box-endpoint constructive allocation plus `atom_factorization_clean` can already satisfy that particular input; an actual-modulus membership theorem is valuable formal reinforcement, **not automatically a necessary extra obstruction**.
- `no_ce_of_finite_and_hinge` must list uniform positivity and finite certificate as hypotheses; a kernel proof of the implication alone is not global Erdős #287.

## Uniformity check

Prove that `S.H` depends only on fixed `T` (not on growing `X`): `boxEnd j <= sqrt Dint` iff `eps0^2*(1+tau)^j <= 1/2`. Otherwise the formally bounded variation `∑ H^J 3^J` has not yet been shown uniform in the asymptotic scale.

## Required status return

1. Exact theorem signatures and `#print axioms` for the two new source lemmas.
2. `lake build RequestProject.Erdos287.SourceChain.Physical` on the current checkout.
3. `lake build RequestProject.Erdos287.Effective.Audit` and lcm universal bound status.
4. Full physical Tail287 dependency graph, identifying every still-open deep analytic input and any source gap.
5. `FACTORIZATION CLOSED` only if the actual source-to-provider dictionary is proved; otherwise `PARTIAL CONSTRUCTION`.
