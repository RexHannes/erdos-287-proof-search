# Formal Module Map and Scope Firewall

The full Lean project remains in the supplied Aristotle bank. This file records the modules directly used by the R12 manuscript and the exact scope attributed to them. A module name does not imply that every analytic continuation, limiting operation, or numerical instantiation appearing nearby is formalised.

| Module | Principal content retained in R12 | Status/scope |
|---|---|---|
| `RequestProject/Erdos287/BsrcWeights.lean` | `B_0`, `beta`, physical `B_src`, typed multiplicativity, single-global-factor firewall | **KERNEL-PROVED**, finite prime factors |
| `RequestProject/Erdos287/SourceWeights.lean` | `lambda`, local Möbius relation, physical collapse, `q=15` regression | **KERNEL-PROVED**, odd squarefree finite source |
| `RequestProject/Erdos287/AllComplement.lean` | all-complement divisor identity | **KERNEL-PROVED**, finite divisor sums |
| `RequestProject/Erdos287/OddHalfDivisor.lean` | odd half-divisor substitution and `w=6` parity firewall | **KERNEL-PROVED**, finite/source algebra |
| `RequestProject/Erdos287/Reflection.lean` | strict and non-strict odd-radical reflection | **KERNEL-PROVED**, finite divisors |
| `RequestProject/Erdos287/MediumLedger.lean` | full-versus-medium typing and no-double-count firewall | **KERNEL-PROVED**, bookkeeping |
| `RequestProject/Erdos287/C1C2Splice.lean` | discrete splice and continuous change of variables | **KERNEL-PROVED**, with stated integrability input |
| `RequestProject/Erdos287/OddLineCancellation.lean` | full odd discrete cancellation and coefficient convolution | **KERNEL-PROVED** finite identity; infinite use **CONDITIONAL** |
| `RequestProject/Erdos287/RatioBoundary.lean` | exact ratio-boundary compiler | **KERNEL-PROVED** as implication; analytic inputs **CONDITIONAL** |
| `RequestProject/Erdos287/EulerLocal.lean` | local Euler factors and finite companion identities | **KERNEL-PROVED** |
| `RequestProject/Erdos287/TwoVariableZ.lean` | two-variable local identity and finite `Z_P(s,s)=0` | **KERNEL-PROVED**, finite prime set |
| `RequestProject/Erdos287/PerronAlgebra.lean` | `(s,z)<->(u,v)`, determinant, Jacobian, kernel compensation | **KERNEL-PROVED**, algebra only; contour theorem **CONDITIONAL** |
| `RequestProject/Erdos287/CompletePeriodEndpoint.lean` | complete-period covariance, coprime orthogonality, positivity, lane invariance | **KERNEL-PROVED**, exact residue sums |
| `RequestProject/Erdos287/IncrementalDirectedLedger.lean` | earlier exact ledger arithmetic and typed retention | **KERNEL-PROVED**, historical snapshot |

## Signed-floor structural modules

The following 4 September modules support the structural signed-floor bank:

- `Erdos287September4PhysicalW.lean`
- `Erdos287September4CanonicalStateSign.lean`
- `Erdos287September4T0T2DeepEvenCancellation.lean`
- `Erdos287September4BoundaryDivisorLattice.lean`
- `Erdos287September4BoundaryCertificateChecker.lean`
- `Erdos287September4LargeLTailCompiler.lean`
- `Erdos287September4SignedBsrcCompiler.lean`
- `Erdos287September4BsrcLocalMobiusCollapse.lean`

They formalise the weight, canonical sign, deep-even cancellation, boundary-event datatype/checker, budget compiler, and tail envelope at their displayed finite or conditional interfaces. The bank records no populated physical event-box certificate. Therefore signed-floor closure is **OPEN**, not kernel-proved.

## Prohibited inference upgrades

The following upgrades are invalid unless a later bank supplies the missing theorem:

1. finite Euler identity `=>` infinite Euler product without convergence;
2. algebraic Perron change of variables `=>` a valid shifted contour with controlled tails;
3. finite complete-period covariance `=>` finite-period joined covariance;
4. a checker for boundary certificates `=>` existence of a populated physical certificate;
5. a conditional compiler `=>` an inhabitant of its analytic input;
6. exact ledger arithmetic `=>` proof that the uninstantiated charge satisfies the ledger.
