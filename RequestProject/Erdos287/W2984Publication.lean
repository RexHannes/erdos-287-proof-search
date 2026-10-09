import RequestProject.Erdos287.W2984Publication.AxiomAudit

/-! # Erdős #287 — W2.984 publication subtree (aggregator).  **ERDŐS #287 REMAINS OPEN.**

Namespace `Erdos287.W2984Publication`.  Imports the W3 publication checkpoint
(`Erdos287.W3Publication`) and adds only what is new between W3 and W2.984:

* `ScalarFunctions`, `ScalarOmega`, `ScalarCertificate` — Merikoski's `Ω₁, Ω₂, Ω₃` at
  `α = 1/7`, `β = 3/14` and the kernel-checked certificate `Ω₁ - Ω₂ + Ω₃ ≤ 3.983412536315 < 3.984`;
* `ChenDecomposition` — the (repaired) affine Chen decomposition, with the kernel-checked
  counterexample to the literal pointwise inequality in Merikoski's proof of Lemma 13;
* `AffineCRT` — the literal congruence transfer for `L_i(t) = a_i t + 1`;
* `ModulusLedger` — the complete modulus ledger;
* `Providers` — the W3 framework (pair constant free) and the four narrow Chen providers;
* `MainTheorem` — `W2984` (conditional, asymptotic, ineffective) and W3 recovered;
* `RegressionSuite`, `AxiomAudit`.

Written proof: `AFFINE_CHEN_TRANSFER_W2984.md`.  Report: `W2984_FORMALIZATION_REPORT.md`. -/
