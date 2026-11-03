# ARISTOTLE / LEAN 4 — ERDŐS #287 FRONTIER CONTINUATION

## Mission: Extend the Existing Kernel-Proved Aristotle Bank to Gold God 4.1

Continue from my existing Aristotle Erdős #287 Lean work. **Reuse and preserve all genuinely proved results. Do not restart from scratch or claim the main Erdős conjecture has been solved.**

### 1. Restore existing formalization

Locate the latest working Aristotle repository and relevant prior files, including where available:

- `RequestProject/Erdos287/ConsecutiveReciprocals.lean`
- `RequestProject/Erdos287/PrimeAdic.lean`
- `RequestProject/Erdos287/SupplyReduction.lean`
- `erdos287_low_height_20261031.lean`
- `erdos287_positional_windows_20261101.lean`
- `erdos287_effectivity_20261101.lean`

Use the attached Gold God 4.1 Positional–Arithmetic Incompatibility manuscript as the new mathematical specification.

First inventory actual declarations, imports, Lean version, Mathlib version, compilation results and axiom dependencies.

Some legacy files use Lean 4.19 with `Std`; other repositories may use different pinned Mathlib versions. Port only when necessary. Never silently mix incompatible toolchains.

### 2. Formalize the authentic source

Define a finite selected set (A\subseteq{2,\ldots,M}) with

[\
\sum\_{n\in A}1/n=1,\qquad M=\max A.\
]

Formalize its actual Boolean indicators (x_n), minimum and maximum, and Gap-two condition.

For each prime (q), define its COMPLETE row:

[\
S_q=\sum\_{\substack{n\in A\q\mid n}}\frac1n\
\=\frac{a_q}{b_q}\
]

in lowest terms.

Prove exact bridges from finite reciprocal sums to prime-power integrality and the existing Aristotle primary-carry lemmas.

All subsequent statements must use these literal source definitions, not unconstrained proxy variables.

### 3. Highest-priority new local theorems

Prove without new axioms:

**A. Upper-half prime exclusion**

For prime (M/2\<p\<M), show (x_p=0).

**B. Forced neighbors**

Under Gap-two, derive the required internal neighbor selections, including (x\_{p-1}=x\_{p+1}=1).

**C. Four-value retained-cofactor lemma**

Assume (p=2qr-1) is prime, (2qr\in A), and the manuscript's exact size and primality conditions hold.

Prove:

[\
6qrS_q\equiv3+6x\_{qr}+2x\_{3qr}\pmod r,\
]

with possible residues (3,5,9,11), and

[\
v_r(b_q)=1.\
]

Treat modular congruences of rationals correctly through localization, p-adic valuation or invertible denominators. Do not incorrectly treat an arbitrary rational expression as an integer residue.

**D. Cleaning obstruction**

Show that if the final reduced q-row denominators exclude every prime in the forced cofactor interval, then the corresponding forced neighbor cannot be selected.

Prove the applicable conditional gap-counting conclusion.

### 4. Formalize the global Chen alternative

Target:

[\
G_M(A)+E\_\eta(A)\ge cM/(\log M)^2.\
]

Separate its ingredients carefully:

1. Published Friedlander–Luca–Stoiciu Chen-prime supply.
2. Uniform balanced-semiprime upper-sieve estimate.
3. Finite logical classification of the surviving prime neighbors.
4. Exact row-residue consequences.

Fully prove the finite and algebraic steps.

If the published analytic theorem or the sieve bound is not yet available in Lean, introduce it ONLY as an explicit hypothesis of a conditional theorem. Do not use a global axiom, an uninhabited provider disguised as a proof, or silently import a manuscript assertion.

Check and repair the Selberg proof's (ab\<z) support issue, investigating (y=\sqrt z/2). If the proposed repair fails, report the actual obstruction.

### 5. Extend toward the latest frontier

Formalize complete shared prime-power carry equations, the same-indicator coupling across rows, and two-sided prime-neighbor forcing wherever genuinely provable.

Represent the unresolved global retained-residue compatibility statement precisely.

Investigate whether any further mathematical incompatibility can actually be proved. If not, preserve it as an OPEN obligation, not an axiom.

### 6. Trust and verification

Requirements:

- No `sorry`, `admit`, custom `axiom`, `native_decide`, `implemented_by`, opaque oracle or fabricated theorem.
- Preserve existing kernel-proved declarations.
- Run `lake build` against the pinned project.
- Run `#print axioms` on each principal theorem.
- Distinguish unconditional proofs from implications requiring explicit analytic hypotheses.
- Verify exact quantifiers and theorem statements against the manuscript.
- If a claim is false, give a counterexample or corrected statement; never silently weaken it.

### 7. Deliverables

Return updated Lean source files, compilation results, an axiom/dependency audit, and an OPEN_FRONTIER document.

Classify each principal claim as:

**KERNEL PROVED / CONDITIONAL ON NAMED HYPOTHESES / NOT FORMALIZED / FALSE OR REQUIRES REPAIR.**

Complete the highest-priority local proofs first. Then advance toward the global Chen alternative and retained-residue frontier as far as rigorous formalization permits.

The final Erdős #287 conjecture must remain OPEN unless an unconditional complete proof has genuinely been found and kernel-checked.
