import RequestProject.Erdos287.ResearchBankV13.PrimeCertificates

/-!
# Erdős #287 — Research Bank V13 §22: the generic finite interval certificate

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

**Proof-carrying format.**
* `FiniteIntervalStep` — `lower`, `upper` and a proof that every endpoint in `[lower, upper]` is
  excluded;
* `Chain lo steps hi` — contiguity: each step starts at or below the first not-yet-covered
  endpoint, and the steps reach `hi`;
* `FiniteIntervalCertificate` — `first`, `last`, `steps`, `contiguous`, `initialCoverage`
  (all endpoints `< first` excluded), `finalEndpoint` (the last step ends at `last`);
* **`FiniteIntervalCertificate.sound`**: a certificate gives `NoCounterexampleUpTo last`.

**Data-level format with a Lean-verified checker.**
* `IntervalRecord` — numbers only: `c ∈ {2, 4}`, a Proth witness `(u, n, a)` for
  `q = u·2ⁿ + 1`, and a Pocklington witness `(b, f)` for `p = c·q + 1`;
* `IntervalRecord.check : Bool` and `IntervalRecord.sound`: a passing record excludes every
  endpoint in `[p − 1, ⌊(685/252) p⌋]` (Family A for `c = 2`, Family B for `c = 4`);
* `checkChain lo recs hi : Bool` and **`checkChain_sound`**: a passing record list excludes every
  endpoint in `[lo, hi]`;
* `certificateOfRecords` — turns a passing record list plus an initial coverage theorem into a
  `FiniteIntervalCertificate`.

Regression fixture 10 (`noncontiguous_rejected`): a list of two individually valid steps with a
gap fails the certificate interface.

The generic format is proved sound here.  **This file imports no concrete 10^500 payload.**
-/

namespace Erdos287
namespace ResearchBankV13
namespace IntervalCertificate

open FiniteRepresentationModel HarmonicTwoHole PrimeCertificates

/-- A proof-carrying interval step. -/
structure FiniteIntervalStep where
  lower : ℕ
  upper : ℕ
  proofExcluded : ∀ M, lower ≤ M → M ≤ upper → NoCounterexampleAt M

/-- Contiguity: `lo` is the first endpoint not yet covered. -/
def Chain : ℕ → List FiniteIntervalStep → ℕ → Prop
  | lo, [], hi => hi < lo
  | lo, s :: rest, hi => s.lower ≤ lo ∧ Chain (s.upper + 1) rest hi

/-- **Chains cover their interval.** -/
theorem Chain.covers : ∀ (steps : List FiniteIntervalStep) (lo hi : ℕ), Chain lo steps hi →
    ∀ M, lo ≤ M → M ≤ hi → NoCounterexampleAt M
  | [], lo, hi, h, M, h1, h2 => absurd (lt_of_le_of_lt (le_trans h1 h2) h) (lt_irrefl _)
  | s :: rest, lo, hi, ⟨hs, hrest⟩, M, h1, h2 => by
    by_cases hM : M ≤ s.upper
    · exact s.proofExcluded M (le_trans hs h1) hM
    · exact Chain.covers rest (s.upper + 1) hi hrest M (by omega) h2

/-- **The finite interval certificate.** -/
structure FiniteIntervalCertificate where
  first : ℕ
  last : ℕ
  steps : List FiniteIntervalStep
  contiguous : Chain first steps last
  initialCoverage : ∀ M < first, NoCounterexampleAt M
  finalEndpoint : ∀ s ∈ steps.getLast?, s.upper = last

/-- **Generic soundness**: `FiniteIntervalCertificate → NoCounterexampleUpTo last`. -/
theorem FiniteIntervalCertificate.sound (C : FiniteIntervalCertificate) :
    NoCounterexampleUpTo C.last := by
  intro M hM
  by_cases h : M < C.first
  · exact C.initialCoverage M h
  · exact Chain.covers C.steps C.first C.last C.contiguous M (by omega) hM

/-! ## Data-level records and the verified checker -/

/-- A numeric interval record. -/
structure IntervalRecord where
  c : ℕ
  u : ℕ
  n : ℕ
  a : ℕ
  b : ℕ
  f : ℕ
  deriving Repr

namespace IntervalRecord

variable (r : IntervalRecord)

/-- `q = u 2ⁿ + 1`. -/
def q : ℕ := r.u * 2 ^ r.n + 1

/-- `p = c q + 1`. -/
def p : ℕ := r.c * r.q + 1

/-- The record check. -/
def check : Bool :=
  prothCheck r.u r.n r.a && pocklingtonCheck r.c r.q r.b r.f &&
    ((decide (r.c = 2) && decide (137 < r.q)) || (decide (r.c = 4) && decide (7381 < r.q)))

/-- **Record soundness**: a passing record excludes `[p − 1, ⌊η p⌋]`. -/
theorem sound (h : r.check = true) :
    ∀ M, r.p - 1 ≤ M → M ≤ etaFloor r.p → NoCounterexampleAt M := by
  simp only [check, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hP, hK⟩, hfam⟩ := h
  have hq : r.q.Prime := prothCheck_sound hP
  have hp : r.p.Prime := pocklingtonCheck_sound hq hK
  rcases hfam with ⟨hc, hq137⟩ | ⟨hc, hq7381⟩
  · exact AdjacentPrimeLayer.familyA_interval hp hq (by unfold p; rw [hc]) hq137
  · exact AdjacentPrimeLayer.familyB_interval hp hq (by unfold p; rw [hc]) hq7381

/-- The proof-carrying step of a passing record. -/
def toStep (h : r.check = true) : FiniteIntervalStep := ⟨r.p - 1, etaFloor r.p, r.sound h⟩

end IntervalRecord

/-- The chain checker for record lists. -/
def checkChain : ℕ → List IntervalRecord → ℕ → Bool
  | lo, [], hi => decide (hi < lo)
  | lo, r :: rest, hi => r.check && decide (r.p - 1 ≤ lo) && checkChain (etaFloor r.p + 1) rest hi

/-- **Checker soundness.** -/
theorem checkChain_sound : ∀ (recs : List IntervalRecord) (lo hi : ℕ),
    checkChain lo recs hi = true → ∀ M, lo ≤ M → M ≤ hi → NoCounterexampleAt M
  | [], lo, hi, h, M, h1, h2 => by
    simp only [checkChain, decide_eq_true_eq] at h; omega
  | r :: rest, lo, hi, h, M, h1, h2 => by
    simp only [checkChain, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hr, hlo⟩, hrest⟩ := h
    by_cases hM : M ≤ etaFloor r.p
    · exact r.sound hr M (by omega) hM
    · exact checkChain_sound rest _ hi hrest M (by omega) h2

/-- The last endpoint reached by a record list starting at `lo`. -/
def reach : ℕ → List IntervalRecord → ℕ
  | lo, [] => lo - 1
  | _, r :: rest => reach (etaFloor r.p + 1) rest

/-- **From records to a certificate**: a passing record list starting at `first`, together with
an initial coverage theorem for all endpoints `< first`, gives `NoCounterexampleUpTo hi`. -/
theorem noCounterexampleUpTo_of_records {first hi : ℕ} {recs : List IntervalRecord}
    (hinit : ∀ M < first, NoCounterexampleAt M) (h : checkChain first recs hi = true) :
    NoCounterexampleUpTo hi := by
  intro M hM
  by_cases h' : M < first
  · exact hinit M h'
  · exact checkChain_sound recs first hi h M (by omega) hM

/-- **A passing record list as a `FiniteIntervalCertificate`** (one proof-carrying step
`[first, hi]` obtained from `checkChain_sound`). -/
def certificateOfRecords (first hi : ℕ) (recs : List IntervalRecord)
    (hinit : ∀ M < first, NoCounterexampleAt M) (h : checkChain first recs hi = true) :
    FiniteIntervalCertificate where
  first := first
  last := hi
  steps := [⟨first, hi, checkChain_sound recs first hi h⟩]
  contiguous := ⟨le_rfl, Nat.lt_succ_self hi⟩
  initialCoverage := hinit
  finalEndpoint := by simp

/-- Initial coverage from the project's unconditional range `M ≤ 4·10^9`. -/
theorem initialCoverage_4e9 : ∀ M < 4000000001, NoCounterexampleAt M :=
  fun M hM => noCounterexampleUpTo_4e9 M (by omega)

/-- The certificate built from records (with the `4·10^9` initial coverage and the empty step
list): `NoCounterexampleUpTo 4·10^9` as a `FiniteIntervalCertificate`. -/
def baseCertificate : FiniteIntervalCertificate where
  first := 4000000001
  last := 4000000000
  steps := []
  contiguous := by show 4000000000 < 4000000001; omega
  initialCoverage := initialCoverage_4e9
  finalEndpoint := by simp

/-! ## Regression fixture 10 -/

/-- Two individually valid steps (from the `4·10^9` range) with a gap at `6`. -/
def gapStep1 : FiniteIntervalStep :=
  ⟨0, 5, fun M _ h2 => noCounterexampleUpTo_4e9 M (by omega)⟩

def gapStep2 : FiniteIntervalStep :=
  ⟨7, 10, fun M _ h2 => noCounterexampleUpTo_4e9 M (by omega)⟩

/-- **A non-contiguous interval list fails the certificate interface.** -/
theorem noncontiguous_rejected : ¬ Chain 0 [gapStep1, gapStep2] 10 := by
  simp only [Chain, gapStep1, gapStep2]
  omega

/-- The data-level checker also rejects a gap: a record whose `p − 1` exceeds the running
lower bound fails. -/
theorem checkChain_rejects_gap (r : IntervalRecord) (lo hi : ℕ) (hgap : lo < r.p - 1) :
    checkChain lo [r] hi = false := by
  simp only [checkChain, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le]
  exact Or.inl (Or.inr hgap)

end IntervalCertificate
end ResearchBankV13
end Erdos287
