import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V8 §2J: the certificate source interval

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The exact row-validity interval of owner `Q` at scale `M` is

  `C_Q(M) = [⌈M/(3Q)⌉, ⌊M/Q⌋] ∩ ℤ`.

Kernel-proved (`certInterval_eq_iff`): for `Q ≥ 1` and `1 ≤ a ≤ b`,

  `C_Q(M) = [a, b]`  ⟺  `M ∈ J(Q; a, b)`,

  `J(Q; a, b) = [max{bQ, 3Q(a−1)+1}, min{(b+1)Q−1, 3Qa}] ∩ ℤ`,

and the intersection of several such windows (`mem_all_windows_iff`, `window_inter`).  The
first-forbidden-power constraints and `T(M)² > M` are carried as explicit hypotheses in
`ValidSource` and are never discharged here.
-/

namespace Erdos287
namespace ResearchBankV8
namespace CertificateInterval

/-- `⌈M / (3Q)⌉`. -/
def ceilDiv3 (M Q : ℕ) : ℕ := (M + 3 * Q - 1) / (3 * Q)

/-- The row-validity interval `C_Q(M)`. -/
def certInterval (Q M : ℕ) : Finset ℕ := Finset.Icc (ceilDiv3 M Q) (M / Q)

/-- The lower end of `J(Q; a, b)`. -/
def jLo (Q a b : ℕ) : ℕ := max (b * Q) (3 * Q * (a - 1) + 1)
/-- The upper end of `J(Q; a, b)`. -/
def jHi (Q a b : ℕ) : ℕ := min ((b + 1) * Q - 1) (3 * Q * a)

/-- The source window `J(Q; a, b)`. -/
def window (Q a b : ℕ) : Finset ℕ := Finset.Icc (jLo Q a b) (jHi Q a b)

theorem Icc_eq_Icc_iff {l h a b : ℕ} (hab : a ≤ b) :
    Finset.Icc l h = Finset.Icc a b ↔ l = a ∧ h = b := by
  constructor
  · intro heq
    have ha : a ∈ Finset.Icc l h := heq ▸ Finset.mem_Icc.2 ⟨le_rfl, hab⟩
    have hb : b ∈ Finset.Icc l h := heq ▸ Finset.mem_Icc.2 ⟨hab, le_rfl⟩
    simp only [Finset.mem_Icc] at ha hb
    have hl : l ∈ Finset.Icc a b := heq ▸ Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
    have hh : h ∈ Finset.Icc a b := heq ▸ Finset.mem_Icc.2 ⟨by omega, le_rfl⟩
    simp only [Finset.mem_Icc] at hl hh
    omega
  · rintro ⟨rfl, rfl⟩; rfl

theorem ceilDiv3_eq_iff {M Q a : ℕ} (hQ : 1 ≤ Q) (ha : 1 ≤ a) :
    ceilDiv3 M Q = a ↔ 3 * Q * (a - 1) + 1 ≤ M ∧ M ≤ 3 * Q * a := by
  unfold ceilDiv3
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.div_eq_iff (by omega)]
  have e1 : (a' + 1) * (3 * Q) = 3 * Q * a' + 3 * Q := by ring
  have e2 : 3 * Q * (a' + 1) = 3 * Q * a' + 3 * Q := by ring
  rw [e1, e2]
  generalize 3 * Q * a' = Y
  omega

theorem div_eq_iff' {M Q b : ℕ} (hQ : 1 ≤ Q) : M / Q = b ↔ b * Q ≤ M ∧ M ≤ (b + 1) * Q - 1 := by
  rw [Nat.div_eq_iff (by omega), show (b + 1) * Q = b * Q + Q by ring]

/-- **The certificate source interval.**  `C_Q(M) = [a,b]` iff `M ∈ J(Q; a, b)`. -/
theorem certInterval_eq_iff {Q a b M : ℕ} (hQ : 1 ≤ Q) (ha : 1 ≤ a) (hab : a ≤ b) :
    certInterval Q M = Finset.Icc a b ↔ M ∈ window Q a b := by
  unfold certInterval window jLo jHi
  rw [Icc_eq_Icc_iff hab, ceilDiv3_eq_iff hQ ha, div_eq_iff' hQ, Finset.mem_Icc, max_le_iff,
    le_min_iff]
  tauto

/-- **Intersection of several windows**: `M` lies in every window of a list of requirements
`(Q_i, a_i, b_i)` iff every owner row has exactly the prescribed cofactor interval. -/
theorem mem_all_windows_iff (reqs : List (ℕ × ℕ × ℕ))
    (hreq : ∀ r ∈ reqs, 1 ≤ r.1 ∧ 1 ≤ r.2.1 ∧ r.2.1 ≤ r.2.2) (M : ℕ) :
    (∀ r ∈ reqs, M ∈ window r.1 r.2.1 r.2.2) ↔
      ∀ r ∈ reqs, certInterval r.1 M = Finset.Icc r.2.1 r.2.2 := by
  apply forall₂_congr
  intro r hr
  obtain ⟨h1, h2, h3⟩ := hreq r hr
  exact (certInterval_eq_iff h1 h2 h3).symm

/-- Two windows intersect in an explicit interval. -/
theorem window_inter (Q₁ a₁ b₁ Q₂ a₂ b₂ : ℕ) :
    window Q₁ a₁ b₁ ∩ window Q₂ a₂ b₂ =
      Finset.Icc (max (jLo Q₁ a₁ b₁) (jLo Q₂ a₂ b₂)) (min (jHi Q₁ a₁ b₁) (jHi Q₂ a₂ b₂)) := by
  unfold window
  ext M
  simp only [Finset.mem_inter, Finset.mem_Icc, max_le_iff, le_min_iff]
  tauto

/-- A valid certificate source: the window condition **plus** the explicit, undischarged
hypotheses (first-forbidden-power constraints and `T(M)² > M`). -/
structure ValidSource (Q a b M : ℕ) (FirstForbiddenPower : ℕ → Prop) (T : ℕ → ℕ) : Prop where
  /-- The window condition. -/
  inWindow : M ∈ window Q a b
  /-- The first-forbidden-power constraint (explicit hypothesis). -/
  firstForbidden : FirstForbiddenPower M
  /-- The cutoff condition `T(M)² > M` (explicit hypothesis). -/
  cutoffSq : M < T M ^ 2

/-- A valid source has the prescribed complete cofactor interval. -/
theorem ValidSource.certInterval_eq {Q a b M : ℕ} {FFP : ℕ → Prop} {T : ℕ → ℕ}
    (h : ValidSource Q a b M FFP T) (hQ : 1 ≤ Q) (ha : 1 ≤ a) (hab : a ≤ b) :
    certInterval Q M = Finset.Icc a b :=
  (certInterval_eq_iff hQ ha hab).2 h.inWindow

/-- A concrete sanity check: `Q = 10`, `[a,b] = [3,5]` gives `J = [61, 59]`, empty, while
`[a,b] = [2,5]` gives `J = [50, 59]`; e.g. `C_{10}(55) = [2, 5]`. -/
theorem window_examples :
    window 10 3 5 = ∅ ∧ window 10 2 5 = Finset.Icc 50 59 ∧
    certInterval 10 55 = Finset.Icc 2 5 := by
  refine ⟨by decide, by decide, by decide⟩

end CertificateInterval
end ResearchBankV8
end Erdos287
