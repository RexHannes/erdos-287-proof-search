import RequestProject.Erdos287.ResearchBankV7.IntervalLifting

/-!
# Erdős #287 — Research Bank V7: arithmetic-spine extraction from a supplied certificate

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This module is a theorem **about a supplied certificate**.  It does *not* say — and must not be
read as saying — that every #287 source possesses an interval-lifting certificate or an arithmetic
spine (`spine_existence_not_claimed`).

A `SpineCert` packages:

* an ambient source support `T`;
* the starter positions `starter ⊆ T` with their certified base interval;
* a list of lifting stages (the residue buffers), all inside `T`, valid in the sense of
  `IntervalLifting.ChainValid` — i.e. carrying enough private mass to realize every residue class
  under each stage's cap, which is exactly what preserves every overlap inequality;
* the final lattice step `chainG`, which is `1` (full final denominator `J`) in the intended
  application.

Extracted (all kernel-proved):

* `SpineCert.spine_subset` — the spine is inside the source;
* `SpineCert.spine_reaches` — the certified `J`-lattice interval inclusion;
* `SpineCert.spine_reaches_all` — with final step `1`, every integer of the interval is reached;
* `SpineCert.spine_card_le` and `SpineCert.spine_mass_eq` — the explicit support and mass
  bookkeeping (starter + buffers).
-/

namespace Erdos287
namespace ResearchBankV7
namespace Spine

open Finset IntervalLifting

/-- The chain support stays inside any ambient set containing the starter and all buffers. -/
theorem chainSupport_subset :
    ∀ (L : List Stage) (T amb : Finset ℕ), T ⊆ amb → (∀ st ∈ L, st.buf ⊆ amb) →
      chainSupport T L ⊆ amb := by
  intro L
  induction L with
  | nil => intro T amb h _; simpa [chainSupport] using h
  | cons st rest ih =>
      intro T amb hT hbuf
      refine ih (T ∪ st.buf) amb (Finset.union_subset hT (hbuf st (by simp))) ?_
      intro s hs
      exact hbuf s (by simp [hs])

/-- A supplied, valid interval-lifting certificate inside a source support. -/
structure SpineCert (w : ℕ → ℤ) where
  /-- The ambient source support. -/
  ambient : Finset ℕ
  /-- The starter positions. -/
  starter : Finset ℕ
  /-- The residue-buffer stages. -/
  stages : List Stage
  /-- The initial lattice step. -/
  g0 : ℤ
  /-- The initial lower endpoint. -/
  A0 : ℤ
  /-- The common upper endpoint. -/
  B : ℤ
  /-- The starter is part of the source. -/
  starter_sub : starter ⊆ ambient
  /-- Every buffer is part of the source. -/
  buffers_sub : ∀ st ∈ stages, st.buf ⊆ ambient
  /-- The certified starter interval. -/
  base : ReachesLattice w starter g0 A0 B
  /-- Validity of the whole lifting chain (private mass for every residue class, caps). -/
  valid : ChainValid w starter g0 stages

namespace SpineCert

variable {w : ℕ → ℤ} (c : SpineCert w)

/-- The extracted spine: starter positions together with all residue buffers. -/
def spine : Finset ℕ := chainSupport c.starter c.stages

/-- The final lattice step of the certificate (`1` means the full final denominator `J`). -/
def gFinal : ℤ := chainG c.g0 c.stages

/-- The final lower endpoint (starter endpoint plus one cap per stage). -/
def loFinal : ℤ := chainLo c.A0 c.stages

/-- **The spine sits inside the supplied source.** -/
theorem spine_subset : c.spine ⊆ c.ambient :=
  chainSupport_subset c.stages c.starter c.ambient c.starter_sub c.buffers_sub

/-- **The starter positions are retained by the spine.** -/
theorem starter_subset_spine : c.starter ⊆ c.spine := subset_chainSupport c.stages c.starter

/-- **Certified interval inclusion.**  The spine reaches the whole final lattice interval
`[loFinal, B]`. -/
theorem spine_reaches : ReachesLattice w c.spine c.gFinal c.loFinal c.B :=
  chain_reaches c.stages c.starter c.g0 c.A0 c.base c.valid

/-- **Full `J`-lattice form.**  If the final step is `1` (all directions have been lifted down to
the final denominator `J`), then *every* integer of `[loFinal, B]` is an exact subset weight of
the spine. -/
theorem spine_reaches_all (h1 : c.gFinal = 1) (n : ℤ) (hlo : c.loFinal ≤ n) (hhi : n ≤ c.B) :
    ∃ S ⊆ c.spine, ∑ x ∈ S, w x = n :=
  c.spine_reaches n (by rw [h1]; exact one_dvd n) hlo hhi

/-- **Explicit support bound.**  The spine uses at most the starter positions plus the buffers. -/
theorem spine_card_le :
    c.spine.card ≤ c.starter.card + (c.stages.map (fun st => st.buf.card)).sum :=
  chainSupport_card_le c.stages c.starter

/-- **Explicit mass bookkeeping.**  For any coordinate mass function `f` the spine mass is exactly
the starter mass plus the buffer masses (the buffers are disjoint by certificate validity). -/
theorem spine_mass_eq (f : ℕ → ℚ) :
    ∑ x ∈ c.spine, f x
      = ∑ x ∈ c.starter, f x + (c.stages.map (fun st => ∑ x ∈ st.buf, f x)).sum :=
  chain_mass_eq f c.stages c.starter c.g0 c.valid

/-- The spine mass never exceeds the ambient mass, for a nonnegative mass function. -/
theorem spine_mass_le_ambient (f : ℕ → ℚ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ c.spine, f x ≤ ∑ x ∈ c.ambient, f x :=
  Finset.sum_le_sum_of_subset_of_nonneg c.spine_subset (fun x _ _ => hf x)

end SpineCert

/-! ## Scope firewall -/

/-- **Firewall.**  `SpineCert` theorems are conditional on a *supplied* certificate.  Nothing here
asserts that a given source has one: a universally quantified statement about certificates never
produces a certificate. -/
theorem spine_existence_not_claimed :
    ¬ ∀ (w : ℕ → ℤ) (H : SpineCert w → Prop), (∀ c, H c → H c) → ∃ c : SpineCert w, H c := by
  intro h
  obtain ⟨c, hc⟩ := h (fun _ => 0) (fun _ => False) (fun _ h => h)
  exact hc

end Spine
end ResearchBankV7
end Erdos287
