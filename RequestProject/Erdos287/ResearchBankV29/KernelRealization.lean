import RequestProject.Erdos287.ResearchBankV29.DIClassRealization

/-!
# Erdős #287 — Research Bank V29 §5: physical smooth source → kernel (audit)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

## Audit finding

The only smooth-cutoff objects in V27 (`SmoothFrequencyRecovery`) are an ABSTRACT Fourier profile
`psiHat : ℝ → ℝ` and an abstract weight sequence `b : ℕ → ℝ`, constrained only through the
providers `SchwartzFrequencyProvider`, `FrequencyCapProvider`, `SmoothRecoveryProvider`.  No
physical cutoff `ψ` (support, normalization, smoothness class) is defined, and the kernel `Kl` of a
`KloostermanData` is an arbitrary function `B → Z → ℂ`.  Hence `realize_clean_kernel :
PhysicalCleanState → DIKernel` cannot be constructed from the bank without inventing the DI kernel
formula, which task §24 forbids.

**Proved here (FINITE REGRESSION / LEAN BANK):**
* `zeroKernelForm_DI` — the form with kernel `0` (same numeric data as the degenerate form)
  satisfies the DI conclusion;
* `kernel_is_load_bearing` — two Kloosterman forms with IDENTICAL numeric parameters
  `Q,R,S,N,d,x,ε_DI,Ξ,mass,Rep,N_q,T,Δ₂,Δ₃` and identical off-diagonal set differ in the DI
  conclusion.  So membership in any correct DI class depends on the kernel itself, which must be
  constructed from the physical cutoff: the numeric parameters do not suffice.
-/

namespace Erdos287
namespace ResearchBankV29
namespace KernelRealization

open ResearchBankV27.DISpectral

/-- The degenerate form with the kernel replaced by `0`. -/
noncomputable def zeroKernelForm (η : ℝ) : KloostermanData :=
  { degenerateForm η with Kl := fun _ _ => 0 }

/-- **The zero-kernel form satisfies the DI conclusion** (LEAN BANK). -/
theorem zeroKernelForm_DI (η : ℝ) : DIConclusion (zeroKernelForm η) := by
  refine ⟨by simp [zeroKernelForm, degenerateForm], fun c _ => ?_, ?_⟩
  · simp [bilinear, zeroKernelForm, degenerateForm]
  · simp [zeroKernelForm, degenerateForm]

/-- **The kernel is load-bearing** (FINITE REGRESSION): same numeric data, different DI verdict. -/
theorem kernel_is_load_bearing (η : ℝ) :
    (zeroKernelForm η).Q = (degenerateForm η).Q ∧ (zeroKernelForm η).R = (degenerateForm η).R ∧
    (zeroKernelForm η).S = (degenerateForm η).S ∧ (zeroKernelForm η).N = (degenerateForm η).N ∧
    (zeroKernelForm η).d = (degenerateForm η).d ∧ (zeroKernelForm η).x = (degenerateForm η).x ∧
    (zeroKernelForm η).epsDI = (degenerateForm η).epsDI ∧
    (zeroKernelForm η).Xi = (degenerateForm η).Xi ∧
    (zeroKernelForm η).Nq = (degenerateForm η).Nq ∧ (zeroKernelForm η).T = (degenerateForm η).T ∧
    DIConclusion (zeroKernelForm η) ∧ ¬ DIConclusion (degenerateForm η) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, zeroKernelForm_DI η, degenerateForm_not_DI η⟩

end KernelRealization
end ResearchBankV29
end Erdos287
