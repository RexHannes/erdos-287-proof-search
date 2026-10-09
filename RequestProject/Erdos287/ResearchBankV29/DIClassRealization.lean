import RequestProject.Erdos287.ResearchBankV29.PhysicalCleanState

/-!
# Erdős #287 — Research Bank V29 §4: DIClass membership (audit, STOP point)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

In V27/V28 `DIClass : KloostermanData → Prop` is a **free parameter** of
`DISpectralProvider`, `CleanAdmissible`, `NonzeroCleanRealization` and `FinalAnalyticProviders`.
It is never defined.  The following facts (all LEAN BANK / FINITE REGRESSION) show that the V28
typing does not determine it, so `actual_clean_state_mem_DIClass` cannot be proved in this bank:

* `di_provider_empty_class` — with `DIClass := False` the DI provider holds trivially;
* `di_provider_full_class_false` — with `DIClass := True` it is false (V27 regression, restated);
* `DIClass_underdetermined` — both at once: the same V28 type admits a vacuous and a false reading;
* `cleanAdmissible_empty_class` — with `DIClass := False` no clean state is admissible, so the
  V27 clean-nonzero theorem is then applicable only to EMPTY clean families.

**Earliest remaining composition hole (task §4 STOP):** `ActualCleanStateMemDIClass` below — for
the (non-existent) physical clean states of the nonzero branch, membership `DIClass s.DD.KD` for a
DIClass that is (a) the literal public DI class and (b) contains those states.  Neither (a) a
definition of that class nor (b) a physical clean-state generator exists in V2–V28.
-/

namespace Erdos287
namespace ResearchBankV29
namespace DIClassRealization

open ResearchBankV27.DISpectral ResearchBankV27.CleanNonzero

/-- **Vacuous DI class** (LEAN BANK). -/
theorem di_provider_empty_class (η : ℝ) : DISpectralProvider η (fun _ => False) :=
  ⟨fun _ h _ => h.elim⟩

/-- **Unrestricted DI class is false** (FINITE REGRESSION, V27 restated). -/
theorem di_provider_full_class_false (η : ℝ) : ¬ DISpectralProvider η (fun _ => True) :=
  unrestricted_provider_false η

/-- **`DIClass` is underdetermined by the V28 typing** (LEAN BANK). -/
theorem DIClass_underdetermined (η : ℝ) :
    DISpectralProvider η (fun _ => False) ∧ ¬ DISpectralProvider η (fun _ => True) :=
  ⟨di_provider_empty_class η, di_provider_full_class_false η⟩

/-- With the vacuous class no clean state is admissible (LEAN BANK). -/
theorem cleanAdmissible_empty_class {η x : ℝ} (s : CleanState x) :
    ¬ CleanAdmissible (fun _ => False) η s := fun h => h.1

/-- **The earliest remaining composition hole** (named statement; NOT proved, NOT assumed by any
V29 theorem except through the explicitly labelled internal glue owner of `ProviderElimination`):
every clean state produced by a physical realization `gen` lies in `DIClass`. -/
def ActualCleanStateMemDIClass (DIClass : KloostermanData → Prop) {β : Type} {x : ℝ}
    (gen : β → CleanState x) : Prop :=
  ∀ b, DIClass (gen b).DD.KD

end DIClassRealization
end ResearchBankV29
end Erdos287
