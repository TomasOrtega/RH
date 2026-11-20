import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzRapidDecayColumnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSmoothKernelRepresentationStatement

open Classical MeasureTheory NumberField

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

/- English proof (translation)
Introduce `E _ _ _ a π`. Use `sInf_le ⟨fun φ hφ => mem_rspan hφ, fun F hF h => rt_mem_rspan hF h, fun F hF f hf => ?_, fun F hF r f => ?_⟩` and prove the remaining obligations. Take `⟨hk, he⟩` from `GlobalTheory.T.archimedean_smooth_kernel_representation f hf`. Rewrite using `[he F]`. Conclude with `kerInf_mem_rspan hF _ hk`.

Establish `e : colConv r f F = kerInf (volume : Measure (Fin a → Cinf E)) (fun x => f x) (colU r) F` using `rfl`. Rewrite using `[e]`. Conclude with `kerInf_mem_rspan hF _ (GlobalTheory.T.schwartz_rapid_decay_column r f)`.
-/
theorem mspan_le_rspan : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (π : GlobalTheory.CuspRep.CuspSub E a), GlobalTheory.JSW.mspan π ≤ GlobalTheory.JSW.rspan π := by
  intro E _ _ _ a π
  refine sInf_le ⟨fun φ hφ => mem_rspan hφ, fun F hF h => rt_mem_rspan hF h, fun F hF f hf => ?_,
    fun F hF r f => ?_⟩
  · obtain ⟨hk, he⟩ := GlobalTheory.T.archimedean_smooth_kernel_representation f hf
    rw [he F]
    exact kerInf_mem_rspan hF _ hk
  · have e : colConv r f F = kerInf (volume : Measure (Fin a → Cinf E)) (fun x => f x) (colU r) F := rfl
    rw [e]
    exact kerInf_mem_rspan hF _ (GlobalTheory.T.schwartz_rapid_decay_column r f)

end GlobalTheory.JSW
