import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFiniteFormsGLSpanKilledScalarDeriva
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemExpSolCons
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HCF.span_formsGL_killed_scalD` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHarishChandraFiniteFormsGLSpanKilledScalarDeriva.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.harishChandraFiniteFormsGL_span_killed_scalarDerivative : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
    (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)), X.Finite → ∀ N : ℕ,
    ∃ Λ : List ℂ, ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N),
      (Λ.map fun c => scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c).prod φ = 0 := by
  first | exact @GlobalTheory.HCF.span_formsGL_killed_scalD | exact GlobalTheory.HCF.span_formsGL_killed_scalD | (intros; apply GlobalTheory.HCF.span_formsGL_killed_scalD <;> assumption)
