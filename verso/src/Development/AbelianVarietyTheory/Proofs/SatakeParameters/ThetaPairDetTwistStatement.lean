import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaPairDetTwist
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GodementJacquet.thetaPair_prod_det` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FThetaPairDetTwist.lean&line=645#L645)
-/
theorem _root_.GlobalTheory.T.theta_pair_det_twist : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V), r < t → IsSmoothChar μ → IsUnitaryChar μ → IsSmooth σ → σ.IsIrreducible → IsUnitarisable σ → ThetaPair μ σ (prod₂ σ (detRep (Fin t) μ)) := by
  first | exact @GlobalTheory.GodementJacquet.thetaPair_prod_det | exact GlobalTheory.GodementJacquet.thetaPair_prod_det | (intros; apply GlobalTheory.GodementJacquet.thetaPair_prod_det <;> assumption)
