import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SpanRealProjectionRationalPointsEqTop
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FSpanRealProjectionRationalPointsEqTop.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.span_realProjection_rationalPoints_eq_top : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (V W : HSp D), Submodule.span ℝ (Set.range fun γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E => piW θ V W (ratW V W γ)) = ⊤ := by
  first | exact @GlobalTheory.FockCompare.span_piW_ratW_eq_top | exact GlobalTheory.FockCompare.span_piW_ratW_eq_top | (intros; apply GlobalTheory.FockCompare.span_piW_ratW_eq_top <;> assumption)
