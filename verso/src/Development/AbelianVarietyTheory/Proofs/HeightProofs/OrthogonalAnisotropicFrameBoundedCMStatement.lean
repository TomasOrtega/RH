import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthogonalAnisotropicFrameBoundedCM
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FOrthogonalAnisotropicFrameBoundedCM.lean&line=157#L157)
-/
theorem _root_.GlobalTheory.T.orthogonalAnisotropicFrame_bounded_CM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], FrameSmall E := by
  first | exact @GlobalTheory.SmoothForms.frameSmall | exact GlobalTheory.SmoothForms.frameSmall | (intros; apply GlobalTheory.SmoothForms.frameSmall <;> assumption)
