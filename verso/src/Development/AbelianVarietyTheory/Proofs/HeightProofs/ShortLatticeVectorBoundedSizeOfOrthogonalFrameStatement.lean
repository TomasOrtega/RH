import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ShortLatticeVectorBoundedSizeOfOrthogonalFrame
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SmoothForms.Short.shortSmall` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FShortLatticeVectorBoundedSizeOfOrthogonalFrame.lean&line=149#L149)
-/
theorem _root_.GlobalTheory.T.shortLatticeVectorBoundedSize_of_orthogonalFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], FrameSmall E → ShortSmall E := by
  first | exact @GlobalTheory.SmoothForms.Short.shortSmall | exact GlobalTheory.SmoothForms.Short.shortSmall | (intros; apply GlobalTheory.SmoothForms.Short.shortSmall <;> assumption)
