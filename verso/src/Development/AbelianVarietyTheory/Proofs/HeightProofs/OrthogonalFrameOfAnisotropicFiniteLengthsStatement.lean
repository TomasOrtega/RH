import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthogonalFrameOfAnisotropicFiniteLengths
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FOrthogonalFrameOfAnisotropicFiniteLengths.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.orthogonalFrame_of_anisotropicFiniteLengths : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], AnisoSmall E → OrthoSmall E := by
  first | exact @GlobalTheory.SmoothForms.orthoSmall_of_anisoSmall | exact GlobalTheory.SmoothForms.orthoSmall_of_anisoSmall | (intros; apply GlobalTheory.SmoothForms.orthoSmall_of_anisoSmall <;> assumption)
