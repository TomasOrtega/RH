import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamIffFramedGaloisRepresentation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FDeRhamIffFramedGaloisRepresentation.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.deRham_iff_framed_galois_representation : FrameEx := by
  first | exact @GlobalTheory.PMon.FrameEquiv.frameEx | exact GlobalTheory.PMon.FrameEquiv.frameEx | (intros; apply GlobalTheory.PMon.FrameEquiv.frameEx <;> assumption)
