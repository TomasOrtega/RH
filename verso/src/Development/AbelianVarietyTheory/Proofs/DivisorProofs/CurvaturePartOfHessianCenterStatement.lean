import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePartOfHessianCenter
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InSOfParts
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RegCurv.curvPart` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCurvaturePartOfHessianCenter.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.curvature_part_of_hessian_center : HessSt → CentSt → OnObj fun _ _ _ T _ _ => ∀ c, GlobalTheory.RegEst.CurvPart (T.F c) := by
  first | exact @GlobalTheory.RegCurv.curvPart | exact GlobalTheory.RegCurv.curvPart | (intros; apply GlobalTheory.RegCurv.curvPart <;> assumption)
