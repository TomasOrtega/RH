import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightIntegralLieSlope
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeightIntegralLieSlope.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.height_integral_lie_slope : Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → LieSlope → HtIntSt := by
  first | exact @GlobalTheory.HeightParts.htIntSt_of_hypotheses | exact GlobalTheory.HeightParts.htIntSt_of_hypotheses | (intros; apply GlobalTheory.HeightParts.htIntSt_of_hypotheses <;> assumption)
