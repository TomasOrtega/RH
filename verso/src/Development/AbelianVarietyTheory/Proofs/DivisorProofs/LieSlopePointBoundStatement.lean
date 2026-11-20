import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSlopePointBound
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
Apply `GlobalTheory.HeightParts.BdProof.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLieSlopePointBound.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.lie_slope_point_bound : Hypotheses2 → HypothesesH → LieSlope → PtBd → OmCmp → StepBd := by
  first | exact @GlobalTheory.HeightParts.BdProof.main | exact GlobalTheory.HeightParts.BdProof.main | (intros; apply GlobalTheory.HeightParts.BdProof.main <;> assumption)
