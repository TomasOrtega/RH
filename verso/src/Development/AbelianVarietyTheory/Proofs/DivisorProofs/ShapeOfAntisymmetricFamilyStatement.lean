import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShapeOfAntisymmetricFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mean4.shapeT_of_wallBd` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FShapeOfAntisymmetricFamily.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.shape_of_antisymmetric_family : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (Φ : ℝ → Fn Y) (hh : Fn Y), 0 < Y.vol → Antisym Φ hh → FlagHt D.what₂.Tau Y.N hh → WallBd Φ → ShapeT Φ hh := by
  first | exact @GlobalTheory.Mean4.shapeT_of_wallBd | exact GlobalTheory.Mean4.shapeT_of_wallBd | (intros; apply GlobalTheory.Mean4.shapeT_of_wallBd <;> assumption)
