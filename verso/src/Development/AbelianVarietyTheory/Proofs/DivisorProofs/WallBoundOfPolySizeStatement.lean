import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WallBoundOfPolySize
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWallBoundOfPolySize.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.wall_bound_of_poly_size : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (A : SlopeTestRemainingChoices Y), ∀ (Φ : ℝ → Fn Y), 2 < D.R.f * (Y.N - 1) → PolySize A Φ → Agree A → WallSmall A → WallBd Φ := by
  first | exact @GlobalTheory.Mean4.wallBd_of_wallSmall | exact GlobalTheory.Mean4.wallBd_of_wallSmall | (intros; apply GlobalTheory.Mean4.wallBd_of_wallSmall <;> assumption)
