import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.GreedySplittingPrincipalTorusExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
/- English proof (citation)
Apply `GlobalTheory.greedy_splitting_exists` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTorusSplitting%2FGreedySplittingPrincipalTorusExists.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.greedy_splitting_principal_torus_exists : SplitStatement := by
  first | exact @GlobalTheory.greedy_splitting_exists | exact GlobalTheory.greedy_splitting_exists | (intros; apply GlobalTheory.greedy_splitting_exists <;> assumption)
