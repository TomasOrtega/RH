import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionFieldOfPointCoordsTop
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.MPDict.GenTop.blockFnField_ptCoord_eq_top` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFunctionFieldOfPointCoordsTop.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.function_field_of_point_coords_top : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) [CharZero ((MP ℤ m n).residueField x)], blockFnField (ptCoord x) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.MPDict.GenTop.blockFnField_ptCoord_eq_top | exact GlobalTheory.CompanionTheory.MPDict.GenTop.blockFnField_ptCoord_eq_top | (intros; apply GlobalTheory.CompanionTheory.MPDict.GenTop.blockFnField_ptCoord_eq_top <;> assumption)
