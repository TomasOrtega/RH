import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArithmeticVarietyPointDimension
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FArithmeticVarietyPointDimension.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.arithmetic_variety_point_dimension : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (d : ℕ), CharZero ((MP ℤ m n).residueField x) → topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (d : ℕ) → Geo.IsArithVar (ptIdeal x) d := by
  first | exact @GlobalTheory.CompanionTheory.MPDict.DimVar.isArithVar_ptIdeal | exact GlobalTheory.CompanionTheory.MPDict.DimVar.isArithVar_ptIdeal | (intros; apply GlobalTheory.CompanionTheory.MPDict.DimVar.isArithVar_ptIdeal <;> assumption)
