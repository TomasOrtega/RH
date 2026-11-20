import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueRationalStatement
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Link.existsUnique_rat` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FExistsUniqueRationalStatement.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_unique_rational_statement : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Link.existsUnique_rat | exact GlobalTheory.CompanionTheory.Ar.Link.existsUnique_rat | (intros; apply GlobalTheory.CompanionTheory.Ar.Link.existsUnique_rat <;> assumption)
