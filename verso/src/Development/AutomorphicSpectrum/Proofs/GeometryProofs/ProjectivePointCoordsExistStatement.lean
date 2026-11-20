import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectivePointCoordsExist
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.TupleCoords.exists_tuple_eq_point` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FProjectivePointCoordsExist.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.projective_point_coords_exist : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (r : ℕ) (p : Sp Ω ⟶ PSpace ℚ r), ∃ (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0), p = point ℚ x' hx' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TupleCoords.exists_tuple_eq_point | exact GlobalTheory.CompanionTheory.Ar.TupleCoords.exists_tuple_eq_point | (intros; apply GlobalTheory.CompanionTheory.Ar.TupleCoords.exists_tuple_eq_point <;> assumption)
