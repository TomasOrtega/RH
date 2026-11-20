import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLocalRingResidueFieldFiniteOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeSpanSupPow
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ResFin.finite_residueField_O` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FModelLocalRingResidueFieldFiniteOfClosedPoint.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.modelLocalRing_residueField_finite_of_closedPoint : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (x : M.Z), IsClosed ({x} : Set M.Z) → Finite (ResidueField (M.O x)) := by
  first | exact @GlobalTheory.ResFin.finite_residueField_O | exact GlobalTheory.ResFin.finite_residueField_O | (intros; apply GlobalTheory.ResFin.finite_residueField_O <;> assumption)
