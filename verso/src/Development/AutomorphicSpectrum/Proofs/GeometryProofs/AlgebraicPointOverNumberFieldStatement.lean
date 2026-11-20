import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicPointOverNumberField
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TopLeOfClosedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FAlgebraicPointOverNumberField.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.algebraic_point_over_number_field : ∀ (C : Type) [Field C] [CharZero C] [Algebra.IsAlgebraic ℚ C] (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π] (x : Sp C ⟶ X), ∃ (K : Type) (_ : Field K) (_ : NumberField K) (e : K →+* C) (x' : Sp K ⟶ X), spMap e ≫ x' = x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Reg.Descend.exists_numberField_point | exact GlobalTheory.CompanionTheory.Ar.Sl.Reg.Descend.exists_numberField_point | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Reg.Descend.exists_numberField_point <;> assumption)
