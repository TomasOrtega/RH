import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreCurveDegreeCompare
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LocalComponentsSurjective
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PropZ
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Flat.fibreCurve_curveIn_degree` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FFibreCurveDegreeCompare.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.fibre_curve_degree_compare : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] (s : X ⟶ Spec (CommRingCat.of O)) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : Ω) (Γ : FibreCurve ξ ϖ), IsCptGen ξ → ∃ Y : Crv.CurveIn Γ.C Γ.η, Y.x = Γ.z ∧ ∀ (L : Lat ξ Ω) (n : ℤ), L.IsVB 1 ⊤ → (Γ.HasDeg L n ↔ Y.IsDeg L n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.fibreCurve_curveIn_degree | exact GlobalTheory.CompanionTheory.Ar.Flat.fibreCurve_curveIn_degree | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.fibreCurve_curveIn_degree <;> assumption)
