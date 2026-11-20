import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteTypeModelOfSmoothAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
/- English proof (citation)
Apply `GlobalTheory.exists_finiteType_model_of_smooth_affine` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FExistsFiniteTypeModelOfSmoothAffine.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_finiteType_model_of_smooth_affine' : ∀ (V : Type) [CommRing V] (X : Scheme.{0}) (p : X ⟶ Sp V), IsAffine X → Smooth p → ∃ (R : Type) (_ : CommRing R) (f : R →+* V) (X₀ : Scheme.{0}) (p₀ : X₀ ⟶ Sp R) (φ : X ⟶ X₀), Algebra.FiniteType ℤ R ∧ Smooth p₀ ∧ IsAffine X₀ ∧ IsPullback φ p p₀ (spMap f) := by
  first | exact @GlobalTheory.exists_finiteType_model_of_smooth_affine | exact GlobalTheory.exists_finiteType_model_of_smooth_affine | (intros; apply GlobalTheory.exists_finiteType_model_of_smooth_affine <;> assumption)
