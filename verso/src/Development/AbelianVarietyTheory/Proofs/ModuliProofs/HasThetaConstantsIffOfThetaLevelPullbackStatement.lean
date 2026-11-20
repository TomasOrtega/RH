import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
/- English proof (citation)
Apply `GlobalTheory.hasTh_iff_of_tmap` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FHasThetaConstantsIffOfThetaLevelPullback.lean&line=275#L275)
-/
theorem _root_.GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (S' : Scheme.{0}) (s' : S' ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s') (f : S' ⟶ S) (R : Type) [CommRing R] (x : Sp R ⟶ S') (v : Ix g (N' ^ 2) → R), TMap t' t f → (t'.HasTh x v ↔ t.HasTh (x ≫ f) v) := by
  first | exact @GlobalTheory.hasTh_iff_of_tmap | exact GlobalTheory.hasTh_iff_of_tmap | (intros; apply GlobalTheory.hasTh_iff_of_tmap <;> assumption)
