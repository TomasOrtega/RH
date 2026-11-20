import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsDominantHomOfVectorOfQuasiFiniteAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FIsDominantHomOfVectorOfQuasiFiniteAt.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.isDominant_homOfVector_of_quasiFiniteAt' : ∀ (X Z : Scheme.{0}) [IsIntegral X] [IsIntegral Z] (t : X ⟶ Z) [LocallyOfFiniteType t] (g : ℕ) (U : X.Opens), (U : Set X).Nonempty → SmoothOfRelativeDimension g (U.ι ≫ t) → ∀ (u : Fin g → Γ(X, ⊤)) (w : X), (AffineSpace.homOfVector t u).QuasiFiniteAt w → IsDominant (AffineSpace.homOfVector t u) := by
  first | exact @GlobalTheory.isDominant_homOfVector_of_quasiFiniteAt | exact GlobalTheory.isDominant_homOfVector_of_quasiFiniteAt | (intros; apply GlobalTheory.isDominant_homOfVector_of_quasiFiniteAt <;> assumption)
