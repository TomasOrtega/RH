import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QuasiFiniteAtAffineSpaceHomOfVectorOfCoord
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
/- English proof (citation)
Apply `GlobalTheory.quasiFiniteAt_homOfVector_of_coord` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FQuasiFiniteAtAffineSpaceHomOfVectorOfCoord.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.quasiFiniteAt_affineSpace_homOfVector_of_coord : ∀ (C : Core) (w : C.G.toScheme) (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)), IsClosed ({w} : Set C.G.toScheme) → C.Coord w W hw u → (AffineSpace.homOfVector (W.ι ≫ C.GG.hom) (fun i => W.topIso.inv.hom (u i))).QuasiFiniteAt ⟨w, hw⟩ := by
  first | exact @GlobalTheory.quasiFiniteAt_homOfVector_of_coord | exact GlobalTheory.quasiFiniteAt_homOfVector_of_coord | (intros; apply GlobalTheory.quasiFiniteAt_homOfVector_of_coord <;> assumption)
