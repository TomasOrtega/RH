import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LevelAndHeckeOfZeroSignature
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Top.LevelZero.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FLevelAndHeckeOfZeroSignature.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.level_and_hecke_of_zero_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), D.p + D.q = 0 → ToroidalLevelCompatibility (H := H) (D := D) ∧ ToroidalHeckeCompatibility (H := H) (D := D) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.LevelZero.main | exact GlobalTheory.CompanionTheory.Ar.Top.LevelZero.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.LevelZero.main <;> assumption)
