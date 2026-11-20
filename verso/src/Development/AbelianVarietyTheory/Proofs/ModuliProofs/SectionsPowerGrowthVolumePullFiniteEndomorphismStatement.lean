import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsPowerGrowthVolumePullFiniteEndomorphism
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.vol_pull_of_isFinite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FSectionsPowerGrowthVolumePullFiniteEndomorphism.lean&line=205#L205)
-/
theorem _root_.GlobalTheory.T.sectionsPowerGrowthVolume_pull_finite_endomorphism : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (α : P.A ⟶ P.A) (D : ℕ) (M : LB P.A.left) (δ : ℝ), IsMonHom α → IsFinite α.left → MapDeg α.left D → M.IsLB → Out.RelAmple P.A M → Vol P.A.hom M P.g δ → Vol P.A.hom (M.pull α.left) P.g (D * δ) := by
  first | exact @GlobalTheory.vol_pull_of_isFinite | exact GlobalTheory.vol_pull_of_isFinite | (intros; apply GlobalTheory.vol_pull_of_isFinite <;> assumption)
