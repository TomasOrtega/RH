import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolarisationFormOfLineBundle
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
Apply `GlobalTheory.BundleForm.exists_formIs` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FExistsPolarisationFormOfLineBundle.lean&line=99#L99)
-/
theorem _root_.GlobalTheory.T.exists_polarisationForm_of_lineBundle : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left), M.IsLB → ∃ s : P.A ⟶ P.A, FormIs P M s := by
  first | exact @GlobalTheory.BundleForm.exists_formIs | exact GlobalTheory.BundleForm.exists_formIs | (intros; apply GlobalTheory.BundleForm.exists_formIs <;> assumption)
