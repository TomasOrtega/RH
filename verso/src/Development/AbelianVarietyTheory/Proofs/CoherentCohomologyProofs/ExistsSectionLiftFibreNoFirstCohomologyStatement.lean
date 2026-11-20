import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSectionLiftFibreNoFirstCohomology
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AbLaw.FibreLift.exists_pull_eq_smul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCoherentCohomologyProofs%2FExistsSectionLiftFibreNoFirstCohomology.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.exists_section_lift_fibre_noFirstCohomology : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y), Flat f → IsProjBy f → M.IsLB → ∀ (K : Type) [Field K] (g : R →+* K), (∀ y : K, ∃ a b : R, g b ≠ 0 ∧ y * g b = g a) → ∀ (Y₀ : Scheme.{0}) (π : Y₀ ⟶ Y) (f₀ : Y₀ ⟶ Spec (CommRingCat.of K)) (h : IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g))), FirstCohomologyVanishes (M.pull π) → ∀ x₀ : SecOnR f₀ (M.pull π) ⊤, ∃ (c : R) (x : SecOnR f M ⊤), g c ≠ 0 ∧ SecOnR.pull M h.w ⊤ ⊤ le_top x = g c • x₀ := by
  first | exact @GlobalTheory.AbLaw.FibreLift.exists_pull_eq_smul | exact GlobalTheory.AbLaw.FibreLift.exists_pull_eq_smul | (intros; apply GlobalTheory.AbLaw.FibreLift.exists_pull_eq_smul <;> assumption)
