import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LinearCombinationGeneratorSectionExists
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SecNorm.exists_gen_normalised_along` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FLinearCombinationGeneratorSectionExists.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.linear_combination_generator_section_exists : ∀ {X Y S₀ : Scheme.{0}} {M : LB X}, M.IsLB → ∀ {K K₂ : Type} [Fintype K] [Fintype K₂] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ₂ : K₂ → (S₀ ⟶ X)) (ε₂ : K₂ → ℤ) (p : Y ⟶ S₀) (e : S₀ ⟶ Y), e ≫ p = 𝟙 S₀ → FormEq (fun k => e ≫ φ k) ε φ₂ ε₂ →
    ∀ (t : LB.Gen (LB.LinComb M φ ε)), t.IsGen → ∀ (R : LB.Gen (LB.LinComb M φ₂ ε₂)), R.IsGen →
    ∃ t' : LB.Gen (LB.LinComb M φ ε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (s : Z ⟶ S₀) (z : Z) (J : (Z ⟶ X) → M.ι), Good M z J → val t' (s ≫ e) z J = val R s z J := by
  first | exact @GlobalTheory.CompanionTheory.SecNorm.exists_gen_normalised_along | exact GlobalTheory.CompanionTheory.SecNorm.exists_gen_normalised_along | (intros; apply GlobalTheory.CompanionTheory.SecNorm.exists_gen_normalised_along <;> assumption)
