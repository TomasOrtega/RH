import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeModuleTensorAction
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.invertible_of_baseChange_tensor_int` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBaseChangeModuleTensorAction.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.base_change_module_tensor_action : ∀ (R R' O : Type) [CommRing R] [CommRing R'] [Algebra R R'] [CommRing O] (M : Type) [AddCommGroup M]
    [Module R M] [Module O M] [SMulCommClass R O M] (N : Type) [AddCommGroup N] [Module R' N] [Module O N]
    [SMulCommClass R' O N] (e : R' ⊗[R] M ≃ₗ[R'] N), (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) →
    letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
    letI : Module (R' ⊗[ℤ] O) N := TensorProduct.Algebra.module
    Module.Invertible (R ⊗[ℤ] O) M → Module.Invertible (R' ⊗[ℤ] O) N := by
  first | exact @GlobalTheory.invertible_of_baseChange_tensor_int | exact GlobalTheory.invertible_of_baseChange_tensor_int | (intros; apply GlobalTheory.invertible_of_baseChange_tensor_int <;> assumption)
