import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductAbelianUniformization
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProductAbelianUniformization.lean&line=171#L171)
-/
theorem _root_.GlobalTheory.T.product_abelian_uniformization : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g : ℕ) (u : HolUnif A L g),
    ∃ U : HolUnif (A ⊗ A) (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩ : LB (A ⊗ A).left) (g + g),
      ∀ x y : Fin g → ℂ, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y) := by
  first | exact @GlobalTheory.exists_holUnif_tensor_self | exact GlobalTheory.exists_holUnif_tensor_self | (intros; apply GlobalTheory.exists_holUnif_tensor_self <;> assumption)
