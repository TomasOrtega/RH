import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

/- English proof (translation)
Use `⟨funext fun a => funext fun b => ?_, funext fun a => funext fun b => ?_⟩` and prove the remaining obligations. Use `show Algebra.TensorProduct.map _ _ (_ ⊗ₜ[R] 1) = _`. Use `(Algebra.TensorProduct.map_tmul _ _ _ _).trans ?_` and prove the remaining obligations. Use `congr 1`. Apply the tactic sequence `all_goals first | exact map_one _ | rfl`.

Use `show Algebra.TensorProduct.map _ _ (1 ⊗ₜ[R] _) = _`. Use `(Algebra.TensorProduct.map_tmul _ _ _ _).trans ?_` and prove the remaining obligations. Use `congr 1`. Apply the tactic sequence `all_goals first | exact map_one _ | rfl`.
-/
theorem bv_pulln_box {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {N p q : ℕ}
    (ρ₁ : Fin (N + 1) →o Fin (p + 1)) (ρ₂ : Fin (N + 1) →o Fin (q + 1)) (x : Cn F N) :
    (bv F ρ₁ ρ₂ (pulln (boxL F) N x) = fun a _ ↦ pr F ρ₁ x a ⊗ₜ[R] 1) ∧
      (bv F ρ₁ ρ₂ (pulln (boxR F) N x) = fun _ b ↦ 1 ⊗ₜ[R] pr F ρ₂ x b) := by
  refine ⟨funext fun a => funext fun b => ?_, funext fun a => funext fun b => ?_⟩
  · show Algebra.TensorProduct.map _ _ (_ ⊗ₜ[R] 1) = _
    refine (Algebra.TensorProduct.map_tmul _ _ _ _).trans ?_
    congr 1
    all_goals first | exact map_one _ | rfl
  · show Algebra.TensorProduct.map _ _ (1 ⊗ₜ[R] _) = _
    refine (Algebra.TensorProduct.map_tmul _ _ _ _).trans ?_
    congr 1
    all_goals first | exact map_one _ | rfl

end GlobalTheory.CompanionTheory.HopfC
