import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

/- English proof (translation)
Introduce `he he' hX`. Set `L' : (Fin N → RL p O Λ) →ₗ[Ainf p O] (Fin N → RL p O Λ)` to `e'.symm.toLinearMap ∘ₗ (Matrix.mulVecLin X) ∘ₗ e.toLinearMap`. Establish `hL' : ∀ w, e' (L' w) = X *ᵥ e w`. Introduce `w`. Simplify using `[L']`.

Establish `hl : ∀ (l : Λ) w, L' (((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) • w) = ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) • L' w`. Introduce `l w`. Apply `e'.injective` to reduce the goal to its premises. Rewrite using `[hL', he, he', hL', Matrix.mulVec_mulVec, hX, ← Matrix.mulVec_mulVec]`. Establish `hs : ∀ (r : RL p O Λ) w, L' (r • w) = r • L' w`.

Introduce `r w`. Proceed by induction on `r using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a l`. Establish `: (a ⊗ₜ[ℤ_[p]] l : RL p O Λ) = algebraMap (Ainf p O) (RL p O Λ) a * ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)`.

Simplify using `[Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]`. Rewrite using `[this, mul_smul, mul_smul, algebraMap_smul, algebraMap_smul, L'.map_smul, hl]`. Consider the case `add x y hx hy => rw [add_smul, add_smul, L'.map_add, hx, hy]`. Set `L : (Fin N → RL p O Λ) →ₗ[RL p O Λ] (Fin N → RL p O Λ)` to `{ toFun := L' map_add' := L'.map_add map_smul' := hs }`. Use `⟨LinearMap.toMatrix' L, fun w => ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.toMatrix'_mulVec]`. Conclude with `(hL' w).symm`.
-/
theorem exists_isMat_of_equivariant (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (ρ ρ' : Λ → Matrix (Fin h) (Fin h) (Ainf p O)) (e e' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) (X : Matrix (Fin h) (Fin h) (Ainf p O)) :
    IsFrame ρ e → IsFrame ρ' e' → (∀ l, X * ρ l = ρ' l * X) → ∃ Y, IsMat e e' X Y := by
  intro he he' hX
  let L' : (Fin N → RL p O Λ) →ₗ[Ainf p O] (Fin N → RL p O Λ) :=
    e'.symm.toLinearMap ∘ₗ (Matrix.mulVecLin X) ∘ₗ e.toLinearMap
  have hL' : ∀ w, e' (L' w) = X *ᵥ e w := by
    intro w; simp [L']
  have hl : ∀ (l : Λ) w, L' (((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) • w) = ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) • L' w := by
    intro l w
    apply e'.injective
    rw [hL', he, he', hL', Matrix.mulVec_mulVec, hX, ← Matrix.mulVec_mulVec]
  have hs : ∀ (r : RL p O Λ) w, L' (r • w) = r • L' w := by
    intro r w
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a l =>
      have : (a ⊗ₜ[ℤ_[p]] l : RL p O Λ) = algebraMap (Ainf p O) (RL p O Λ) a * ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) := by
        simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
      rw [this, mul_smul, mul_smul, algebraMap_smul, algebraMap_smul, L'.map_smul, hl]
    | add x y hx hy => rw [add_smul, add_smul, L'.map_add, hx, hy]
  let L : (Fin N → RL p O Λ) →ₗ[RL p O Λ] (Fin N → RL p O Λ) :=
    { toFun := L'
      map_add' := L'.map_add
      map_smul' := hs }
  refine ⟨LinearMap.toMatrix' L, fun w => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  exact (hL' w).symm

end GlobalTheory.DetInv
