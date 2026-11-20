import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDiagonalCoordinatesOfDeterminantCondition

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

/- English proof (translation)
Introduce `F _ _ 𝔠 X L u κ hκ`. Take `⟨h₁, h₂⟩` from `GlobalTheory.TorusTransfer.tangent_bijective u X.dim`. Take `⟨d, hdi, hd⟩` from `GlobalTheory.DiagCoord.exists_diff_linear u X.rm h₁ h₂`. Establish `hds : Function.Surjective d` using `fun w => by`. Take `⟨v, hv, hw⟩` from `(h₂ w).exists`.

Use `⟨GlobalTheory.Serre.Lie.mk X.rm v hv, ?_⟩` and prove the remaining obligations. Conclude with `(h₁ _ hv).unique (hd _) hw`. Set `e : X.Lie ≃ₗ[ℂ] (Fin (Module.finrank ℚ F) → ℂ)` to `LinearEquiv.ofBijective d ⟨hdi, hds⟩`. Set `b : Module.Basis (Fin (Module.finrank ℚ F)) ℂ X.Lie` to `(Pi.basisFun ℂ _).map e.symm`. Use `⟨⟨κ • b.det, ?_⟩, fun v W hW => ?_⟩` and prove the remaining obligations.

Rewrite using `[show κ • b.det = (Units.mk0 κ hκ : ℂˣ) • b.det from rfl, Submodule.span_singleton_group_smul_eq]`. Conclude with `(Obj.DetGen.ofBasis X b).2`. Establish `hv : ∀ i, d (v i) = W i` using `fun i => (h₁ _ (v i).isTangent).unique (hd _) (hW i)`. Establish `hm : b.toMatrix v = W.transpose`. Use extensionality with `i j`.

Rewrite using `[Module.Basis.toMatrix_apply, Matrix.transpose_apply]`. Rewrite using `[Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm, Pi.basisFun_repr]`. Conclude with `congrFun (hv j) i`. Rewrite using `[AlternatingMap.smul_apply, Module.Basis.det_apply, hm, Matrix.det_transpose, smul_eq_mul]`.
-/
theorem Obj.exists_detGen_holUnif : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left)
    (u : HolUnif X.A L (Module.finrank ℚ F)) (κ : ℂ), κ ≠ 0 →
    ∃ δ : X.DetGen, ∀ (v : Fin (Module.finrank ℚ F) → X.Lie)
      (W : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ),
      (∀ i, u.IsDiff (W i) (v i).hom) → δ.1 v = κ * W.det := by
  intro F _ _ 𝔠 X L u κ hκ
  obtain ⟨h₁, h₂⟩ := GlobalTheory.TorusTransfer.tangent_bijective u X.dim
  obtain ⟨d, hdi, hd⟩ := GlobalTheory.DiagCoord.exists_diff_linear u X.rm h₁ h₂
  have hds : Function.Surjective d := fun w => by
    obtain ⟨v, hv, hw⟩ := (h₂ w).exists
    refine ⟨GlobalTheory.Serre.Lie.mk X.rm v hv, ?_⟩
    exact (h₁ _ hv).unique (hd _) hw
  let e : X.Lie ≃ₗ[ℂ] (Fin (Module.finrank ℚ F) → ℂ) := LinearEquiv.ofBijective d ⟨hdi, hds⟩
  let b : Module.Basis (Fin (Module.finrank ℚ F)) ℂ X.Lie := (Pi.basisFun ℂ _).map e.symm
  refine ⟨⟨κ • b.det, ?_⟩, fun v W hW => ?_⟩
  · rw [show κ • b.det = (Units.mk0 κ hκ : ℂˣ) • b.det from rfl, Submodule.span_singleton_group_smul_eq]
    exact (Obj.DetGen.ofBasis X b).2
  · have hv : ∀ i, d (v i) = W i := fun i => (h₁ _ (v i).isTangent).unique (hd _) (hW i)
    have hm : b.toMatrix v = W.transpose := by
      ext i j
      rw [Module.Basis.toMatrix_apply, Matrix.transpose_apply]
      rw [Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm, Pi.basisFun_repr]
      exact congrFun (hv j) i
    rw [AlternatingMap.smul_apply, Module.Basis.det_apply, hm, Matrix.det_transpose, smul_eq_mul]

end GlobalTheory.RealMult
