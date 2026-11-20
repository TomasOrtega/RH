import Formalism.FockGram.StatementTensor

open Matrix LinearMap Module TensorProduct

noncomputable section
namespace Formalism.E

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem hermitian_tensor_mul_apply : HTmulApply := by
  intro R M₁ M₂ _ _ _ _ _ _ B₁ B₂ x₁ y₁ x₂ y₂
  simp [htmul, tensorFunctional]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
example {R M₁ M₂ : Type} [CommRing R] [StarRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] (B₁ : M₁ →ₗ⋆[R] M₁ →ₗ[R] R) (B₂ : M₂ →ₗ⋆[R] M₂ →ₗ[R] R)
    (a : R) (z w : M₁ ⊗[R] M₂) :
    htmul B₁ B₂ (a • z) w = star a * htmul B₁ B₂ z w ∧ htmul B₁ B₂ z (a • w) = a * htmul B₁ B₂ z w := by
  simp [starRingEnd_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hermitian_tensor_mul_gram : HTmulGram := by
  intro R M₁ M₂ ι₁ ι₂ _ _ _ _ _ _ _ _ _ _ B₁ B₂ v₁ v₂
  have h : sgram (htmul B₁ B₂) (fun p : ι₁ × ι₂ => v₁ p.1 ⊗ₜ[R] v₂ p.2) =
      Matrix.kroneckerMap (· * ·) (sgram B₁ v₁) (sgram B₂ v₂) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp [sgram, htmul, tensorFunctional]
  refine ⟨h, ?_⟩
  rw [h]
  exact Matrix.det_kronecker _ _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Proceed by induction. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately.
-/
theorem hermitian_tensor_mul_hermitian : HTmulHerm := by
  intro R M₁ M₂ _ _ _ _ _ _ B₁ B₂ h₁ h₂
  rw [LinearMap.isSymm_def] at *
  intro z w
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x₁ x₂ =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul y₁ y₂ =>
      simp only [htmul, tensorFunctional] at *
      simp [← h₁ x₁ y₁, ← h₂ x₂ y₂, starRingEnd_apply, mul_comm]
    | add a b ha hb => simp_all
  | add a b ha hb => simp_all

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
example {R M : Type} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
    (B : M →ₗ⋆[R] M →ₗ[R] R) : B.IsSymm ↔ ∀ x y, star (B x y) = B y x := by
  simp [LinearMap.isSymm_def, starRingEnd_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
example (n : ℤ) : star n = n := rfl

end Formalism.E
