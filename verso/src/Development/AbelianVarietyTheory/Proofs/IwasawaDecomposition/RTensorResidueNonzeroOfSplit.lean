import Mathlib
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
open scoped TensorProduct NumberField
open GlobalTheory.EigenSplit

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Treat this case separately. Treat this case separately. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem rTensor_reduction_ne_zero_of_form_eq_one :
    ∀ {O R k : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Field k] [Module.Free ℤ O] [Module.Finite ℤ O]
    (ρ₀ : R →+* k), (∀ x, ρ₀ x = 0 → x ∈ IsLocalRing.maximalIdeal R) → ∀ (e : R ⊗[ℤ] O)
    (f : R ⊗[ℤ] O →ₗ[R] R), f e = 1 → ρ₀.toIntAlgHom.toLinearMap.rTensor O e ≠ 0 := by
  intro O R k _ _ _ _ _ _ ρ₀ hρ e f hf hε
  classical
  let b := Module.Free.chooseBasis ℤ O
  have key : ∀ (z : R ⊗[ℤ] O) i,
      TensorProduct.equivFinsuppOfBasisRight b (ρ₀.toIntAlgHom.toLinearMap.rTensor O z) i
        = ρ₀ (TensorProduct.equivFinsuppOfBasisRight b z i) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp
    | add x y hx hy => simp [hx, hy]
  have hmem : ∀ i, TensorProduct.equivFinsuppOfBasisRight b e i ∈ IsLocalRing.maximalIdeal R := by
    intro i
    apply hρ
    rw [← key, hε]
    simp
  have he : e = (TensorProduct.equivFinsuppOfBasisRight b e).sum
      (fun i m => m • ((1 : R) ⊗ₜ[ℤ] b i)) := by
    conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply e]
    rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply]
    congr 1
    ext i m
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← hf, he, map_finsuppSum]
    refine Ideal.sum_mem _ fun i _ => ?_
    simp only [map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (hmem i)
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h1)

end GlobalTheory
