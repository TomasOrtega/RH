import Mathlib
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
open scoped TensorProduct NumberField
open GlobalTheory.EigenSplit

namespace GlobalTheory

/- English proof (translation)
Introduce `O R k _ _ _ _ _ _ ρ₀ hρ e f hf hε`. Set `b` to `Module.Free.chooseBasis ℤ O`. Establish `key : ∀ (z : R ⊗[ℤ] O) i, TensorProduct.equivFinsuppOfBasisRight b (ρ₀.toIntAlgHom.toLinearMap.rTensor O z) i = ρ₀ (TensorProduct.equivFinsuppOfBasisRight b z i)`. Introduce `z i`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul m n => simp`. Consider the case `add x y hx hy => simp [hx, hy]`. Establish `hmem : ∀ i, TensorProduct.equivFinsuppOfBasisRight b e i ∈ IsLocalRing.maximalIdeal R`. Introduce `i`.

Apply `hρ` to reduce the goal to its premises. Rewrite using `[← key, hε]`. Simplify using the standard rewrite rules. Establish `he : e = (TensorProduct.equivFinsuppOfBasisRight b e).sum (fun i m => m • ((1 : R) ⊗ₜ[ℤ] b i))` using `by conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply e]`. Rewrite using `[TensorProduct.equivFinsuppOfBasisRight_symm_apply]`.

Use `congr 1`. Use extensionality with `i m`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Establish `h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R`. Rewrite using `[← hf, he, map_finsuppSum]`.

Use `Ideal.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Simplify using `only [map_smul, smul_eq_mul]`. Conclude with `Ideal.mul_mem_right _ _ (hmem i)`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h1)`.
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
