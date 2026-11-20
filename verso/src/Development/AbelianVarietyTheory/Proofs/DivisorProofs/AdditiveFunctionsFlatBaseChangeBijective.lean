import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

variable {R A : Type} (R' : Type) [CommRing R] [CommRing A] [Bialgebra R A] [CommRing R']
  [Algebra R R']

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules.
-/
theorem cobOne_baseChange :
    cobOne R' (R' ⊗[R] A) = (AlgebraTensorModule.distribBaseChange R R' A A).toLinearMap ∘ₗ
      (cobOne R A).baseChange R' := by
  refine AlgebraTensorModule.ext fun r a => ?_
  rw [← mul_one r, ← smul_eq_mul, ← smul_tmul', map_smul, map_smul]
  congr 1
  have h : ∀ c : A ⊗[R] A, AlgebraTensorModule.tensorTensorTensorComm R R' R R' R' R' A A
      (comul (R := R') (1 : R') ⊗ₜ[R] c) = AlgebraTensorModule.distribBaseChange R R' A A (1 ⊗ₜ c) := by
    intro c
    induction c with
    | zero => simp
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
    | tmul x y => simp [Bialgebra.comul_one, Algebra.TensorProduct.one_def]
  simp only [cobOne_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.baseChange_tmul, tmul_sub, map_sub, TensorProduct.comul_tmul, h,
    AlgebraTensorModule.distribBaseChange_tmul, Algebra.TensorProduct.one_def]

end GlobalTheory.PDiv

namespace GlobalTheory.PDiv

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem liftSemi_prim_baseChange_bijective {R A : Type} (R' : Type) [CommRing R] [CommRing A]
    [Bialgebra R A] [CommRing R'] [Algebra R R'] [Module.Flat R R'] :
    Function.Bijective (liftSemi (toBaseChange R R' A).prim) := by
  set K := LinearMap.ker (cobOne R A)
  have hsub : ∀ y : R' ⊗[R] K,
      (liftSemi (toBaseChange R R' A).prim y).1 = K.subtype.lTensor R' y := by
    intro y
    induction y with
    | zero => simp
    | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
    | tmul r b =>
      rw [liftSemi_tmul, Submodule.coe_smul, SemiBialgHom.prim_val, toBaseChange_apply,
        LinearMap.lTensor_tmul, Submodule.subtype_apply, smul_tmul', smul_eq_mul, mul_one]
  have hex := Module.Flat.lTensor_exact R' (LinearMap.exact_subtype_ker_map (cobOne R A))
  refine ⟨fun x y h => ?_, fun z => ?_⟩
  · refine Module.Flat.lTensor_preserves_injective_linearMap (M := R') K.subtype
      K.injective_subtype ?_
    rw [← hsub, ← hsub, h]
  · obtain ⟨x, hx⟩ := z
    have hz : (cobOne R A).lTensor R' x = 0 := by
      have h0 : cobOne R' (R' ⊗[R] A) x = 0 := hx
      rw [cobOne_baseChange, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.map_eq_zero_iff, LinearMap.baseChange_eq_ltensor] at h0
      exact h0
    obtain ⟨y, hy⟩ := (hex x).1 hz
    exact ⟨y, Subtype.ext ((hsub y).trans hy)⟩

end GlobalTheory.PDiv
