import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

variable {R A : Type} (R' : Type) [CommRing R] [CommRing A] [Bialgebra R A] [CommRing R']
  [Algebra R R']

/- English proof (translation)
Use `AlgebraTensorModule.ext fun r a => ?_` and prove the remaining obligations. Rewrite using `[← mul_one r, ← smul_eq_mul, ← smul_tmul', map_smul, map_smul]`. Use `congr 1`. Establish `h : ∀ c : A ⊗[R] A, AlgebraTensorModule.tensorTensorTensorComm R R' R R' R' R' A A (comul (R` using `R') (1 : R') ⊗ₜ[R] c) = AlgebraTensorModule.distribBaseChange R R' A A (1 ⊗ₜ c) := by`. Introduce `c`.

Proceed by induction on `c with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [tmul_add, map_add, hx, hy]`. Consider the case `tmul x y => simp [Bialgebra.comul_one, Algebra.TensorProduct.one_def]`. Simplify using `only [cobOne_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.baseChange_tmul, tmul_sub, map_sub, TensorProduct.comul_tmul, h, AlgebraTensorModule.distribBaseChange_tmul, Algebra.TensorProduct.one_def]`.
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
Use `set K := LinearMap.ker (cobOne R A)`. Establish `hsub : ∀ y : R' ⊗[R] K, (liftSemi (toBaseChange R R' A).prim y).1 = K.subtype.lTensor R' y`. Introduce `y`. Proceed by induction on `y with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]`. Consider the case `tmul r b`. Rewrite using `[liftSemi_tmul, Submodule.coe_smul, SemiBialgHom.prim_val, toBaseChange_apply, LinearMap.lTensor_tmul, Submodule.subtype_apply, smul_tmul', smul_eq_mul, mul_one]`. Establish `hex` using `Module.Flat.lTensor_exact R' (LinearMap.exact_subtype_ker_map (cobOne R A))`. Use `⟨fun x y h => ?_, fun z => ?_⟩` and prove the remaining obligations.

Use `Module.Flat.lTensor_preserves_injective_linearMap (M := R') K.subtype K.injective_subtype ?_` and prove the remaining obligations. Rewrite using `[← hsub, ← hsub, h]`. Take `⟨x, hx⟩` from `z`. Establish `hz : (cobOne R A).lTensor R' x = 0`. Establish `h0 : cobOne R' (R' ⊗[R] A) x = 0` using `hx`.

Rewrite `h0` using `[cobOne_baseChange, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff, LinearMap.baseChange_eq_ltensor]`. Conclude with `h0`. Take `⟨y, hy⟩` from `(hex x).1 hz`. Conclude with `⟨y, Subtype.ext ((hsub y).trans hy)⟩`.
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
