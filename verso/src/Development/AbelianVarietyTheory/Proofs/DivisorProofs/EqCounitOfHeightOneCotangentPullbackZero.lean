import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualHeightOneAdjoinPrimitiveEqTop

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.HeightOneHom

/- English proof (translation)
Rewrite `hφ` using `[cobOne_apply, sub_sub, sub_eq_zero, CartierDual.comul_eq_iff]`. Establish `h` using `hφ a b`. Rewrite `h` using `[map_add, LinearMap.add_apply, CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul, CartierDual.one_apply, CartierDual.one_apply]`. Express the relevant statement in the definitionally equal form `φ (a * b) = _`. Rewrite using `[← h]`.

Simplify using `only [counitAlgHom_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem primitive_apply_mul {k C : Type} [Field k] [CommRing C] [HopfAlgebra k C]
    [IsCocomm k C] [Module.Finite k C] {φ : CartierDual k C} (hφ : cobOne k (CartierDual k C) φ = 0) (a b : C) :
    φ.ofConv (a * b) = counitAlgHom k C a • φ.ofConv b + counitAlgHom k C b • φ.ofConv a := by
  rw [cobOne_apply, sub_sub, sub_eq_zero, CartierDual.comul_eq_iff] at hφ
  have h := hφ a b
  rw [map_add, LinearMap.add_apply, CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul,
    CartierDual.one_apply, CartierDual.one_apply] at h
  change φ (a * b) = _
  rw [← h]
  simp only [counitAlgHom_apply, smul_eq_mul]
  ring

/- English proof (translation)
Introduce `p _ k _ _ C _ _ _ _ D _ _ _ _ f hpow hcot d`. Establish `hgen` using `GlobalTheory.HeightOneDual.adjoin_primitive_eq_top p k C hpow`. Establish `hzero : ∀ φ : CartierDual k C, cobOne k (CartierDual k C) φ = 0 → ∀ x, φ (f x) = 0`. Introduce `φ hφ x`. Establish `h1` using `AugCot.lift_d (counitAlgHom k C) φ.ofConv (primitive_apply_mul hφ) (f x)`.

Establish `h2 : dUnit k (f x) = 0`. Rewrite using `[← cotMap_d f x, hcot, LinearMap.zero_apply]`. Express the relevant statement in the definitionally equal form `φ.ofConv (f x) = 0`. Rewrite using `[← h1]`. Express the relevant statement in the definitionally equal form `AugCot.lift (counitAlgHom k C) φ.ofConv (primitive_apply_mul hφ) (dUnit k (f x)) = 0`.

Rewrite using `[h2, map_zero]`. Establish `hone : ∀ φ : CartierDual k C, cobOne k (CartierDual k C) φ = 0 → φ 1 = 0`. Introduce `φ hφ`. Use `AugCot.pointDer_algebraMap (primitive_apply_mul hφ) (1 : k)` as an intermediate fact. Rewrite `this` using `[map_one]`. Then use the resulting hypothesis.

Set `T : CartierDual k C →ₐ[k] CartierDual k D` to `(Algebra.ofId k _).comp (counitAlgHom k (CartierDual k C))`. Establish `hT : ∀ φ : CartierDual k C, ∀ x : D, T φ x = φ 1 * counit (R` using `k) x := by`. Introduce `φ x`. Express the relevant statement in the definitionally equal form `(algebraMap k (CartierDual k D) (counit (R := k) φ)) x = _`. Rewrite using `[Algebra.algebraMap_eq_smul_one, CartierDual.counit_apply]`.

Express the relevant statement in the definitionally equal form `φ 1 • (1 : CartierDual k D) x = _`. Rewrite using `[CartierDual.one_apply, smul_eq_mul]`. Establish `hM : (CartierDual.map f : CartierDual k C →ₐ[k] CartierDual k D) = T`. Use `AlgHom.ext_of_adjoin_eq_top hgen fun φ hφ => ?_` and prove the remaining obligations. Use `CartierDual.ext_apply fun x => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `CartierDual.map f φ x = T φ x`. Rewrite using `[CartierDual.map_apply, hT, hzero φ hφ x, hone φ hφ, zero_mul]`. Use `CartierDual.eq_of_forall_apply (R := k) fun φ => ?_` and prove the remaining obligations. Establish `h1 : CartierDual.map f φ d = T φ d`. Rewrite using `[← hM]`.

Both sides reduce to the same expression. Rewrite `h1` using `[CartierDual.map_apply, hT]`. Rewrite using `[h1, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_comm]`.
-/
theorem eq_algebraMap_counit_of_cotMap_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C]
    (D : Type) [CommRing D] [HopfAlgebra k D] [IsCocomm k D] [Module.Finite k D]
    (f : D →ₐc[k] C), (∀ a ∈ augIdeal k C, a ^ p = 0) → cotMap f = 0 →
    ∀ d, f d = algebraMap k C (counit (R := k) d) := by
  intro p _ k _ _ C _ _ _ _ D _ _ _ _ f hpow hcot d
  have hgen := GlobalTheory.HeightOneDual.adjoin_primitive_eq_top p k C hpow
  have hzero : ∀ φ : CartierDual k C, cobOne k (CartierDual k C) φ = 0 → ∀ x, φ (f x) = 0 := by
    intro φ hφ x
    have h1 := AugCot.lift_d (counitAlgHom k C) φ.ofConv (primitive_apply_mul hφ) (f x)
    have h2 : dUnit k (f x) = 0 := by
      rw [← cotMap_d f x, hcot, LinearMap.zero_apply]
    change φ.ofConv (f x) = 0
    rw [← h1]
    change AugCot.lift (counitAlgHom k C) φ.ofConv (primitive_apply_mul hφ) (dUnit k (f x)) = 0
    rw [h2, map_zero]
  have hone : ∀ φ : CartierDual k C, cobOne k (CartierDual k C) φ = 0 → φ 1 = 0 := by
    intro φ hφ
    have := AugCot.pointDer_algebraMap (primitive_apply_mul hφ) (1 : k)
    rwa [map_one] at this
  let T : CartierDual k C →ₐ[k] CartierDual k D :=
    (Algebra.ofId k _).comp (counitAlgHom k (CartierDual k C))
  have hT : ∀ φ : CartierDual k C, ∀ x : D, T φ x = φ 1 * counit (R := k) x := by
    intro φ x
    change (algebraMap k (CartierDual k D) (counit (R := k) φ)) x = _
    rw [Algebra.algebraMap_eq_smul_one, CartierDual.counit_apply]
    change φ 1 • (1 : CartierDual k D) x = _
    rw [CartierDual.one_apply, smul_eq_mul]
  have hM : (CartierDual.map f : CartierDual k C →ₐ[k] CartierDual k D) = T := by
    refine AlgHom.ext_of_adjoin_eq_top hgen fun φ hφ => ?_
    refine CartierDual.ext_apply fun x => ?_
    change CartierDual.map f φ x = T φ x
    rw [CartierDual.map_apply, hT, hzero φ hφ x, hone φ hφ, zero_mul]
  refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
  have h1 : CartierDual.map f φ d = T φ d := by
    rw [← hM]; rfl
  rw [CartierDual.map_apply, hT] at h1
  rw [h1, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.HeightOneHom
