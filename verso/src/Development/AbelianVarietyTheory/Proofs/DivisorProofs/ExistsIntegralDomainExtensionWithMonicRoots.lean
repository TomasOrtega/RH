import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `D _ _`. Establish `hDL : Function.Injective (algebraMap D (AlgebraicClosure (FractionRing D)))`. Rewrite using `[IsScalarTower.algebraMap_eq D (FractionRing D) (AlgebraicClosure (FractionRing D))]`. Conclude with `(algebraMap (FractionRing D) (AlgebraicClosure (FractionRing D))).injective.comp (IsFractionRing.injective D (FractionRing D))`. Establish `hCL : Function.Injective (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D))) (AlgebraicClosure (FractionRing D)))` using `Subtype.val_injective`.

Use `⟨integralClosure D (AlgebraicClosure (FractionRing D)), inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Apply `hDL` to reduce the goal to its premises. Simplify using `using congrArg Subtype.val hab`. Introduce `f hf hdeg`.

Establish `hdeg' : (f.map (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D))) (AlgebraicClosure (FractionRing D)))).degree ≠ 0`. Rewrite using `[degree_map_eq_of_injective hCL, degree_eq_natDegree hf.ne_zero]`. Conclude with `hdeg.ne'` after adjusting the coercions. Take `⟨y, hy⟩` from `IsAlgClosed.exists_root _ hdeg'`. Establish `hy' : f.eval₂ (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D))) (AlgebraicClosure (FractionRing D))) y = 0` using `by rwa [IsRoot, eval_map] at hy`.

Establish `hyC : IsIntegral (integralClosure D (AlgebraicClosure (FractionRing D))) y` using `⟨f, hf, hy'⟩`. Establish `hyD : IsIntegral D y` using `isIntegral_trans y hyC`. Use `⟨⟨y, hyD⟩, ?_⟩` and prove the remaining obligations. Apply `hCL` to reduce the goal to its premises. Rewrite using `[← eval₂_at_apply, map_zero]`.

Conclude with `hy'`. Introduce `K _ _ h hinj`. Use `letI : Algebra (FractionRing D) K := (IsFractionRing.lift hinj : FractionRing D →+* K).toAlgebra`. Set `φ : AlgebraicClosure (FractionRing D) →ₐ[FractionRing D] K` to `IsAlgClosed.lift`. Use `⟨φ.toRingHom.comp (integralClosure D (AlgebraicClosure (FractionRing D))).val.toRingHom, φ.toRingHom.injective.comp Subtype.val_injective, ?_⟩` and prove the remaining obligations.

Use extensionality with `a`. Use `show φ (algebraMap D (AlgebraicClosure (FractionRing D)) a) = h a`. Rewrite using `[IsScalarTower.algebraMap_apply D (FractionRing D) (AlgebraicClosure (FractionRing D)), AlgHom.commutes]`. Conclude with `IsFractionRing.lift_algebraMap hinj a`.
-/
theorem exists_integral_domain_extension_monic_roots :
    ∀ (D : Type) [CommRing D] [IsDomain D], ∃ (C : Type) (_ : CommRing C) (_ : Algebra D C),
      IsDomain C ∧ Algebra.IsIntegral D C ∧ Function.Injective (algebraMap D C) ∧
      (∀ f : C[X], f.Monic → 0 < f.natDegree → ∃ y : C, f.eval y = 0) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (h : D →+* K), Function.Injective h →
        ∃ e : C →+* K, Function.Injective e ∧ e.comp (algebraMap D C) = h := by
  intro D _ _
  have hDL : Function.Injective (algebraMap D (AlgebraicClosure (FractionRing D))) := by
    rw [IsScalarTower.algebraMap_eq D (FractionRing D) (AlgebraicClosure (FractionRing D))]
    exact (algebraMap (FractionRing D) (AlgebraicClosure (FractionRing D))).injective.comp
      (IsFractionRing.injective D (FractionRing D))
  have hCL : Function.Injective (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D)))
      (AlgebraicClosure (FractionRing D))) := Subtype.val_injective
  refine ⟨integralClosure D (AlgebraicClosure (FractionRing D)), inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro a b hab
    apply hDL
    simpa using congrArg Subtype.val hab
  · intro f hf hdeg
    have hdeg' : (f.map (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D)))
        (AlgebraicClosure (FractionRing D)))).degree ≠ 0 := by
      rw [degree_map_eq_of_injective hCL, degree_eq_natDegree hf.ne_zero]
      exact_mod_cast hdeg.ne'
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg'
    have hy' : f.eval₂ (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D)))
        (AlgebraicClosure (FractionRing D))) y = 0 := by rwa [IsRoot, eval_map] at hy
    have hyC : IsIntegral (integralClosure D (AlgebraicClosure (FractionRing D))) y :=
      ⟨f, hf, hy'⟩
    have hyD : IsIntegral D y := isIntegral_trans y hyC
    refine ⟨⟨y, hyD⟩, ?_⟩
    apply hCL
    rw [← eval₂_at_apply, map_zero]
    exact hy'
  · intro K _ _ h hinj
    letI : Algebra (FractionRing D) K := (IsFractionRing.lift hinj : FractionRing D →+* K).toAlgebra
    let φ : AlgebraicClosure (FractionRing D) →ₐ[FractionRing D] K := IsAlgClosed.lift
    refine ⟨φ.toRingHom.comp (integralClosure D (AlgebraicClosure (FractionRing D))).val.toRingHom,
      φ.toRingHom.injective.comp Subtype.val_injective, ?_⟩
    ext a
    show φ (algebraMap D (AlgebraicClosure (FractionRing D)) a) = h a
    rw [IsScalarTower.algebraMap_apply D (FractionRing D) (AlgebraicClosure (FractionRing D)),
      AlgHom.commutes]
    exact IsFractionRing.lift_algebraMap hinj a

end GlobalTheory
