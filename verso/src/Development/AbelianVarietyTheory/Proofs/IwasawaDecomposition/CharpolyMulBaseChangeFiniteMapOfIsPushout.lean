import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapNormCoeff

noncomputable section

namespace GlobalTheory.NormalDescent

open CategoryTheory Polynomial TensorProduct

/- English proof (translation)
Use `algebraize [φ, α, β, φ', φ'.comp α]`. Establish `: IsScalarTower A B B'` using `IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm`. Establish `P : Algebra.IsPushout A B A' B'` using `CommRingCat.isPushout_iff_isPushout.1 H`. Establish `hb : IsBaseChange A' (IsScalarTower.toAlgHom A B B').toLinearMap` using `P.symm.out`. Use `haveI : Module.Finite A B := hφ`.

Use `haveI : Module.Finite A' B' := hφ'`. Use `letI : Algebra K K' := ι.toAlgebra`. Use `letI : Algebra A K' := (ι.comp (algebraMap A K)).toAlgebra`. Use `haveI : IsScalarTower A K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : IsScalarTower A A' K' := IsScalarTower.of_algebraMap_eq fun a => hι a`.

Set `e : K' ⊗[K] (K ⊗[A] B) ≃ₗ[K'] K' ⊗[A'] B'` to `AlgebraTensorModule.cancelBaseChange A K K' K' B ≪≫ₗ (AlgebraTensorModule.cancelBaseChange A A' K' K' B).symm ≪≫ₗ AlgebraTensorModule.congr (LinearEquiv.refl K' K') hb.equiv`. Unfold `charK`. Express the relevant statement in the definitionally equal form `(Algebra.lmul K' (K' ⊗[A'] B') (1 ⊗ₜ β b)).charpoly = (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)).charpoly.map (algebraMap K K')`. Rewrite using `[← LinearMap.charpoly_baseChange, ← e.charpoly_conj]`. Use `congr 1`.

Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Take `⟨t, rfl⟩` from `e.surjective y`. Simplify using `only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add s t hs ht => simp only [map_add, hs, ht]`. Consider the case `tmul c' u`. Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add s t hs ht => simp only [tmul_add, map_add, hs, ht]`.

Consider the case `tmul c x`. Simplify using `[e, IsBaseChange.equiv_tmul]`. Both sides reduce to the same expression.
-/
theorem charK_map_of_isPushout {A B A' B' K K' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Field K] [Field K'] [Algebra A K] [Algebra A' K'] (φ : A →+* B) (α : A →+* A') (β : B →+* B')
    (φ' : A' →+* B')
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ'))
    (hφ : φ.Finite) (hφ' : φ'.Finite) (ι : K →+* K')
    (hι : ∀ a : A, ι (algebraMap A K a) = algebraMap A' K' (α a)) (b : B) :
    charK φ' hφ' K' (β b) = (charK φ hφ K b).map ι := by
  algebraize [φ, α, β, φ', φ'.comp α]
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm
  have P : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.1 H
  have hb : IsBaseChange A' (IsScalarTower.toAlgHom A B B').toLinearMap := P.symm.out
  haveI : Module.Finite A B := hφ
  haveI : Module.Finite A' B' := hφ'
  letI : Algebra K K' := ι.toAlgebra
  letI : Algebra A K' := (ι.comp (algebraMap A K)).toAlgebra
  haveI : IsScalarTower A K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A A' K' := IsScalarTower.of_algebraMap_eq fun a => hι a
  let e : K' ⊗[K] (K ⊗[A] B) ≃ₗ[K'] K' ⊗[A'] B' :=
    AlgebraTensorModule.cancelBaseChange A K K' K' B ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange A A' K' K' B).symm ≪≫ₗ
      AlgebraTensorModule.congr (LinearEquiv.refl K' K') hb.equiv
  unfold charK
  change (Algebra.lmul K' (K' ⊗[A'] B') (1 ⊗ₜ β b)).charpoly =
    (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)).charpoly.map (algebraMap K K')
  rw [← LinearMap.charpoly_baseChange, ← e.charpoly_conj]
  congr 1
  refine LinearMap.ext fun y => ?_
  obtain ⟨t, rfl⟩ := e.surjective y
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul c' u =>
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [tmul_add, map_add, hs, ht]
    | tmul c x =>
      simp [e, IsBaseChange.equiv_tmul]
      rfl

end GlobalTheory.NormalDescent
