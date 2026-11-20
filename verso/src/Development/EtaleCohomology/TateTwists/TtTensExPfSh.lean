import Development.EtaleCohomology.TateTwists.TtTensExPfLoc

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations

variable {R : Type} [CommRing R]

noncomputable section

abbrev shK {I J : Cx R} (T : TensPre I J) : Cx R :=
  ((presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj T.P

abbrev tS {I J : Cx R} (T : TensPre I J) (U : Scheme.{0}) (w : ℤ) :
    Tens I J U w →ₗ[ULift.{1} R] Sec ((shK T).X w) U :=
  ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op U)).hom ∘ₗ (T.e U w).toLinearMap

/- English proof (translation)
Establish `h1` using `ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).naturality g.op) (T.e U w x)`. Simplify using `only [ConcreteCategory.comp_apply] at h1`. Use `show Sec.res g (((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op U)).hom (T.e U w x)) = ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op V)).hom (T.e V w (Tens.res g w x))`. Rewrite using `[T.nat]`. Conclude with `h1.symm`.
-/
theorem tS_nat {I J : Cx R} (T : TensPre I J) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    Sec.res g (tS T U w x) = tS T V w (Tens.res g w x) := by
  have h1 := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).naturality g.op) (T.e U w x)
  simp only [ConcreteCategory.comp_apply] at h1
  show Sec.res g (((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op U)).hom (T.e U w x)) =
    ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op V)).hom (T.e V w (Tens.res g w x))
  rw [T.nat]
  exact h1.symm

/- English proof (translation)
Simplify using `only [tS, LinearMap.comp_apply, LinearEquiv.coe_coe]`. Conclude with `(ConcreteCategory.congr_hom (congrArg (fun f => NatTrans.app f (op U)) (toSheafify_naturality Scheme.etaleTopology.{0} (T.P.d w (w + 1)))) _).symm`.
-/
theorem tS_d {I J : Cx R} (T : TensPre I J) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    Sec.map ((shK T).d w (w + 1)) (tS T U w x) =
      ((toSheafify Scheme.etaleTopology.{0} (T.P.X (w + 1))).app (op U)).hom
        (((T.P.d w (w + 1)).app (op U)).hom (T.e U w x)) := by
  simp only [tS, LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact (ConcreteCategory.congr_hom (congrArg (fun f => NatTrans.app f (op U))
    (toSheafify_naturality Scheme.etaleTopology.{0} (T.P.d w (w + 1)))) _).symm

def shPair {I J : Cx R} (T : TensPre I J) : Pair I J (shK T) where
  mul U s t w h := (TensorProduct.mk _ _ _).compr₂ (tS T U w ∘ₗ DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w} (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩)
  nat g s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.comp_apply, tS_nat]
    congr 1
    rw [Tens.res, DirectSum.lmap_lof, TensorProduct.map_tmul]
  leibniz U s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.comp_apply, DirectSum.lof_eq_of]
    rw [tS_d, T.leibniz]
    rw [map_add, Units.smul_def, Units.smul_def, map_zsmul]
    rfl

/- English proof (translation)
Apply `DirectSum.linearMap_ext` to reduce the goal to its premises. Introduce `p`. Apply `TensorProduct.ext'` to reduce the goal to its premises. Introduce `a b`. Simplify using `[Pair.lift, shPair, DirectSum.toModule_lof]`.
-/
theorem shPair_lift {I J : Cx R} (T : TensPre I J) (U : Scheme.{0}) (w : ℤ) :
    (shPair T).lift U w = tS T U w := by
  classical
  apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
  simp [Pair.lift, shPair, DirectSum.toModule_lof]

/- English proof (translation)
Use `⟨fun U w y => ?_, fun U w x hx => ?_⟩` and prove the remaining obligations. Take `⟨S, hS, hP⟩` from `tt_sheafify_locSurj (T.P.X w) U y`. Use `⟨S, hS, fun V g hg => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `hP V g hg`. Use `⟨(T.e V w).symm x, ?_⟩` and prove the remaining obligations.

Rewrite using `[shPair_lift]`. Use `show ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op V)).hom (T.e V w ((T.e V w).symm x)) = _`. Rewrite using `[LinearEquiv.apply_symm_apply]`. Conclude with `hx`. Rewrite `hx` using `[shPair_lift]`.

Take `⟨S, hS, hP⟩` from `tt_sheafify_locInj (T.P.X w) U (T.e U w x) hx`. Use `⟨S, hS, fun V g hg => ?_⟩` and prove the remaining obligations. Establish `h2` using `hP V g hg`. Simplify using `only at h2 ⊢`. Rewrite `h2` using `[← T.nat]`.

Conclude with `(LinearEquiv.map_eq_zero_iff _).mp h2`.
-/
theorem shPair_isTensor {I J : Cx R} (T : TensPre I J) : (shPair T).IsTensor := by
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · obtain ⟨S, hS, hP⟩ := tt_sheafify_locSurj (T.P.X w) U y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hP V g hg
    refine ⟨(T.e V w).symm x, ?_⟩
    rw [shPair_lift]
    show ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op V)).hom (T.e V w ((T.e V w).symm x)) = _
    rw [LinearEquiv.apply_symm_apply]
    exact hx
  · rw [shPair_lift] at hx
    obtain ⟨S, hS, hP⟩ := tt_sheafify_locInj (T.P.X w) U (T.e U w x) hx
    refine ⟨S, hS, fun V g hg => ?_⟩
    have h2 := hP V g hg
    simp only at h2 ⊢
    rw [← T.nat] at h2
    exact (LinearEquiv.map_eq_zero_iff _).mp h2

/- English proof (translation)
Introduce `_ _ _ _ T` and use `⟨_, shPair T, shPair_isTensor T⟩`.
-/
theorem etale_presheaf_tensor_data_sheafification_is_tensor_complex : tt_tens_sheafify := fun _ _ _ _ T => ⟨_, shPair T, shPair_isTensor T⟩

end

end LateralTheory.EtaleFoundations
