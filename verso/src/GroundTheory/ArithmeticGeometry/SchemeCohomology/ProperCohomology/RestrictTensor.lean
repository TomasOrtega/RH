import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory TensorProduct

universe u

noncomputable section

namespace RestrictTensor

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) (U : X.Opens)

def ringInv : ringOn X U →+* ringOn Y (f ''ᵁ U) := (f.appIso U).inv.hom

def ringHom : ringOn Y (f ''ᵁ U) →+* ringOn X U := (f.appIso U).hom.hom

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(f.appIso U).inv ((f.appIso U).hom r) = r`. Conclude with `(f.appIso U).hom_inv_id_apply r`.
-/
lemma ringInv_ringHom (r : ringOn Y (f ''ᵁ U)) : ringInv f U (ringHom f U r) = r := by
  change (f.appIso U).inv ((f.appIso U).hom r) = r
  exact (f.appIso U).hom_inv_id_apply r

def sec : ((preMod X).obj (M.restrict f)).obj (op U) →+ ((preMod Y).obj M).obj (op (f ''ᵁ U)) :=
  AddMonoidHom.id _

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma sec_smul (r : ringOn X U) (m : ((preMod X).obj (M.restrict f)).obj (op U)) :
    sec f M U (r • m) = ringInv f U r • sec f M U m := rfl

def sec' : ((preMod Y).obj M).obj (op (f ''ᵁ U)) →+ ((preMod X).obj (M.restrict f)).obj (op U) :=
  AddMonoidHom.id _

/- English proof (translation)
Express the relevant statement in the definitionally equal form `r • m = ringInv f U (ringHom f U r) • m`. Rewrite using `[ringInv_ringHom]`.
-/
lemma sec'_smul (r : ringOn Y (f ''ᵁ U)) (m : ((preMod Y).obj M).obj (op (f ''ᵁ U))) :
    sec' f M U (r • m) = ringHom f U r • sec' f M U m := by
  change r • m = ringInv f U (ringHom f U r) • m
  rw [ringInv_ringHom]

def toImage :
    ((preMod X).obj (M.restrict f)).obj (op U) ⊗[ringOn X U] ((preMod X).obj (N.restrict f)).obj (op U) →+
      ((preMod Y).obj M).obj (op (f ''ᵁ U)) ⊗[ringOn Y (f ''ᵁ U)]
        ((preMod Y).obj N).obj (op (f ''ᵁ U)) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (fun n => sec f M U m ⊗ₜ sec f N U n)
      (fun a b => by rw [map_add, tmul_add]))
      (fun a b => by ext n; simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add,
        add_tmul]))
    (fun r m n => by
      simp only [AddMonoidHom.mk'_apply, sec_smul]
      exact smul_tmul _ _ _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma toImage_tmul (m : ((preMod X).obj (M.restrict f)).obj (op U))
    (n : ((preMod X).obj (N.restrict f)).obj (op U)) :
    toImage f M N U (m ⊗ₜ n) = sec f M U m ⊗ₜ sec f N U n := rfl

def ofImage :
    ((preMod Y).obj M).obj (op (f ''ᵁ U)) ⊗[ringOn Y (f ''ᵁ U)] ((preMod Y).obj N).obj (op (f ''ᵁ U)) →+
      ((preMod X).obj (M.restrict f)).obj (op U) ⊗[ringOn X U]
        ((preMod X).obj (N.restrict f)).obj (op U) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (fun n => sec' f M U m ⊗ₜ sec' f N U n)
      (fun a b => by rw [map_add, tmul_add]))
      (fun a b => by ext n; simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add,
        add_tmul]))
    (fun r m n => by
      simp only [AddMonoidHom.mk'_apply, sec'_smul]
      exact smul_tmul _ _ _)

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul m n => rfl`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`.
-/
lemma ofImage_toImage (z : ((preMod X).obj (M.restrict f)).obj (op U) ⊗[ringOn X U]
    ((preMod X).obj (N.restrict f)).obj (op U)) : ofImage f M N U (toImage f M N U z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul m n => rfl`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`.
-/
lemma toImage_ofImage (z : ((preMod Y).obj M).obj (op (f ''ᵁ U)) ⊗[ringOn Y (f ''ᵁ U)]
    ((preMod Y).obj N).obj (op (f ''ᵁ U))) : toImage f M N U (ofImage f M N U z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul m n`. Rewrite using `[TensorProduct.smul_tmul', toImage_tmul, toImage_tmul, sec_smul, TensorProduct.smul_tmul']`. Consider the case `add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, smul_add]`.
-/
lemma toImage_smul (r : ringOn X U) (z : ((preMod X).obj (M.restrict f)).obj (op U) ⊗[ringOn X U]
    ((preMod X).obj (N.restrict f)).obj (op U)) :
    toImage f M N U (r • z) = ringInv f U r • toImage f M N U z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    rw [TensorProduct.smul_tmul', toImage_tmul, toImage_tmul, sec_smul, TensorProduct.smul_tmul']
  | add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, smul_add]

def compApp : ((preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f)).obj (op U) →+
    ((preMod X).obj ((M ⊗ N).restrict f)).obj (op U) :=
  (sec' f (M ⊗ N) U).comp (((tensorToSheaf M N).app (op (f ''ᵁ U))).hom.toAddMonoidHom.comp
    (toImage f M N U))

/- English proof (translation)
Express the relevant statement in the definitionally equal form `sec' f (M ⊗ N) U ((tensorToSheaf M N).app (op (f ''ᵁ U)) (toImage f M N U (r • z))) = sec' f (M ⊗ N) U (ringInv f U r • (tensorToSheaf M N).app (op (f ''ᵁ U)) (toImage f M N U z))`. Conclude with `congrArg (sec' f (M ⊗ N) U) ((congrArg ((tensorToSheaf M N).app (op (f ''ᵁ U))).hom (toImage_smul f M N U r z)).trans (((tensorToSheaf M N).app (op (f ''ᵁ U))).hom.map_smul (ringInv f U r) (toImage f M N U z)))`.
-/
lemma compApp_smul (r : ringOn X U)
    (z : ((preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f)).obj (op U)) :
    compApp f M N U (r • z) = r • compApp f M N U z := by
  change sec' f (M ⊗ N) U ((tensorToSheaf M N).app (op (f ''ᵁ U)) (toImage f M N U (r • z))) =
    sec' f (M ⊗ N) U (ringInv f U r • (tensorToSheaf M N).app (op (f ''ᵁ U)) (toImage f M N U z))
  exact congrArg (sec' f (M ⊗ N) U) ((congrArg ((tensorToSheaf M N).app (op (f ''ᵁ U))).hom
    (toImage_smul f M N U r z)).trans
      (((tensorToSheaf M N).app (op (f ''ᵁ U))).hom.map_smul (ringInv f U r) (toImage f M N U z)))

def comp : (preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f) ⟶
    (preMod X).obj ((M ⊗ N).restrict f) :=
  PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (compApp f M N U.unop)
      naturality := fun U V g => by
        ext z
        let L := (compApp f M N V.unop).comp (((preMod X).obj (M.restrict f) ⊗
          (preMod X).obj (N.restrict f)).map g).hom.toAddMonoidHom
        let R := (((preMod X).obj ((M ⊗ N).restrict f)).map g).hom.toAddMonoidHom.comp
          (compApp f M N U.unop)
        change L z = R z
        induction z using TensorProduct.induction_on with
        | zero => exact (map_zero L).trans (map_zero R).symm
        | tmul m n =>
          exact PresheafOfModules.naturality_apply (tensorToSheaf M N)
            (f.opensFunctor.map g.unop).op (sec f M U.unop m ⊗ₜ sec f N U.unop n)
        | add a b ha hb =>
          exact (map_add L a b).trans ((congrArg₂ (· + ·) ha hb).trans (map_add R a b).symm) }
    (fun U r z => compApp_smul f M N U.unop r z)

/- English proof (translation)
Set `L` to `(toImage f M N V).comp (((preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f)).map (homOfLE h).op).hom.toAddMonoidHom`. Set `R` to `(((preMod Y).obj M ⊗ (preMod Y).obj N).map (homOfLE (f.image_mono h)).op).hom.toAddMonoidHom.comp (toImage f M N U)`. Express the relevant statement in the definitionally equal form `L z = R z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact (map_zero L).trans (map_zero R).symm`.

Consider the case `tmul m n => rfl`. Consider the case `add a b ha hb => exact (map_add L a b).trans ((congrArg₂ (· + ·) ha hb).trans (map_add R a b).symm)`.
-/
lemma toImage_map {U V : X.Opens} (h : V ≤ U)
    (z : ((preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f)).obj (op U)) :
    toImage f M N V (((preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f)).map
      (homOfLE h).op z) =
      (((preMod Y).obj M ⊗ (preMod Y).obj N).map (homOfLE (f.image_mono h)).op (toImage f M N U z)) := by
  let L := (toImage f M N V).comp (((preMod X).obj (M.restrict f) ⊗
    (preMod X).obj (N.restrict f)).map (homOfLE h).op).hom.toAddMonoidHom
  let R := (((preMod Y).obj M ⊗ (preMod Y).obj N).map
    (homOfLE (f.image_mono h)).op).hom.toAddMonoidHom.comp (toImage f M N U)
  change L z = R z
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero L).trans (map_zero R).symm
  | tmul m n => rfl
  | add a b ha hb => exact (map_add L a b).trans ((congrArg₂ (· + ·) ha hb).trans (map_add R a b).symm)

/- English proof (translation)
Take `⟨hT₁, hT₂⟩` from `(ModulesTensor.W_toPresheaf_iff (tensorToSheaf M N)).1 (W_tensorToSheaf M N)`. Rewrite using `[ModulesTensor.W, MorphismProperty.inverseImage_iff, ModulesTensor.W_toPresheaf_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `U z hz`. Establish `h0 : (tensorToSheaf M N).app (op (f ''ᵁ U.unop)) (toImage f M N U.unop z) = 0` using `hz`.

Establish `hS` using `hT₁ (op (f ''ᵁ U.unop)) _ h0`. Rewrite `hS`, the goal using `[Opens.mem_grothendieckTopology]`. Introduce `x hx`. Take `⟨W', i, hi, hxW'⟩` from `hS (f x) ⟨x, hx, rfl⟩`. Establish `hVU : f ⁻¹ᵁ W' ≤ U.unop`.

Rewrite using `[← f.preimage_image_eq U.unop]`. Conclude with `f.preimage_mono i.le`. Use `⟨f ⁻¹ᵁ W', homOfLE hVU, ?_, hxW'⟩` and prove the remaining obligations. Establish `hi' : ((preMod Y).obj M ⊗ (preMod Y).obj N).map (homOfLE (f.image_mono hVU)).op (toImage f M N U.unop z) = 0` using `(ModulesTensor.zeroSieve _).downward_closed hi (homOfLE (f.image_preimage_le W'))`. Express the relevant statement in the definitionally equal form `(((preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f)).map (homOfLE hVU).op z) = 0`.

Rewrite using `[← ofImage_toImage f M N (f ⁻¹ᵁ W') (((preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f)).map (homOfLE hVU).op z), toImage_map]`. Use `erw [hi', map_zero]`. Both sides reduce to the same expression. Introduce `U y`. Establish `hS` using `hT₂ (op (f ''ᵁ U.unop)) y`.

Rewrite `hS`, the goal using `[Opens.mem_grothendieckTopology]`. Introduce `x hx`. Take `⟨W', i, hi, hxW'⟩` from `hS (f x) ⟨x, hx, rfl⟩`. Establish `hVU : f ⁻¹ᵁ W' ≤ U.unop`. Rewrite using `[← f.preimage_image_eq U.unop]`.

Conclude with `f.preimage_mono i.le`. Use `⟨f ⁻¹ᵁ W', homOfLE hVU, ?_, hxW'⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `(ModulesTensor.imSieve _ _).downward_closed hi (homOfLE (f.image_preimage_le W'))`. Use `⟨ofImage f M N (f ⁻¹ᵁ W') w, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `sec' f (M ⊗ N) _ ((tensorToSheaf M N).app _ (toImage f M N (f ⁻¹ᵁ W') (ofImage f M N (f ⁻¹ᵁ W') w))) = _`.

Use `erw [toImage_ofImage]`. Conclude with `hw`.
-/
lemma W_comp : ModulesTensor.W (Opens.grothendieckTopology X) X.sheaf.obj (comp f M N) := by
  obtain ⟨hT₁, hT₂⟩ := (ModulesTensor.W_toPresheaf_iff (tensorToSheaf M N)).1 (W_tensorToSheaf M N)
  rw [ModulesTensor.W, MorphismProperty.inverseImage_iff, ModulesTensor.W_toPresheaf_iff]
  constructor
  · intro U z hz
    have h0 : (tensorToSheaf M N).app (op (f ''ᵁ U.unop)) (toImage f M N U.unop z) = 0 := hz
    have hS := hT₁ (op (f ''ᵁ U.unop)) _ h0
    rw [Opens.mem_grothendieckTopology] at hS ⊢
    intro x hx
    obtain ⟨W', i, hi, hxW'⟩ := hS (f x) ⟨x, hx, rfl⟩
    have hVU : f ⁻¹ᵁ W' ≤ U.unop := by
      rw [← f.preimage_image_eq U.unop]
      exact f.preimage_mono i.le
    refine ⟨f ⁻¹ᵁ W', homOfLE hVU, ?_, hxW'⟩
    have hi' : ((preMod Y).obj M ⊗ (preMod Y).obj N).map (homOfLE (f.image_mono hVU)).op
        (toImage f M N U.unop z) = 0 :=
      (ModulesTensor.zeroSieve _).downward_closed hi (homOfLE (f.image_preimage_le W'))
    change (((preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f)).map
      (homOfLE hVU).op z) = 0
    rw [← ofImage_toImage f M N (f ⁻¹ᵁ W') (((preMod X).obj (M.restrict f) ⊗
      (preMod X).obj (N.restrict f)).map (homOfLE hVU).op z), toImage_map]
    erw [hi', map_zero]
    rfl
  · intro U y
    have hS := hT₂ (op (f ''ᵁ U.unop)) y
    rw [Opens.mem_grothendieckTopology] at hS ⊢
    intro x hx
    obtain ⟨W', i, hi, hxW'⟩ := hS (f x) ⟨x, hx, rfl⟩
    have hVU : f ⁻¹ᵁ W' ≤ U.unop := by
      rw [← f.preimage_image_eq U.unop]
      exact f.preimage_mono i.le
    refine ⟨f ⁻¹ᵁ W', homOfLE hVU, ?_, hxW'⟩
    obtain ⟨w, hw⟩ := (ModulesTensor.imSieve _ _).downward_closed hi
      (homOfLE (f.image_preimage_le W'))
    refine ⟨ofImage f M N (f ⁻¹ᵁ W') w, ?_⟩
    change sec' f (M ⊗ N) _ ((tensorToSheaf M N).app _
      (toImage f M N (f ⁻¹ᵁ W') (ofImage f M N (f ⁻¹ᵁ W') w))) = _
    erw [toImage_ofImage]
    exact hw

def sheafifyIso : (sheafifyMod X).obj ((preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f)) ≅
    (M ⊗ N).restrict f :=
  haveI : IsIso ((sheafifyMod X).map (comp f M N)) :=
    Localization.inverts (modulesSheafification (Opens.grothendieckTopology X) X.sheaf)
      (ModulesTensor.W (Opens.grothendieckTopology X) X.sheaf.obj) _ (W_comp f M N)
  asIso ((sheafifyMod X).map (comp f M N)) ≪≫ asIso ((sheafifyModAdj X).counit.app _)

end RestrictTensor

open RestrictTensor in

def restrictTensorIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) :
    (M ⊗ N).restrict f ≅ M.restrict f ⊗ N.restrict f :=
  (sheafifyIso f M N).symm ≪≫ tensorIso (M.restrict f) (N.restrict f)

attribute [local instance] MvPolynomial.gradedAlgebra in

def restrictTwistIso {A : Type u} [CommRing A] {n : ℕ} {U X : Scheme.{u}} (f : U ⟶ X)
    [IsOpenImmersion f] (i : X ⟶ projectiveSpace A n) (G : X.Modules) (k : ℤ) :
    ProjScheme.twist (f ≫ i) (G.restrict f) k ≅ (ProjScheme.twist i G k).restrict f :=
  (whiskerLeftIso (G.restrict f)
    (((Scheme.Modules.pullbackComp f i).app _).symm ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback f).app _).symm)) ≪≫
    (restrictTensorIso f G (ProjScheme.twistingSheaf i k)).symm

end

end GroundTheory.Arith.SchemeCoh
