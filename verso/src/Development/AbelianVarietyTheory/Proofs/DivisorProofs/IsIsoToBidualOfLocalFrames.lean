import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory TopologicalSpace Opposite
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB
open GlobalTheory.VB
open GlobalTheory.Twist (resM resM_self app_resM)
open GlobalTheory.QCoh (appLinear freeModule)

namespace GlobalTheory.OmegaGlobal

/- English proof (translation)
Establish `h : (R.map : (X ⟶ Y) → _) = adj.homEquiv _ _ ∘ fun φ => adj.counit.app X ≫ φ`. Use function extensionality and compare the values at `φ`. Simplify using `[Adjunction.homEquiv_unit]`. Rewrite using `[h]`. Conclude with `(adj.homEquiv _ _).bijective.comp ((asIso (adj.counit.app X)).homFromEquiv (Z := Y)).symm.bijective`.
-/
theorem map_bijective_of_isIso_counit {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) (X Y : D) [IsIso (adj.counit.app X)] :
    Function.Bijective (R.map : (X ⟶ Y) → _) := by
  have h : (R.map : (X ⟶ Y) → _) = adj.homEquiv _ _ ∘ fun φ => adj.counit.app X ≫ φ := by
    funext φ
    simp [Adjunction.homEquiv_unit]
  rw [h]
  exact (adj.homEquiv _ _).bijective.comp
    ((asIso (adj.counit.app X)).homFromEquiv (Z := Y)).symm.bijective

section Frames

variable {X : Scheme.{0}} {F : X.Modules}

/- English proof (translation)
Use `choose U n e hx he using h`. Use `Twist.isIso_of_cover _ (U := U) (top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩) fun x W hW => ?_` and prove the remaining obligations. Establish `: appLinear (cartierDualToBidual F) W = ((he x).equiv (he x).dual.dual hW).toLinearMap` using `((he x).basis hW).ext fun i => by`. Rewrite using `[IsFrame.basis_apply, LinearEquiv.coe_coe, IsFrame.equiv_resM_frame, ← (he x).toBidual_app]`. Conclude with `app_resM (cartierDualToBidual F) hW (e x i)`.

Rewrite using `[← QCoh.coe_appLinear, this]`. Conclude with `((he x).equiv (he x).dual.dual hW).bijective`.
-/
theorem isIso_toBidual_of_local_frames (h : ∀ x : X, ∃ (U : X.Opens) (n : ℕ) (e : Fin n → Γ(F, U)),
    x ∈ U ∧ IsFrame e) : IsIso (cartierDualToBidual F) := by
  choose U n e hx he using h
  refine Twist.isIso_of_cover _ (U := U) (top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩)
    fun x W hW => ?_
  have : appLinear (cartierDualToBidual F) W = ((he x).equiv (he x).dual.dual hW).toLinearMap :=
    ((he x).basis hW).ext fun i => by
      rw [IsFrame.basis_apply, LinearEquiv.coe_coe, IsFrame.equiv_resM_frame,
        ← (he x).toBidual_app]
      exact app_resM (cartierDualToBidual F) hW (e x i)
  rw [← QCoh.coe_appLinear, this]
  exact ((he x).equiv (he x).dual.dual hW).bijective

/- English proof (translation)
Use `choose U n e hx he using h`. Use `QCoh.isQuasicoherent_of_restrict F (fun x => (U x).ι) (fun x => ⟨x, by simpa using hx x⟩) fun x => ?_` and prove the remaining obligations. Use `(isVB_freeModule (U x).toScheme (Fin (n x))).isQuasicoherent` as an intermediate fact. Conclude with `QCoh.isQuasicoherent_of_iso ((isFrame_freeFrame _ _).iso ((isFrame_restrict_iff (U x).ι _).2 ((he x).res ((U x).ι_image_le ⊤))))`.
-/
theorem isQuasicoherent_of_frames (h : ∀ x : X, ∃ (U : X.Opens) (n : ℕ) (e : Fin n → Γ(F, U)),
    x ∈ U ∧ IsFrame e) : F.IsQuasicoherent := by
  choose U n e hx he using h
  refine QCoh.isQuasicoherent_of_restrict F (fun x => (U x).ι)
    (fun x => ⟨x, by simpa using hx x⟩) fun x => ?_
  have := (isVB_freeModule (U x).toScheme (Fin (n x))).isQuasicoherent
  exact QCoh.isQuasicoherent_of_iso ((isFrame_freeFrame _ _).iso
      ((isFrame_restrict_iff (U x).ι _).2 ((he x).res ((U x).ι_image_le ⊤))))

end Frames

/- English proof (translation)
Establish `: IsIso ((tilde.adjunction (R` using `.of O)).counit.app F) := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of O) F`. Establish `h` using `map_bijective_of_isIso_counit (tilde.adjunction (R := .of O)) F (structureModule (Sp O))`. Prove the components needed by the constructor for the conclusion. Introduce `l l' e`. Apply `(homGlobalEquiv F _).injective` to reduce the goal to its premises.

Apply `h.1` to reduce the goal to its premises. Use extensionality with `s`. Conclude with `congr($e s)`. Introduce `f`. Set `g : (moduleSpecΓFunctor (R` to `.of O)).obj F →ₗ[CommRingCat.of O] (moduleSpecΓFunctor (R := .of O)).obj (structureModule (Sp O)) := { toFun := f map_add' := f.map_add map_smul' := fun a s => f.map_smul ((Sp O).presheaf.map (Opens.leTop ⊤).op ((Scheme.ΓSpecIso (.of O)).inv a)) s }`.

Take `⟨φ, hφ⟩` from `h.2 (ConcreteCategory.ofHom (C := ModuleCat (CommRingCat.of O)) g)`. Use `⟨(homGlobalEquiv F _).symm φ, LinearMap.ext fun s => ?_⟩` and prove the remaining obligations. Conclude with `congr($hφ s)`.
-/
theorem dualApp_top_bijective {O : Type} [CommRing O] (F : (Sp O).Modules) [F.IsQuasicoherent] :
    Function.Bijective fun l : Γ(dual F, ⊤) => dualApp l (le_refl ⊤) := by
  have : IsIso ((tilde.adjunction (R := .of O)).counit.app F) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of O) F
  have h := map_bijective_of_isIso_counit (tilde.adjunction (R := .of O)) F
    (structureModule (Sp O))
  constructor
  · intro l l' e
    apply (homGlobalEquiv F _).injective
    apply h.1
    ext s
    exact congr($e s)
  · intro f
    let g : (moduleSpecΓFunctor (R := .of O)).obj F →ₗ[CommRingCat.of O]
        (moduleSpecΓFunctor (R := .of O)).obj (structureModule (Sp O)) :=
      { toFun := f
        map_add' := f.map_add
        map_smul' := fun a s => f.map_smul
          ((Sp O).presheaf.map (Opens.leTop ⊤).op ((Scheme.ΓSpecIso (.of O)).inv a)) s }
    obtain ⟨φ, hφ⟩ := h.2 (ConcreteCategory.ofHom (C := ModuleCat (CommRingCat.of O)) g)
    refine ⟨(homGlobalEquiv F _).symm φ, LinearMap.ext fun s => ?_⟩
    exact congr($hφ s)

variable {O : Type} [CommRing O] {G : Over (Sp O)} [GrpObj G]

/- English proof (translation)
Rewrite using `[comp_mul, x.2, y.2]`. Conclude with `_root_.mul_one (1 : specO O O ⟶ G)`.
-/
theorem fst_mul (x y : LieG G) : ptMap (TrivSqZeroExt.fstHom O O O) ≫ (x.1 * y.1) =
    toUnit (specO O O) ≫ η[G] := by
  rw [comp_mul, x.2, y.2]
  exact _root_.mul_one (1 : specO O O ⟶ G)

/- English proof (translation)
Use `Eq.trans ?_ x.2` and prove the remaining obligations. Rewrite using `[← Category.assoc]`. Use `congr 1`. Use `ext1`. Express the relevant statement in the definitionally equal form `Spec.map _ ≫ Spec.map _ = Spec.map _`.

Rewrite using `[← Spec.map_comp]`. Use `congr 1`. Apply the tactic sequence `ext y <;> simp [dualScale]`.
-/
theorem fst_scale (a : O) (x : LieG G) : ptMap (TrivSqZeroExt.fstHom O O O) ≫
    (ptMap (dualScale a) ≫ x.1) = toUnit (specO O O) ≫ η[G] := by
  refine Eq.trans ?_ x.2
  rw [← Category.assoc]
  congr 1
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext y <;> simp [dualScale]

/- English proof (translation)
Establish `h₁` using `isIso_toBidual_of_local_frames (exists_isFrame_omega G)`. Establish `h₂ : (Lie G).IsQuasicoherent` using `isQuasicoherent_of_frames fun x =>`. Establish `⟨U, n, _, hx, he⟩` using `exists_isFrame_omega G x`. Use the proof step `⟨U, n, _, hx, he.dual⟩`. Establish `h₃` using `(dualApp_top_bijective (Lie G)).comp (ConcreteCategory.bijective_of_isIso ((cartierDualToBidual (LieVB.omega G)).app ⊤))`.

Establish `key (w : Γ(LieVB.omega G, ⊤)) (l : Γ(Lie G, ⊤)) : dualApp ((cartierDualToBidual (LieVB.omega G)).app ⊤ w) (le_refl ⊤) l = dualApp l le_top w`. Rewrite using `[dualSheafSectionApply_toBidual, resM_self]`. Establish `hc` using `ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of O)).hom`. Establish `hc'` using `ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of O)).inv`. Prove the components needed by the constructor for the conclusion.

Introduce `w w' e`. Use `h₃.1 (LinearMap.ext fun l => ?_)` and prove the remaining obligations. Take `⟨x, rfl⟩` from `ht.2 l`. Conclude with `(key w _).trans ((hc.1 congr(($e).1 x)).trans (key w' _).symm)`. Introduce and unpack `⟨f, hf₁, hf₂⟩`.

Set `t` to `Equiv.ofBijective _ ht`. Establish `ht' (x : LieG G) : t.symm (tangent x) = x` using `t.symm_apply_apply x`. Set `g : Γ(Lie G, ⊤) →ₗ[Γ(Sp O, ⊤)] Γ(Sp O, ⊤)` to `{ toFun := fun l => cst O (f (t.symm l)) map_add' := fun l l' => by`. Take `⟨x, rfl⟩` from `ht.2 l`. Take `⟨y, rfl⟩` from `ht.2 l'`.

Rewrite using `[← tangent_mul x y (fst_mul x y), ht' x, ht' y, ← map_add, ← hf₁ x y (fst_mul x y)]`. Conclude with `congrArg (fun y => cst O (f y)) (ht' _)`. Use the proof step `map_smul' := fun a l => by`. Take `⟨x, rfl⟩` from `ht.2 l`. Take `⟨a, rfl⟩ : ∃ b, cst O b = a` from `hc'.2 a`.

Rewrite using `[← tangent_scale a x (fst_scale a x), ht' x, RingHom.id_apply, smul_eq_mul, ← map_mul, ← hf₂ a x (fst_scale a x)]`. Conclude with `congrArg (fun y => cst O (f y)) (ht' _) }`. Take `⟨w, hw⟩` from `h₃.2 g`. Use `⟨w, Subtype.ext (funext fun x => ?_)⟩` and prove the remaining obligations. Establish `e : dualApp (tangent x) le_top w = cst O (f x)` using `(key w _).symm.trans (congr($hw (tangent x)).trans (congrArg (fun y => cst O (f y)) (ht' x)))`.

Rewrite using `[toOmega_apply, e]`. Conclude with `Iso.inv_hom_id_apply _ _`.
-/
theorem toOmega_bijective (O : Type) [CommRing O] (G : Over (Sp O)) [GrpObj G]
    [QuasiSeparated G.hom] [Smooth G.hom]
    (ht : Function.Bijective (tangent : LieG G → Γ(Lie G, ⊤))) :
    Function.Bijective (toOmega G) := by
  have h₁ := isIso_toBidual_of_local_frames (exists_isFrame_omega G)
  have h₂ : (Lie G).IsQuasicoherent := isQuasicoherent_of_frames fun x =>
    have ⟨U, n, _, hx, he⟩ := exists_isFrame_omega G x
    ⟨U, n, _, hx, he.dual⟩
  have h₃ := (dualApp_top_bijective (Lie G)).comp
    (ConcreteCategory.bijective_of_isIso ((cartierDualToBidual (LieVB.omega G)).app ⊤))
  have key (w : Γ(LieVB.omega G, ⊤)) (l : Γ(Lie G, ⊤)) :
      dualApp ((cartierDualToBidual (LieVB.omega G)).app ⊤ w) (le_refl ⊤) l = dualApp l le_top w := by
    rw [dualSheafSectionApply_toBidual, resM_self]
  have hc := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of O)).hom
  have hc' := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of O)).inv
  constructor
  · intro w w' e
    refine h₃.1 (LinearMap.ext fun l => ?_)
    obtain ⟨x, rfl⟩ := ht.2 l
    exact (key w _).trans ((hc.1 congr(($e).1 x)).trans (key w' _).symm)
  · rintro ⟨f, hf₁, hf₂⟩
    let t := Equiv.ofBijective _ ht
    have ht' (x : LieG G) : t.symm (tangent x) = x := t.symm_apply_apply x
    let g : Γ(Lie G, ⊤) →ₗ[Γ(Sp O, ⊤)] Γ(Sp O, ⊤) :=
      { toFun := fun l => cst O (f (t.symm l))
        map_add' := fun l l' => by
          obtain ⟨x, rfl⟩ := ht.2 l
          obtain ⟨y, rfl⟩ := ht.2 l'
          rw [← tangent_mul x y (fst_mul x y), ht' x, ht' y, ← map_add, ← hf₁ x y (fst_mul x y)]
          exact congrArg (fun y => cst O (f y)) (ht' _)
        map_smul' := fun a l => by
          obtain ⟨x, rfl⟩ := ht.2 l
          obtain ⟨a, rfl⟩ : ∃ b, cst O b = a := hc'.2 a
          rw [← tangent_scale a x (fst_scale a x), ht' x, RingHom.id_apply, smul_eq_mul, ← map_mul,
            ← hf₂ a x (fst_scale a x)]
          exact congrArg (fun y => cst O (f y)) (ht' _) }
    obtain ⟨w, hw⟩ := h₃.2 g
    refine ⟨w, Subtype.ext (funext fun x => ?_)⟩
    have e : dualApp (tangent x) le_top w = cst O (f x) :=
      (key w _).symm.trans (congr($hw (tangent x)).trans (congrArg (fun y => cst O (f y)) (ht' x)))
    rw [toOmega_apply, e]
    exact Iso.inv_hom_id_apply _ _

end GlobalTheory.OmegaGlobal
