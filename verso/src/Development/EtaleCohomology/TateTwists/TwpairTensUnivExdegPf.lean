import Development.EtaleCohomology.TateTwists.TwpairTensUnivPf

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ExDeg

variable {R : Type} [CommRing R]

noncomputable def tmap {I J I' J' : Cx R} (f : I ⟶ I') (g : J ⟶ J') (V : Scheme.{0}) (w : ℤ) :
    Tens I J V w →ₗ[ULift.{1} R] Tens I' J' V w :=
  DirectSum.lmap fun p => TensorProduct.map ((f.f p.1.1).hom.app (op V)).hom ((g.f p.1.2).hom.app (op V)).hom

/- English proof (translation)
Establish `key : τ.lift V w ∘ₗ Tens.res k w = ((K.X w).obj.map k.op).hom ∘ₗ τ.lift U w`. Apply `DirectSum.linearMap_ext` to reduce the goal to its premises. Introduce `p`. Apply `TensorProduct.ext'` to reduce the goal to its premises. Introduce `a b`.

Simplify using `only [LinearMap.comp_apply, Tens.res, DirectSum.lmap_lof, TensorProduct.map_tmul, Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]`. Conclude with `(τ.nat k p.1.1 p.1.2 w p.2 a b).symm`. Conclude with `congrArg (fun m => m x) key`.
-/
theorem lift_res {I J K : Cx R} (τ : Pair I J K) {V U : Scheme.{0}} (k : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    τ.lift V w (Tens.res k w x) = Sec.res k (τ.lift U w x) := by
  classical
  have key : τ.lift V w ∘ₗ Tens.res k w = ((K.X w).obj.map k.op).hom ∘ₗ τ.lift U w := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, Tens.res, DirectSum.lmap_lof, TensorProduct.map_tmul, Pair.lift,
      DirectSum.toModule_lof, TensorProduct.lift.tmul]
    exact (τ.nat k p.1.1 p.1.2 w p.2 a b).symm
  exact congrArg (fun m => m x) key

/- English proof (translation)
Establish `key : (ν.lift V w ∘ₗ tmap f g V w) ∘ₗ Tens.res k w = ((K.X w).obj.map k.op).hom ∘ₗ (ν.lift U w ∘ₗ tmap f g U w)`. Apply `DirectSum.linearMap_ext` to reduce the goal to its premises. Introduce `p`. Apply `TensorProduct.ext'` to reduce the goal to its premises. Introduce `a b`.

Simplify using `only [LinearMap.comp_apply, Tens.res, tmap, DirectSum.lmap_lof, TensorProduct.map_tmul, Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]`. Establish `e` using `ν.nat k p.1.1 p.1.2 w p.2 (Sec.map (f.f p.1.1) a) (Sec.map (g.f p.1.2) b)`. Rewrite `e` using `[secmap_res, secmap_res]`. Conclude with `e.symm`. Conclude with `congrArg (fun m => m x) key`.
-/
theorem lam_res {I J I' J' K : Cx R} (ν : Pair I' J' K) (f : I ⟶ I') (g : J ⟶ J') {V U : Scheme.{0}} (k : V ⟶ U)
    (w : ℤ) (x : Tens I J U w) :
    ν.lift V w (tmap f g V w (Tens.res k w x)) = Sec.res k (ν.lift U w (tmap f g U w x)) := by
  classical
  have key : (ν.lift V w ∘ₗ tmap f g V w) ∘ₗ Tens.res k w =
      ((K.X w).obj.map k.op).hom ∘ₗ (ν.lift U w ∘ₗ tmap f g U w) := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, Tens.res, tmap, DirectSum.lmap_lof, TensorProduct.map_tmul, Pair.lift,
      DirectSum.toModule_lof, TensorProduct.lift.tmul]
    have e := ν.nat k p.1.1 p.1.2 w p.2 (Sec.map (f.f p.1.1) a) (Sec.map (g.f p.1.2) b)
    rw [secmap_res, secmap_res] at e
    exact e.symm
  exact congrArg (fun m => m x) key

/- English proof (translation)
Apply `etale_sheaf_sections_separated_holds R (K'.X w) V` to reduce the goal to its premises. Use `TensLocbij.loc_mono (hτ.2 V w x hx) ?_` and prove the remaining obligations. Introduce `W k hk`. Rewrite using `[← lam_res, hk, map_zero, map_zero]`. Conclude with `(map_zero _).symm`.
-/
theorem lam_zero {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') (V : Scheme.{0}) (w : ℤ) (x : Tens I J V w) (hx : τ.lift V w x = 0) :
    ν.lift V w (tmap f g V w x) = 0 := by
  apply etale_sheaf_sections_separated_holds R (K'.X w) V
  refine TensLocbij.loc_mono (hτ.2 V w x hx) ?_
  intro W k hk
  rw [← lam_res, hk, map_zero, map_zero]
  exact (map_zero _).symm

/- English proof (translation)
Use `lam_zero τ hτ ν f g V w (x - x') (by rw [map_sub, hx, sub_self])` as an intermediate fact. Rewrite `this` using `[map_sub, map_sub, sub_eq_zero]`. Conclude with `this`.
-/
theorem lam_eq {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') (V : Scheme.{0}) (w : ℤ) (x x' : Tens I J V w) (hx : τ.lift V w x = τ.lift V w x') :
    ν.lift V w (tmap f g V w x) = ν.lift V w (tmap f g V w x') := by
  have := lam_zero τ hτ ν f g V w (x - x') (by rw [map_sub, hx, sub_self])
  rw [map_sub, map_sub, sub_eq_zero] at this
  exact this

end LateralTheory.EtaleFoundations.ExDeg

namespace LateralTheory.EtaleFoundations.ExDeg
variable {R : Type} [CommRing R]

/- English proof (translation)
The claim follows from `(isSheaf_iff_isSheaf_of_type _ _).1 (Presheaf.isSheaf_comp_of_isSheaf _ _ _ F.property)`.
-/
theorem sheafT (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology.{0} (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 (Presheaf.isSheaf_comp_of_isSheaf _ _ _ F.property)

/- English proof (translation)
The claim follows from `(TensLocbij.map_comp_apply' R F.obj k g y).symm`.
-/
theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res k (Sec.res g y) = Sec.res (k ≫ g) y :=
  (TensLocbij.map_comp_apply' R F.obj k g y).symm

def sv {I J K : Cx R} (τ : Pair I J K) {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) : Sieve U where
  arrows V g := ∃ x, τ.lift V w x = Sec.res g y
  downward_closed := by
    rintro V W g ⟨x, hx⟩ k
    exact ⟨Tens.res k w x, by rw [lift_res, hx, res_comp]⟩

/- English proof (translation)
Take `⟨S, hS, hP⟩` from `hτ.1 U w y`. Conclude with `Scheme.etaleTopology.superset_covering (fun V g hg => hP V g hg) hS`.
-/
theorem sv_cov {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) :
    sv τ w y ∈ Scheme.etaleTopology.{0} U := by
  obtain ⟨S, hS, hP⟩ := hτ.1 U w y
  exact Scheme.etaleTopology.superset_covering (fun V g hg => hP V g hg) hS

noncomputable def fam {I J K I' J' K' : Cx R} (τ : Pair I J K) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) :
    Presieve.FamilyOfElements ((K'.X w).obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) (sv τ w y).arrows :=
  fun V _ hk => (ν.lift V w (tmap f g V w hk.choose) : Sec (K'.X w) V)

/- English proof (translation)
Introduce `Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ heq`. Use `show Sec.res g₁ (ν.lift Y₁ w (tmap f g Y₁ w h₁.choose)) = Sec.res g₂ (ν.lift Y₂ w (tmap f g Y₂ w h₂.choose))`. Rewrite using `[← lam_res, ← lam_res]`. Apply `lam_eq τ hτ` to reduce the goal to its premises. Rewrite using `[lift_res, lift_res, h₁.choose_spec, h₂.choose_spec, res_comp, res_comp, heq]`.
-/
theorem fam_compat {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) :
    (fam τ ν f g w y).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ heq
  show Sec.res g₁ (ν.lift Y₁ w (tmap f g Y₁ w h₁.choose)) = Sec.res g₂ (ν.lift Y₂ w (tmap f g Y₂ w h₂.choose))
  rw [← lam_res, ← lam_res]
  apply lam_eq τ hτ
  rw [lift_res, lift_res, h₁.choose_spec, h₂.choose_spec, res_comp, res_comp, heq]

noncomputable def glue {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) : Sec (K'.X w) U :=
  (sheafT (K'.X w) _ (sv_cov τ hτ w y)).amalgamate _ (fam_compat τ hτ ν f g w y)

/- English proof (translation)
Establish `hk : (sv τ w y).arrows k` using `⟨x, hx⟩`. Use `(sheafT (K'.X w) _ (sv_cov τ hτ w y)).valid_glue (fam_compat τ hτ ν f g w y) k hk` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Use `show ν.lift V w (tmap f g V w hk.choose) = _`. Conclude with `lam_eq τ hτ ν f g V w _ _ (hk.choose_spec.trans hx.symm)`.
-/
theorem glue_spec {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) {V : Scheme.{0}} (k : V ⟶ U)
    (x : Tens I J V w) (hx : τ.lift V w x = Sec.res k y) :
    Sec.res k (glue τ hτ ν f g w y) = ν.lift V w (tmap f g V w x) := by
  have hk : (sv τ w y).arrows k := ⟨x, hx⟩
  have := (sheafT (K'.X w) _ (sv_cov τ hτ w y)).valid_glue (fam_compat τ hτ ν f g w y) k hk
  refine this.trans ?_
  show ν.lift V w (tmap f g V w hk.choose) = _
  exact lam_eq τ hτ ν f g V w _ _ (hk.choose_spec.trans hx.symm)

end LateralTheory.EtaleFoundations.ExDeg

namespace LateralTheory.EtaleFoundations.ExDeg
variable {R : Type} [CommRing R]

/- English proof (translation)
Assemble the required witnesses or components as `⟨sv τ w y, sv_cov τ hτ w y, fun _ _ h => h⟩`.
-/
theorem sv_loc {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) :
    Loc U fun V k => (sv τ w y).arrows k :=
  ⟨sv τ w y, sv_cov τ hτ w y, fun _ _ h => h⟩

/- English proof (translation)
Apply `etale_sheaf_sections_separated_holds R (K'.X w) U` to reduce the goal to its premises. Use `TensLocbij.loc_mono (TensLocbij.loc_and (sv_loc τ hτ w y₁) (sv_loc τ hτ w y₂)) ?_` and prove the remaining obligations. Introduce and unpack `V k ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩`. Rewrite using `[glue_spec τ hτ ν f g w _ k (x₁ + x₂) (by rw [map_add, hx₁, hx₂]; exact (map_add _ _ _).symm)]`. Establish `e : Sec.res k (glue τ hτ ν f g w y₁ + glue τ hτ ν f g w y₂) = Sec.res k (glue τ hτ ν f g w y₁) + Sec.res k (glue τ hτ ν f g w y₂)` using `map_add _ _ _`.

Rewrite using `[e, glue_spec τ hτ ν f g w _ k x₁ hx₁, glue_spec τ hτ ν f g w _ k x₂ hx₂, map_add, map_add]`.
-/
theorem glue_add {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y₁ y₂ : Sec (K.X w) U) :
    glue τ hτ ν f g w (y₁ + y₂) = glue τ hτ ν f g w y₁ + glue τ hτ ν f g w y₂ := by
  apply etale_sheaf_sections_separated_holds R (K'.X w) U
  refine TensLocbij.loc_mono (TensLocbij.loc_and (sv_loc τ hτ w y₁) (sv_loc τ hτ w y₂)) ?_
  rintro V k ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
  rw [glue_spec τ hτ ν f g w _ k (x₁ + x₂) (by rw [map_add, hx₁, hx₂]; exact (map_add _ _ _).symm)]
  have e : Sec.res k (glue τ hτ ν f g w y₁ + glue τ hτ ν f g w y₂) =
      Sec.res k (glue τ hτ ν f g w y₁) + Sec.res k (glue τ hτ ν f g w y₂) := map_add _ _ _
  rw [e, glue_spec τ hτ ν f g w _ k x₁ hx₁, glue_spec τ hτ ν f g w _ k x₂ hx₂, map_add, map_add]

/- English proof (translation)
Apply `etale_sheaf_sections_separated_holds R (K'.X w) U` to reduce the goal to its premises. Use `TensLocbij.loc_mono (sv_loc τ hτ w y) ?_` and prove the remaining obligations. Introduce and unpack `V k ⟨x, hx⟩`. Rewrite using `[glue_spec τ hτ ν f g w _ k (c • x) (by rw [map_smul, hx]; exact (map_smul _ _ _).symm)]`. Establish `e : Sec.res k (c • glue τ hτ ν f g w y) = c • Sec.res k (glue τ hτ ν f g w y)` using `map_smul _ _ _`.

Rewrite using `[e, glue_spec τ hτ ν f g w _ k x hx, map_smul, map_smul]`.
-/
theorem glue_smul {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (c : ULift.{1} R) (y : Sec (K.X w) U) :
    glue τ hτ ν f g w (c • y) = c • glue τ hτ ν f g w y := by
  apply etale_sheaf_sections_separated_holds R (K'.X w) U
  refine TensLocbij.loc_mono (sv_loc τ hτ w y) ?_
  rintro V k ⟨x, hx⟩
  rw [glue_spec τ hτ ν f g w _ k (c • x) (by rw [map_smul, hx]; exact (map_smul _ _ _).symm)]
  have e : Sec.res k (c • glue τ hτ ν f g w y) = c • Sec.res k (glue τ hτ ν f g w y) := map_smul _ _ _
  rw [e, glue_spec τ hτ ν f g w _ k x hx, map_smul, map_smul]

/- English proof (translation)
Apply `etale_sheaf_sections_separated_holds R (K'.X w) U'` to reduce the goal to its premises. Use `TensLocbij.loc_mono (sv_loc τ hτ w (Sec.res h y)) ?_` and prove the remaining obligations. Introduce and unpack `_ k ⟨x, hx⟩`. Rewrite using `[glue_spec τ hτ ν f g w _ k x hx, res_comp]`. Rewrite `hx` using `[res_comp]`.

Rewrite using `[glue_spec τ hτ ν f g w _ (k ≫ h) x hx]`.
-/
theorem glue_res {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U U' : Scheme.{0}} (w : ℤ) (h : U' ⟶ U) (y : Sec (K.X w) U) :
    glue τ hτ ν f g w (Sec.res h y) = Sec.res h (glue τ hτ ν f g w y) := by
  apply etale_sheaf_sections_separated_holds R (K'.X w) U'
  refine TensLocbij.loc_mono (sv_loc τ hτ w (Sec.res h y)) ?_
  rintro _ k ⟨x, hx⟩
  rw [glue_spec τ hτ ν f g w _ k x hx, res_comp]
  rw [res_comp] at hx
  rw [glue_spec τ hτ ν f g w _ (k ≫ h) x hx]

noncomputable def phi {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') (w : ℤ) : K.X w ⟶ K'.X w :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun y => glue τ hτ ν f g w (U := U.unop) y
          map_add' := fun y₁ y₂ => glue_add τ hτ ν f g w y₁ y₂
          map_smul' := fun c y => glue_smul τ hτ ν f g w c y }
     naturality := by
       intro U U' h
       ext y
       exact glue_res τ hτ ν f g w h.unop y }⟩

/- English proof (translation)
Simplify using `[Sec.res]`.
-/
theorem res_id {F : Shv R} {U : Scheme.{0}} (y : Sec F U) : Sec.res (𝟙 U) y = y := by
  simp [Sec.res]

end LateralTheory.EtaleFoundations.ExDeg

open LateralTheory.EtaleFoundations.ExDeg in
/- English proof (translation)
Introduce `R _ I J K τ hτ I' J' K' ν f g w`. Use `⟨phi τ hτ ν f g w, ?_⟩` and prove the remaining obligations. Introduce `U s t h a b`. Establish `hx : τ.lift U w (DirectSum.lof (ULift.{1} R) _ _ ⟨(s, t), h⟩ (a ⊗ₜ b)) = Sec.res (𝟙 U) (τ.mul U s t w h a b)`. Rewrite using `[res_id]`.

Simplify using `only [Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]`. Establish `e` using `glue_spec τ hτ ν f g w _ (𝟙 U) _ hx`. Rewrite `e` using `[res_id]`. Use `e.trans ?_` and prove the remaining obligations. Simplify using `only [tmap, DirectSum.lmap_lof, TensorProduct.map_tmul, Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]`.
-/
theorem LateralTheory.EtaleFoundations.twpair_tens_univ_exdeg_of : LateralTheory.EtaleFoundations.twpair_tens_univ_exdeg := by
  intro R _ I J K τ hτ I' J' K' ν f g w
  refine ⟨phi τ hτ ν f g w, ?_⟩
  intro U s t h a b
  classical
  have hx : τ.lift U w (DirectSum.lof (ULift.{1} R) _ _ ⟨(s, t), h⟩ (a ⊗ₜ b)) =
      Sec.res (𝟙 U) (τ.mul U s t w h a b) := by
    rw [res_id]
    simp only [Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]
  have e := glue_spec τ hτ ν f g w _ (𝟙 U) _ hx
  rw [res_id] at e
  refine e.trans ?_
  simp only [tmap, DirectSum.lmap_lof, TensorProduct.map_tmul, Pair.lift, DirectSum.toModule_lof,
    TensorProduct.lift.tmul]
