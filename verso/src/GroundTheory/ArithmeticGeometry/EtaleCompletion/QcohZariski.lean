import Mathlib
import GroundTheory.ArithmeticGeometry.EtaleCompletion.QcohPresheaf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Etale

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

section Unit

variable {V T U : Scheme.{u}}

noncomputable def pullbackUnitApp (g : T ⟶ U) (N : U.Modules) (O : U.Opens) :
    Γ(N, O) →+ Γ((Scheme.Modules.pullback g).obj N, g ⁻¹ᵁ O) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).app O).hom

/- English proof (translation)
Use `((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).mapPresheaf.naturality i.op` as an intermediate fact. Establish `h2` using `congrArg (fun φ => φ.hom n) this`. Simplify using `only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h2`. Conclude with `h2`.
-/
lemma pullbackUnitApp_res (g : T ⟶ U) (N : U.Modules) {O O' : U.Opens} (i : O' ⟶ O)
    (n : Γ(N, O)) :
    pullbackUnitApp g N O' (N.presheaf.map i.op n) =
      ((Scheme.Modules.pullback g).obj N).presheaf.map ((TopologicalSpace.Opens.map g.base).map i).op
        (pullbackUnitApp g N O n) := by
  have := ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).mapPresheaf.naturality i.op
  have h2 := congrArg (fun φ => φ.hom n) this
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h2
  exact h2

/- English proof (translation)
Establish `h` using `unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction g).comp (Scheme.Modules.pullbackPushforwardAdjunction f)) (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)) (Scheme.Modules.pullbackComp f g).inv N`. Rewrite `h` using `[Scheme.Modules.conjugateEquiv_pullbackComp_inv]`. Establish `h'` using `congrArg (fun ψ => (Scheme.Modules.Hom.app ψ O).hom n) h`. Simplify using `only [Adjunction.comp_unit_app, Scheme.Modules.Hom.comp_app, AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, Scheme.Modules.pushforwardComp_hom_app_app] at h'`. Conclude with `h'.symm`.
-/
lemma pullbackUnitApp_comp (f : V ⟶ T) (g : T ⟶ U) (N : U.Modules) (O : U.Opens) (n : Γ(N, O)) :
    ((Scheme.Modules.pullbackComp f g).inv.app N).app ((f ≫ g) ⁻¹ᵁ O)
      (pullbackUnitApp (f ≫ g) N O n) =
        pullbackUnitApp f _ (g ⁻¹ᵁ O) (pullbackUnitApp g N O n) := by
  have h := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)) (Scheme.Modules.pullbackComp f g).inv N
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  have h' := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ O).hom n) h
  simp only [Adjunction.comp_unit_app, Scheme.Modules.Hom.comp_app, AddCommGrpCat.hom_comp,
    AddMonoidHom.coe_comp, Function.comp_apply, Scheme.Modules.pushforwardComp_hom_app_app] at h'
  exact h'.symm

/- English proof (translation)
Rewrite using `[← pullbackUnitApp_comp, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id_app]`. Both sides reduce to the same expression.
-/
lemma pullbackUnitApp_comp_hom (f : V ⟶ T) (g : T ⟶ U) (N : U.Modules) (O : U.Opens)
    (n : Γ(N, O)) :
    ((Scheme.Modules.pullbackComp f g).hom.app N).app ((f ≫ g) ⁻¹ᵁ O)
      (pullbackUnitApp f _ (g ⁻¹ᵁ O) (pullbackUnitApp g N O n)) =
        pullbackUnitApp (f ≫ g) N O n := by
  rw [← pullbackUnitApp_comp, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
    Iso.inv_hom_id_app]
  rfl

/- English proof (translation)
Establish `h` using `Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction j) (Scheme.Modules.pullbackPushforwardAdjunction j) N`. Establish `h' : ∀ n, pullbackUnitApp j N O n = (((Scheme.Modules.restrictFunctorIsoPullback j).hom.app N).app (j ⁻¹ᵁ O)) (N.presheaf.map (homOfLE (j.image_preimage_le O)).op n)` using `fun n => by`. Rewrite using `[pullbackUnitApp, ← h]`. Both sides reduce to the same expression. Establish `hE : j ''ᵁ (j ⁻¹ᵁ O) = O`.

Rewrite using `[Scheme.Hom.image_preimage_eq_opensRange_inf]`. Conclude with `inf_eq_right.2 hO`. Establish `b1` using `ConcreteCategory.bijective_of_isIso (((Scheme.Modules.restrictFunctorIsoPullback j).hom.app N).app (j ⁻¹ᵁ O))`. Establish `b2 : Function.Bijective (N.presheaf.map (homOfLE (j.image_preimage_le O)).op)`. Establish `: homOfLE (j.image_preimage_le O) = eqToHom hE` using `Subsingleton.elim _ _`.

Rewrite using `[this]`. Conclude with `ConcreteCategory.bijective_of_isIso _`. Establish `e : ⇑(pullbackUnitApp j N O) = ⇑(ConcreteCategory.hom (((Scheme.Modules.restrictFunctorIsoPullback j).hom.app N).app (j ⁻¹ᵁ O))) ∘ ⇑(ConcreteCategory.hom (N.presheaf.map (homOfLE (j.image_preimage_le O)).op))`. Use function extensionality and compare the values at `h'`. Rewrite using `[e]`.

Conclude with `b1.comp b2`.
-/
lemma pullbackUnitApp_bijective (j : T ⟶ U) [IsOpenImmersion j] (N : U.Modules) {O : U.Opens}
    (hO : O ≤ j.opensRange) : Function.Bijective (pullbackUnitApp j N O) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction j)
    (Scheme.Modules.pullbackPushforwardAdjunction j) N
  have h' : ∀ n, pullbackUnitApp j N O n =
      (((Scheme.Modules.restrictFunctorIsoPullback j).hom.app N).app (j ⁻¹ᵁ O))
        (N.presheaf.map (homOfLE (j.image_preimage_le O)).op n) := fun n => by
    rw [pullbackUnitApp, ← h]
    rfl
  have hE : j ''ᵁ (j ⁻¹ᵁ O) = O := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_eq_right.2 hO
  have b1 := ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictFunctorIsoPullback j).hom.app N).app (j ⁻¹ᵁ O))
  have b2 : Function.Bijective (N.presheaf.map (homOfLE (j.image_preimage_le O)).op) := by
    have : homOfLE (j.image_preimage_le O) = eqToHom hE := Subsingleton.elim _ _
    rw [this]
    exact ConcreteCategory.bijective_of_isIso _
  have e : ⇑(pullbackUnitApp j N O) =
      ⇑(ConcreteCategory.hom (((Scheme.Modules.restrictFunctorIsoPullback j).hom.app N).app
        (j ⁻¹ᵁ O))) ∘ ⇑(ConcreteCategory.hom (N.presheaf.map (homOfLE (j.image_preimage_le O)).op)) :=
    funext h'
  rw [e]
  exact b1.comp b2

end Unit

section Opens

variable {X : Scheme.{u}} (F : X.Modules) (U : X.Etale)

noncomputable abbrev openObj (O : U.left.Opens) : X.Etale := Scheme.Etale.mk (O.ι ≫ U.hom)

noncomputable def openIncl (O : U.left.Opens) : openObj U O ⟶ U :=
  MorphismProperty.Over.homMk O.ι rfl trivial

noncomputable def openInclLE {O' O : U.left.Opens} (h : O' ≤ O) : openObj U O' ⟶ openObj U O :=
  MorphismProperty.Over.homMk (U.left.homOfLE h)
    (by
      change U.left.homOfLE h ≫ (O.ι ≫ U.hom) = O'.ι ≫ U.hom
      rw [← Category.assoc, Scheme.homOfLE_ι]) trivial

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
lemma openInclLE_left {O' O : U.left.Opens} (h : O' ≤ O) :
    (openInclLE U h).left = U.left.homOfLE h := rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma openIncl_left (O : U.left.Opens) : (openIncl U O).left = O.ι := rfl

instance {Y Z : Scheme.{u}} (a : Y ⟶ Z) (b : Z ⟶ X) (c : Y ⟶ X) (h : a ≫ b = c) :
    IsIso (compHom F a b c h) := by
  unfold compHom
  infer_instance

noncomputable def openSection (O : U.left.Opens) :
    Γ((Scheme.Modules.pullback U.hom).obj F, O) →+
      Γ((Scheme.Modules.pullback (O.ι ≫ U.hom)).obj F, ⊤) :=
  ((compHom F O.ι U.hom _ rfl).app ⊤).hom.comp
    ((((Scheme.Modules.pullback O.ι).obj ((Scheme.Modules.pullback U.hom).obj F)).presheaf.map
      (homOfLE (by rw [Scheme.Opens.ι_preimage_self]) : (⊤ : O.toScheme.Opens) ⟶ O.ι ⁻¹ᵁ O).op).hom.comp
      (pullbackUnitApp O.ι _ O))

end Opens

end GroundTheory.Arith.Etale
