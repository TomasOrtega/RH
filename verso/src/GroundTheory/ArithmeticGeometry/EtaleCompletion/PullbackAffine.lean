import Mathlib
import GroundTheory.ArithmeticGeometry.EtaleCompletion.ModulesPullback
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Etale

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable def sectionLinear {X : Scheme.{u}} {P P' : X.Modules} (θ : P ⟶ P') :
    Γ(P, ⊤) →ₗ[Γ(X, ⊤)] Γ(P', ⊤) where
  toFun := θ.app ⊤
  map_add' := map_add _
  map_smul' := Scheme.Modules.Hom.app_smul θ

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma sectionLinear_apply {X : Scheme.{u}} {P P' : X.Modules} (θ : P ⟶ P') (x : Γ(P, ⊤)) :
    sectionLinear θ x = θ.app ⊤ x := rfl

def IsBaseChangeSection {T U : Scheme.{u}} (g : T ⟶ U) (N : U.Modules) : Prop :=
  ∀ (Q : Type u) [AddCommGroup Q] [Module Γ(T, ⊤) Q] (ψ : Γ(N, ⊤) →+ Q),
    (∀ (a : Γ(U, ⊤)) (n : Γ(N, ⊤)), ψ (a • n) = g.appTop a • ψ n) →
    ∃! ψ' : Γ((Scheme.Modules.pullback g).obj N, ⊤) →ₗ[Γ(T, ⊤)] Q,
      ∀ n, ψ' (pullbackSection g N n) = ψ n

/- English proof (translation)
Introduce `Q _ _ ψ hψ`. Set `: Module Γ(T, ⊤) Q` to `Module.compHom Q f.appTop.hom`. Establish `hsm : ∀ (t : Γ(T, ⊤)) (q : Q), t • q = f.appTop t • q` using `fun _ _ => rfl`. Take `⟨ψ₁, hψ₁, u₁⟩` from `hg Q ψ (fun a n => by`. Rewrite using `[hψ, hsm, Scheme.Hom.comp_appTop]`.

Use the proof step `rfl)`. Take `⟨ψ₂, hψ₂, u₂⟩` from `hf Q ψ₁.toAddMonoidHom (fun t x => ψ₁.map_smul t x)`. Set `c` to `(Scheme.Modules.pullbackComp f g).app N`. Establish `hc : ∀ n, c.inv.app ⊤ (pullbackSection (f ≫ g) N n) = pullbackSection f _ (pullbackSection g N n)` using `pullbackComp_inv_pullbackSection f g N`. Establish `hchi : ∀ x, c.hom.app ⊤ (c.inv.app ⊤ x) = x` using `fun x => by`.

Rewrite using `[← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, c.inv_hom_id]`. Both sides reduce to the same expression. Establish `hchi' : ∀ x, c.inv.app ⊤ (c.hom.app ⊤ x) = x` using `fun x => by`. Rewrite using `[← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, c.hom_inv_id]`. Both sides reduce to the same expression.

Use `⟨ψ₂ ∘ₗ sectionLinear c.inv, fun n => ?_, fun ψ'' hψ'' => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, sectionLinear_apply, hc, hψ₂]`. Conclude with `hψ₁ n`. Set `χ : Γ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N), ⊤) →ₗ[Γ(W, ⊤)] Q` to `ψ'' ∘ₗ sectionLinear c.hom`. Establish `hχ : ∀ n, χ (pullbackSection f _ (pullbackSection g N n)) = ψ n` using `fun n => by`.

Simplify using `only [χ, LinearMap.comp_apply, sectionLinear_apply, ← hc, hchi, hψ'']`. Set `χ₁ : Γ((Scheme.Modules.pullback g).obj N, ⊤) →ₗ[Γ(T, ⊤)] Q` to `{ toFun := fun x => χ (pullbackSection f _ x) map_add' := fun x y => by simp map_smul' := fun t x => by`. Simplify using `only [RingHom.id_apply]`. Rewrite using `[pullbackSection_smul, map_smul, hsm] }`. Establish `h₁ : χ₁ = ψ₁` using `u₁ χ₁ hχ`.

Establish `h₂ : χ = ψ₂` using `u₂ χ (fun x => congrArg (fun l => l x) h₁)`. Use extensionality with `x`. Simplify using `only [LinearMap.comp_apply, sectionLinear_apply, ← h₂, χ, hchi]`.
-/
lemma IsBaseChangeSection.comp {W T U : Scheme.{u}} {f : W ⟶ T} {g : T ⟶ U} {N : U.Modules}
    (hg : IsBaseChangeSection g N)
    (hf : IsBaseChangeSection f ((Scheme.Modules.pullback g).obj N)) :
    IsBaseChangeSection (f ≫ g) N := by
  intro Q _ _ ψ hψ
  let : Module Γ(T, ⊤) Q := Module.compHom Q f.appTop.hom
  have hsm : ∀ (t : Γ(T, ⊤)) (q : Q), t • q = f.appTop t • q := fun _ _ => rfl
  obtain ⟨ψ₁, hψ₁, u₁⟩ := hg Q ψ (fun a n => by
    rw [hψ, hsm, Scheme.Hom.comp_appTop]; rfl)
  obtain ⟨ψ₂, hψ₂, u₂⟩ := hf Q ψ₁.toAddMonoidHom (fun t x => ψ₁.map_smul t x)
  let c := (Scheme.Modules.pullbackComp f g).app N
  have hc : ∀ n, c.inv.app ⊤ (pullbackSection (f ≫ g) N n) =
      pullbackSection f _ (pullbackSection g N n) :=
    pullbackComp_inv_pullbackSection f g N
  have hchi : ∀ x, c.hom.app ⊤ (c.inv.app ⊤ x) = x := fun x => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, c.inv_hom_id]; rfl
  have hchi' : ∀ x, c.inv.app ⊤ (c.hom.app ⊤ x) = x := fun x => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, c.hom_inv_id]; rfl
  refine ⟨ψ₂ ∘ₗ sectionLinear c.inv, fun n => ?_, fun ψ'' hψ'' => ?_⟩
  · simp only [LinearMap.comp_apply, sectionLinear_apply, hc, hψ₂]
    exact hψ₁ n
  · let χ : Γ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N), ⊤) →ₗ[Γ(W, ⊤)] Q :=
      ψ'' ∘ₗ sectionLinear c.hom
    have hχ : ∀ n, χ (pullbackSection f _ (pullbackSection g N n)) = ψ n := fun n => by
      simp only [χ, LinearMap.comp_apply, sectionLinear_apply, ← hc, hchi, hψ'']
    let χ₁ : Γ((Scheme.Modules.pullback g).obj N, ⊤) →ₗ[Γ(T, ⊤)] Q :=
      { toFun := fun x => χ (pullbackSection f _ x)
        map_add' := fun x y => by simp
        map_smul' := fun t x => by
          simp only [RingHom.id_apply]
          rw [pullbackSection_smul, map_smul, hsm] }
    have h₁ : χ₁ = ψ₁ := u₁ χ₁ hχ
    have h₂ : χ = ψ₂ := u₂ χ (fun x => congrArg (fun l => l x) h₁)
    ext x
    simp only [LinearMap.comp_apply, sectionLinear_apply, ← h₂, χ, hchi]

/- English proof (translation)
Establish `: (fun h : X ⟶ Y => G.map h) = (adj.homEquiv (G.obj X) Y) ∘ (fun h => adj.counit.app X ≫ h)`. Use function extensionality and compare the values at `h`. Simplify using `[Adjunction.homEquiv_unit]`. Rewrite using `[this]`. Conclude with `(adj.homEquiv _ _).bijective.comp ⟨fun a b h => (cancel_epi _).mp h, fun b => ⟨inv (adj.counit.app X) ≫ b, by simp⟩⟩`.
-/
lemma bijective_map_of_isIso_counit {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) (X Y : D) [IsIso (adj.counit.app X)] :
    Function.Bijective (fun h : X ⟶ Y => G.map h) := by
  have : (fun h : X ⟶ Y => G.map h) =
      (adj.homEquiv (G.obj X) Y) ∘ (fun h => adj.counit.app X ≫ h) := by
    funext h
    simp [Adjunction.homEquiv_unit]
  rw [this]
  exact (adj.homEquiv _ _).bijective.comp
    ⟨fun a b h => (cancel_epi _).mp h,
      fun b => ⟨inv (adj.counit.app X) ≫ b, by simp⟩⟩

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Establish `: IsIso ((tilde.adjunction (R` using `A)).counit.app P) := inferInstanceAs (IsIso P.fromTildeΓ)`. Establish `hb` using `bijective_map_of_isIso_counit (tilde.adjunction (R := A)) P P'`. Set `fA : (moduleSpecΓFunctor (R` to `A)).obj P ⟶ (moduleSpecΓFunctor (R := A)).obj P' := ModuleCat.ofHom (X := (moduleSpecΓFunctor (R := A)).obj P) (Y := (moduleSpecΓFunctor (R := A)).obj P') { toFun := f map_add' := map_add f map_smul' := fun a x => f.map_smul ((Scheme.ΓSpecIso A).inv a) x }`. Take `⟨θ, hθ⟩` from `hb.2 fA`. Use `⟨θ, fun x => ?_, fun θ' hθ' => hb.1 ?_⟩` and prove the remaining obligations.

Conclude with `congrArg (fun l => l.hom x) hθ`. Use `hθ.symm ▸ ?_` and prove the remaining obligations. Use extensionality with `x`. Conclude with `hθ' x`.
-/
lemma existsUnique_hom_app_top {A : CommRingCat.{u}} (P P' : (Spec A).Modules)
    [IsIso P.fromTildeΓ] (f : Γ(P, ⊤) →ₗ[Γ(Spec A, ⊤)] Γ(P', ⊤)) :
    ∃! θ : P ⟶ P', ∀ x, θ.app ⊤ x = f x := by
  have : IsIso ((tilde.adjunction (R := A)).counit.app P) :=
    inferInstanceAs (IsIso P.fromTildeΓ)
  have hb := bijective_map_of_isIso_counit (tilde.adjunction (R := A)) P P'
  let fA : (moduleSpecΓFunctor (R := A)).obj P ⟶ (moduleSpecΓFunctor (R := A)).obj P' :=
    ModuleCat.ofHom (X := (moduleSpecΓFunctor (R := A)).obj P)
      (Y := (moduleSpecΓFunctor (R := A)).obj P')
      { toFun := f
        map_add' := map_add f
        map_smul' := fun a x => f.map_smul ((Scheme.ΓSpecIso A).inv a) x }
  obtain ⟨θ, hθ⟩ := hb.2 fA
  refine ⟨θ, fun x => ?_, fun θ' hθ' => hb.1 ?_⟩
  · exact congrArg (fun l => l.hom x) hθ
  · refine hθ.symm ▸ ?_
    ext x
    exact hθ' x

/- English proof (translation)
Set `: Module R Q` to `Module.compHom Q (Scheme.ΓSpecIso R).inv.hom`. Set `e` to `(tilde.isoTop (ModuleCat.of R Q)).toLinearEquiv`. Use `⟨tilde (ModuleCat.of R Q), ⟨ { toFun := e.symm invFun := e map_add' := map_add e.symm map_smul' := fun t x => ?_ left_inv := fun x => e.apply_symm_apply x right_inv := fun x => e.symm_apply_apply x }⟩⟩` and prove the remaining obligations. Take `⟨r, rfl⟩ : ∃ r : R, (Scheme.ΓSpecIso R).inv r = t` from `⟨(Scheme.ΓSpecIso R).hom t, by simp⟩`. Conclude with `e.symm.map_smul r x`.
-/
lemma exists_modules_linearEquiv (R : CommRingCat.{u}) (Q : Type u) [AddCommGroup Q]
    [Module Γ(Spec R, ⊤) Q] :
    ∃ P : (Spec R).Modules, Nonempty (Γ(P, ⊤) ≃ₗ[Γ(Spec R, ⊤)] Q) := by
  let : Module R Q := Module.compHom Q (Scheme.ΓSpecIso R).inv.hom
  let e := (tilde.isoTop (ModuleCat.of R Q)).toLinearEquiv
  refine ⟨tilde (ModuleCat.of R Q), ⟨
    { toFun := e.symm
      invFun := e
      map_add' := map_add e.symm
      map_smul' := fun t x => ?_
      left_inv := fun x => e.apply_symm_apply x
      right_inv := fun x => e.symm_apply_apply x }⟩⟩
  obtain ⟨r, rfl⟩ : ∃ r : R, (Scheme.ΓSpecIso R).inv r = t :=
    ⟨(Scheme.ΓSpecIso R).hom t, by simp⟩
  exact e.symm.map_smul r x

noncomputable def pushforwardΓIso {A R : CommRingCat.{u}} (φ : A ⟶ R) :
    moduleSpecΓFunctor (R := R) ⋙ ModuleCat.restrictScalars φ.hom ≅
      Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := A) :=
  Iso.symm (Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso φ)
    (TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op ⊤)))

noncomputable def pullbackTildeIso {A R : CommRingCat.{u}} (φ : A ⟶ R) :
    tilde.functor A ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor R :=
  ((tilde.adjunction (R := A)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).leftAdjointUniq
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := R))).ofNatIsoRight
      (pushforwardΓIso φ))

/- English proof (translation)
Rewrite using `[isIso_fromTildeΓ_iff]`. Conclude with `⟨_, ⟨((pullbackTildeIso φ).app _).symm ≪≫ (Scheme.Modules.pullback (Spec.map φ)).mapIso (@asIso _ _ _ _ N.fromTildeΓ ‹_›)⟩⟩`.
-/
lemma isIso_fromTildeΓ_pullback {A R : CommRingCat.{u}} (φ : A ⟶ R) (N : (Spec A).Modules)
    [IsIso N.fromTildeΓ] :
    IsIso ((Scheme.Modules.pullback (Spec.map φ)).obj N).fromTildeΓ := by
  rw [isIso_fromTildeΓ_iff]
  exact ⟨_, ⟨((pullbackTildeIso φ).app _).symm ≪≫
    (Scheme.Modules.pullback (Spec.map φ)).mapIso (@asIso _ _ _ _ N.fromTildeΓ ‹_›)⟩⟩

/- English proof (translation)
Introduce `Q _ _ ψ hψ`. Use `set g := Spec.map φ with hg`. Use `isIso_fromTildeΓ_pullback φ N` as an intermediate fact. Take `⟨P, ⟨e⟩⟩` from `exists_modules_linearEquiv R Q`. Set `adj` to `Scheme.Modules.pullbackPushforwardAdjunction g`.

Set `f : Γ(N, ⊤) →ₗ[Γ(Spec A, ⊤)] Γ((Scheme.Modules.pushforward g).obj P, ⊤)` to `{ toFun := fun n => e.symm (ψ n) map_add' := fun x y => by`. Rewrite using `[map_add, map_add]`. Both sides reduce to the same expression. Use the proof step `map_smul' := fun a x => by`. Rewrite using `[hψ, map_smul]`.

Use `rfl }`. Establish `hf : ∀ n, f n = e.symm (ψ n)` using `fun _ => rfl`. Take `⟨θ, hθ, uθ⟩` from `existsUnique_hom_app_top N _ f`. Establish `key : ∀ (h : (Scheme.Modules.pullback g).obj N ⟶ P) (n : Γ(N, ⊤)), (adj.homEquiv _ _ h).app ⊤ n = h.app ⊤ (pullbackSection g N n)` using `fun h n => by`. Rewrite using `[Adjunction.homEquiv_unit]`.

Both sides reduce to the same expression. Set `θ'` to `(adj.homEquiv _ _).symm θ`. Use `⟨e.toLinearMap ∘ₗ sectionLinear θ', fun n => ?_, fun ψ'' hψ'' => ?_⟩` and prove the remaining obligations. Use `key θ' n` as an intermediate fact. Rewrite `this` using `[Equiv.apply_symm_apply, hθ, hf]`.

Simplify using `only [LinearMap.comp_apply, sectionLinear_apply, LinearEquiv.coe_coe]`. Use `erw [← this]`. Simplify using the standard rewrite rules. Take `⟨h, hh, -⟩` from `existsUnique_hom_app_top _ P (e.symm.toLinearMap ∘ₗ ψ'')`. Establish `: adj.homEquiv _ _ h = θ` using `uθ _ (fun n => by`.

Rewrite using `[key, hh, hf]`. Simplify using `[hψ''])`. Establish `hθ' : h = θ'` using `by simp [θ', ← this]`. Use extensionality with `x`. Simplify using `[← hθ', hh]`.
-/
lemma isBaseChangeSection_specMap {A R : CommRingCat.{u}} (φ : A ⟶ R) (N : (Spec A).Modules)
    [IsIso N.fromTildeΓ] : IsBaseChangeSection (Spec.map φ) N := by
  intro Q _ _ ψ hψ
  set g := Spec.map φ with hg
  have := isIso_fromTildeΓ_pullback φ N
  obtain ⟨P, ⟨e⟩⟩ := exists_modules_linearEquiv R Q
  let adj := Scheme.Modules.pullbackPushforwardAdjunction g
  let f : Γ(N, ⊤) →ₗ[Γ(Spec A, ⊤)] Γ((Scheme.Modules.pushforward g).obj P, ⊤) :=
    { toFun := fun n => e.symm (ψ n)
      map_add' := fun x y => by
        rw [map_add, map_add]
        rfl
      map_smul' := fun a x => by
        rw [hψ, map_smul]
        rfl }
  have hf : ∀ n, f n = e.symm (ψ n) := fun _ => rfl
  obtain ⟨θ, hθ, uθ⟩ := existsUnique_hom_app_top N _ f
  have key : ∀ (h : (Scheme.Modules.pullback g).obj N ⟶ P) (n : Γ(N, ⊤)),
      (adj.homEquiv _ _ h).app ⊤ n = h.app ⊤ (pullbackSection g N n) := fun h n => by
    rw [Adjunction.homEquiv_unit]
    rfl
  let θ' := (adj.homEquiv _ _).symm θ
  refine ⟨e.toLinearMap ∘ₗ sectionLinear θ', fun n => ?_, fun ψ'' hψ'' => ?_⟩
  · have := key θ' n
    rw [Equiv.apply_symm_apply, hθ, hf] at this
    simp only [LinearMap.comp_apply, sectionLinear_apply, LinearEquiv.coe_coe]
    erw [← this]
    simp
  · obtain ⟨h, hh, -⟩ := existsUnique_hom_app_top _ P (e.symm.toLinearMap ∘ₗ ψ'')
    have : adj.homEquiv _ _ h = θ := uθ _ (fun n => by
      rw [key, hh, hf]
      simp [hψ''])
    have hθ' : h = θ' := by simp [θ', ← this]
    ext x
    simp [← hθ', hh]

/- English proof (translation)
Establish `h` using `Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction g) (Scheme.Modules.pullbackPushforwardAdjunction g) N`. Establish `hU : (⊤ : U.Opens) ≤ g ''ᵁ (g ⁻¹ᵁ (⊤ : U.Opens))`. Simplify using `[Scheme.Hom.opensRange_of_isIso]`. Establish `h1 : IsIso (((Scheme.Modules.restrictAdjunction g).unit.app N).app ⊤)`. Rewrite using `[Scheme.Modules.restrictAdjunction_unit_app_app]`.

Establish `: IsIso (homOfLE (g.image_preimage_le (⊤ : U.Opens))).op` using `⟨(homOfLE hU).op, Subsingleton.elim _ _, Subsingleton.elim _ _⟩`. Conclude with `Functor.map_isIso N.presheaf _`. Establish `h2 : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).app ⊤)`. Rewrite using `[← h, Scheme.Modules.Hom.comp_app]`. Establish `: IsIso (((Scheme.Modules.pushforward g).map (((Scheme.Modules.restrictAdjunction g).leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction g)).hom.app N)).app ⊤)` using `inferInstanceAs (IsIso (Scheme.Modules.Hom.app _ _))`.

Use `infer_instance`. Conclude with `ConcreteCategory.bijective_of_isIso (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).app ⊤)`.
-/
lemma bijective_pullbackSection_of_isIso {T U : Scheme.{u}} (g : T ⟶ U) [IsIso g] (N : U.Modules) :
    Function.Bijective (pullbackSection g N) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction g)
    (Scheme.Modules.pullbackPushforwardAdjunction g) N
  have hU : (⊤ : U.Opens) ≤ g ''ᵁ (g ⁻¹ᵁ (⊤ : U.Opens)) := by
    simp [Scheme.Hom.opensRange_of_isIso]
  have h1 : IsIso (((Scheme.Modules.restrictAdjunction g).unit.app N).app ⊤) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    have : IsIso (homOfLE (g.image_preimage_le (⊤ : U.Opens))).op :=
      ⟨(homOfLE hU).op, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    exact Functor.map_isIso N.presheaf _
  have h2 : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).app ⊤) := by
    rw [← h, Scheme.Modules.Hom.comp_app]
    have : IsIso (((Scheme.Modules.pushforward g).map
        (((Scheme.Modules.restrictAdjunction g).leftAdjointUniq
          (Scheme.Modules.pullbackPushforwardAdjunction g)).hom.app N)).app ⊤) :=
      inferInstanceAs (IsIso (Scheme.Modules.Hom.app _ _))
    infer_instance
  exact ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).app ⊤)

/- English proof (translation)
Introduce `Q _ _ ψ hψ`. Establish `hb` using `bijective_pullbackSection_of_isIso g N`. Establish `: IsIso g.appTop` using `inferInstanceAs (IsIso (g.app ⊤))`. Set `e` to `AddEquiv.ofBijective (pullbackSection g N) hb`. Establish `he : ∀ n, e.symm (pullbackSection g N n) = n` using `fun n => e.symm_apply_apply n`.

Establish `hs : ∀ x, pullbackSection g N (e.symm x) = x` using `fun x => e.apply_symm_apply x`. Use `⟨{ toFun := fun x => ψ (e.symm x) map_add' := fun x y => by simp map_smul' := fun t x => ?_ }, fun n => ?_, fun ψ'' hψ'' => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩ : ∃ a : Γ(U, ⊤), g.appTop a = t` from `⟨(asIso g.appTop).inv t, by simp⟩`. Simplify using `only [RingHom.id_apply]`. Rewrite using `[← hψ, ← hs x, he, ← pullbackSection_smul, he]`.

Simplify using `[he]`. Use extensionality with `x`. Take `⟨n, rfl⟩` from `hb.2 x`. Simplify using `[he, hψ'']`.
-/
lemma isBaseChangeSection_of_isIso {T U : Scheme.{u}} (g : T ⟶ U) [IsIso g] (N : U.Modules) :
    IsBaseChangeSection g N := by
  intro Q _ _ ψ hψ
  have hb := bijective_pullbackSection_of_isIso g N
  have : IsIso g.appTop := inferInstanceAs (IsIso (g.app ⊤))
  let e := AddEquiv.ofBijective (pullbackSection g N) hb
  have he : ∀ n, e.symm (pullbackSection g N n) = n := fun n => e.symm_apply_apply n
  have hs : ∀ x, pullbackSection g N (e.symm x) = x := fun x => e.apply_symm_apply x
  refine ⟨{ toFun := fun x => ψ (e.symm x)
            map_add' := fun x y => by simp
            map_smul' := fun t x => ?_ }, fun n => ?_, fun ψ'' hψ'' => ?_⟩
  · obtain ⟨a, rfl⟩ : ∃ a : Γ(U, ⊤), g.appTop a = t :=
      ⟨(asIso g.appTop).inv t, by simp⟩
    simp only [RingHom.id_apply]
    rw [← hψ, ← hs x, he, ← pullbackSection_smul, he]
  · simp [he]
  · ext x
    obtain ⟨n, rfl⟩ := hb.2 x
    simp [he, hψ'']

/- English proof (translation)
The claim follows from `(SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso ((Scheme.Modules.restrictFunctorIsoPullback g).app N) inferInstance`.
-/
lemma isQuasicoherent_pullback_of_isIso {T U : Scheme.{u}} (g : T ⟶ U) [IsIso g] (N : U.Modules)
    [N.IsQuasicoherent] : ((Scheme.Modules.pullback g).obj N).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback g).app N) inferInstance

/- English proof (translation)
Take `⟨φ, hφ⟩ : ∃ φ, Spec.map φ = T.isoSpec.inv ≫ g ≫ U.isoSpec.hom` from `⟨Spec.preimage _, Spec.map_preimage _⟩`. Establish `hg : g = T.isoSpec.hom ≫ Spec.map φ ≫ U.isoSpec.inv` using `by simp [hφ]`. Establish `key : IsBaseChangeSection g N`. Rewrite using `[hg]`. Use `isQuasicoherent_pullback_of_isIso U.isoSpec.inv N` as an intermediate fact.

Use `(isQuasicoherent_iff_isIso_fromTildeΓ ((Scheme.Modules.pullback U.isoSpec.inv).obj N)).mp inferInstance` as an intermediate fact. Conclude with `IsBaseChangeSection.comp (IsBaseChangeSection.comp (isBaseChangeSection_of_isIso _ N) (isBaseChangeSection_specMap φ _)) (isBaseChangeSection_of_isIso _ _)`. Conclude with `key Q ψ hψ`.
-/
theorem existsUnique_pullbackSection {T U : Scheme.{u}} (g : T ⟶ U) [IsAffine T] [IsAffine U]
    (N : U.Modules) [N.IsQuasicoherent] (Q : Type u) [AddCommGroup Q] [Module Γ(T, ⊤) Q]
    (ψ : Γ(N, ⊤) →+ Q) (hψ : ∀ (a : Γ(U, ⊤)) (n : Γ(N, ⊤)), ψ (a • n) = g.appTop a • ψ n) :
    ∃! ψ' : Γ((Scheme.Modules.pullback g).obj N, ⊤) →ₗ[Γ(T, ⊤)] Q,
      ∀ n, ψ' (pullbackSection g N n) = ψ n := by
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = T.isoSpec.inv ≫ g ≫ U.isoSpec.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hg : g = T.isoSpec.hom ≫ Spec.map φ ≫ U.isoSpec.inv := by simp [hφ]
  have key : IsBaseChangeSection g N := by
    rw [hg]
    have := isQuasicoherent_pullback_of_isIso U.isoSpec.inv N
    have := (isQuasicoherent_iff_isIso_fromTildeΓ
      ((Scheme.Modules.pullback U.isoSpec.inv).obj N)).mp inferInstance
    exact IsBaseChangeSection.comp (IsBaseChangeSection.comp (isBaseChangeSection_of_isIso _ N)
      (isBaseChangeSection_specMap φ _)) (isBaseChangeSection_of_isIso _ _)
  exact key Q ψ hψ

end GroundTheory.Arith.Etale
