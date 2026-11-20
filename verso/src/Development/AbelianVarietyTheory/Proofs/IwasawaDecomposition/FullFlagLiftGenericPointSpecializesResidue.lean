import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoBear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagCommonClosedPointOfGenericStatement

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

/- English proof (translation)
Use `haveI : IsLocalRing (M.O y).toSubring := inferInstanceAs (IsLocalRing (M.O y))`. Take `⟨V, hle, hloc⟩` from `(LocalSubring.mk (M.O y).toSubring).exists_le_valuationSubring`. Set `ψ : M.Z.presheaf.stalk y →+* V` to `(M.stalkHom y).codRestrict V (fun a => hle (M.stalkEquiv y a).2)`. Use `haveI : IsLocalHom ψ := ⟨fun a ha => by`. Establish `h1 : IsUnit (Subring.inclusion hle (M.stalkEquiv y a))` using `ha`.

Conclude with `(MulEquiv.isUnit_map (M.stalkEquiv y)).1 (hloc.map_nonunit _ h1)⟩`. Use `⟨V, spMap ψ ≫ M.Z.fromSpecStalk y, ?_, ?_⟩` and prove the remaining obligations. Establish `hs` using `M.pt_specializes (IsLocalRing.closedPoint Ω) y`. Establish `hc : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap V Ω) = M.Z.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (R` using `CommRingCat.of Ω) M.pt := by`. Use extensionality with `a`.

Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Spec.map_comp, Category.assoc]`. Use `_ = Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt) ≫ Spec.map (M.Z.presheaf.stalkSpecializes hs) ≫ M.Z.fromSpecStalk y := by`. Rewrite using `[hc, Spec.map_comp, Category.assoc]`.

Use `_ = M.pt := by`. Rewrite using `[Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]`. Establish `ec : spMap ψ (IsLocalRing.closedPoint V) = IsLocalRing.closedPoint _` using `IsLocalRing.comap_closedPoint ψ show M.Z.fromSpecStalk y (spMap ψ (IsLocalRing.closedPoint V)) = y`. Rewrite using `[ec]`. Conclude with `Scheme.fromSpecStalk_closedPoint`.
-/
theorem exists_valuation_point {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (y : M.Z) :
    ∃ (V : ValuationSubring Ω) (v : Sp V ⟶ M.Z), spMap (algebraMap V Ω) ≫ v = M.pt ∧
      v (IsLocalRing.closedPoint V) = y := by
  haveI : IsLocalRing (M.O y).toSubring := inferInstanceAs (IsLocalRing (M.O y))
  obtain ⟨V, hle, hloc⟩ := (LocalSubring.mk (M.O y).toSubring).exists_le_valuationSubring
  let ψ : M.Z.presheaf.stalk y →+* V :=
    (M.stalkHom y).codRestrict V (fun a => hle (M.stalkEquiv y a).2)
  haveI : IsLocalHom ψ := ⟨fun a ha => by
    have h1 : IsUnit (Subring.inclusion hle (M.stalkEquiv y a)) := ha
    exact (MulEquiv.isUnit_map (M.stalkEquiv y)).1 (hloc.map_nonunit _ h1)⟩
  refine ⟨V, spMap ψ ≫ M.Z.fromSpecStalk y, ?_, ?_⟩
  · have hs := M.pt_specializes (IsLocalRing.closedPoint Ω) y
    have hc : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap V Ω) =
        M.Z.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt := by
      ext a
      rfl
    calc spMap (algebraMap V Ω) ≫ spMap ψ ≫ M.Z.fromSpecStalk y
        = Spec.map (CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap V Ω)) ≫ M.Z.fromSpecStalk y := by
          rw [Spec.map_comp, Category.assoc]
      _ = Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt) ≫
            Spec.map (M.Z.presheaf.stalkSpecializes hs) ≫ M.Z.fromSpecStalk y := by
          rw [hc, Spec.map_comp, Category.assoc]
      _ = M.pt := by
          rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · have ec : spMap ψ (IsLocalRing.closedPoint V) = IsLocalRing.closedPoint _ := IsLocalRing.comap_closedPoint ψ
    show M.Z.fromSpecStalk y (spMap ψ (IsLocalRing.closedPoint V)) = y
    rw [ec]
    exact Scheme.fromSpecStalk_closedPoint

/- English proof (translation)
The claim follows from `exists_valuation_point (ratOf Y) y`.
-/
theorem exists_valuation_point_var {F : Type} [Field F] (Y : Var F) (y : Y.X) :
    ∃ (V : ValuationSubring Y.Fn) (v : Sp V ⟶ Y.X), spMap (algebraMap V Y.Fn) ≫ v = (ratOf Y).pt ∧
      v (IsLocalRing.closedPoint V) = y :=
  exists_valuation_point (ratOf Y) y

/- English proof (translation)
Introduce `F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ q hq hco y hy`. Take `⟨V, v, hvg, hvc⟩` from `exists_valuation_point_var Y₁ y`. Establish `hs : f₂ ≫ X.str = Y₂.str` using `h₂.1.inducedModelMorphism_comp_structureMap`. Use `haveI : IsProper (f₂ ≫ X.str) := hs ▸ inferInstance`. Use `haveI : UniversallyClosed f₂ := UniversallyClosed.of_comp_of_isSeparated f₂ X.str`.

Establish `hE : ValuativeCriterion.Existence f₂` using `(UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f₂) : (ValuativeCriterion.Existence ⊓ @QuasiCompact) f₂).1`. Establish `hsq : q ≫ f₂ = spMap (algebraMap V Y₁.Fn) ≫ (v ≫ f₁)`. Conclude with `hq.trans ((congrArg (· ≫ f₁) hvg.symm).trans (Category.assoc _ _ _))`. Take `⟨⟨l⟩⟩` from `hE { R := V, K := Y₁.Fn, i₁ := q, i₂ := v ≫ f₁, commSq := ⟨hsq⟩ }`. Establish `hl₁ : spMap (algebraMap V Y₁.Fn) ≫ l.l = q` using `l.fac_left`.

Establish `hl₂ : l.l ≫ f₂ = v ≫ f₁` using `l.fac_right`. Establish `hinc` using `GlobalTheory.T.fullFlag_common_closedPoint_of_generic F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ V Y₁.Fn v l.l hl₂.symm (by`. Establish `e : spMap (algebraMap V Y₁.Fn) ≫ v ≫ f₁ = (ratOf Y₁).pt ≫ f₁` using `(Category.assoc _ _ _).symm.trans (congrArg (· ≫ f₁) hvg)`. Establish `key : ∀ (x x' : Sp Y₁.Fn ⟶ X.X) (p p' : Sp Y₁.Fn ⟶ Y₁.X) (r r' : Sp Y₁.Fn ⟶ Y₂.X), x = x' → p = p' → r = r' → CoBear Eb S₁ φ₁ S₂ φ₂ x p r → CoBear Eb S₁ φ₁ S₂ φ₂ x' p' r'`. Introduce and unpack `_ _ _ _ _ _ rfl rfl rfl h`.

Conclude with `h`. Conclude with `key _ _ _ _ _ _ e.symm hvg.symm hl₁.symm hco)`. Establish `ec : spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) = IsLocalRing.closedPoint V` using `IsLocalRing.comap_closedPoint (IsLocalRing.residue V)`. Establish `hp'` using `hy (IsLocalRing.ResidueField V) (spMap (IsLocalRing.residue V) ≫ v) (spMap (IsLocalRing.residue V) ≫ l.l) (by show v (spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint _)) = y`. Rewrite using `[ec]`.

Conclude with `hvc)`. Use the proof step `((Category.assoc _ _ _).trans ((congrArg (spMap (IsLocalRing.residue V) ≫ ·) hl₂.symm).trans (Category.assoc _ _ _).symm))`. Use the proof step `(by convert hinc using 1; exact Category.assoc _ _ _)`. Establish `e2 : l.l (IsLocalRing.closedPoint V) = genericPoint Y₂.X`. Express the relevant statement in the definitionally equal form `l.l (spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint _)) = _ at hp'`.

Rewrite `hp'` using `[ec]`. Then use the resulting hypothesis. Establish `e1 : q (IsLocalRing.closedPoint Y₁.Fn) = l.l (spMap (algebraMap V Y₁.Fn) (IsLocalRing.closedPoint Y₁.Fn))`. Use `congrArg (fun g : Sp Y₁.Fn ⟶ Y₂.X => g (IsLocalRing.closedPoint Y₁.Fn)) hl₁` as an intermediate fact. Conclude with `this.symm`. Establish `h2` using `(IsLocalRing.specializes_closedPoint (spMap (algebraMap V Y₁.Fn) (IsLocalRing.closedPoint Y₁.Fn))).map l.l.continuous`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Conclude with `e2.symm`.
-/
theorem lift_specializes_genericPoint : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ q : Sp Y₁.Fn ⟶ Y₂.X, q ≫ f₂ = (ratOf Y₁).pt ≫ f₁ → CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt q → ∀ y : Y₁.X, (∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X) (p' : Sp K ⟶ Y₂.X), p (IsLocalRing.closedPoint K) = y → p ≫ f₁ = p' ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p p' → p' (IsLocalRing.closedPoint K) = genericPoint Y₂.X) → q (IsLocalRing.closedPoint Y₁.Fn) ⤳ genericPoint Y₂.X := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ q hq hco y hy
  obtain ⟨V, v, hvg, hvc⟩ := exists_valuation_point_var Y₁ y
  have hs : f₂ ≫ X.str = Y₂.str := h₂.1.inducedModelMorphism_comp_structureMap
  haveI : IsProper (f₂ ≫ X.str) := hs ▸ inferInstance
  haveI : UniversallyClosed f₂ := UniversallyClosed.of_comp_of_isSeparated f₂ X.str
  have hE : ValuativeCriterion.Existence f₂ :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f₂) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) f₂).1
  have hsq : q ≫ f₂ = spMap (algebraMap V Y₁.Fn) ≫ (v ≫ f₁) := by
    exact hq.trans ((congrArg (· ≫ f₁) hvg.symm).trans (Category.assoc _ _ _))
  obtain ⟨⟨l⟩⟩ := hE { R := V, K := Y₁.Fn, i₁ := q, i₂ := v ≫ f₁, commSq := ⟨hsq⟩ }
  have hl₁ : spMap (algebraMap V Y₁.Fn) ≫ l.l = q := l.fac_left
  have hl₂ : l.l ≫ f₂ = v ≫ f₁ := l.fac_right
  have hinc := GlobalTheory.T.fullFlag_common_closedPoint_of_generic F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ V Y₁.Fn v l.l hl₂.symm
    (by
      have e : spMap (algebraMap V Y₁.Fn) ≫ v ≫ f₁ = (ratOf Y₁).pt ≫ f₁ :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f₁) hvg)
      have key : ∀ (x x' : Sp Y₁.Fn ⟶ X.X) (p p' : Sp Y₁.Fn ⟶ Y₁.X) (r r' : Sp Y₁.Fn ⟶ Y₂.X), x = x' → p = p' →
          r = r' → CoBear Eb S₁ φ₁ S₂ φ₂ x p r → CoBear Eb S₁ φ₁ S₂ φ₂ x' p' r' := by
        rintro _ _ _ _ _ _ rfl rfl rfl h
        exact h
      exact key _ _ _ _ _ _ e.symm hvg.symm hl₁.symm hco)
  have ec : spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) =
      IsLocalRing.closedPoint V := IsLocalRing.comap_closedPoint (IsLocalRing.residue V)
  have hp' := hy (IsLocalRing.ResidueField V) (spMap (IsLocalRing.residue V) ≫ v)
    (spMap (IsLocalRing.residue V) ≫ l.l)
    (by
      show v (spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint _)) = y
      rw [ec]
      exact hvc)
    ((Category.assoc _ _ _).trans ((congrArg (spMap (IsLocalRing.residue V) ≫ ·) hl₂.symm).trans
      (Category.assoc _ _ _).symm))
    (by convert hinc using 1; exact Category.assoc _ _ _)
  have e2 : l.l (IsLocalRing.closedPoint V) = genericPoint Y₂.X := by
    change l.l (spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint _)) = _ at hp'
    rwa [ec] at hp'
  have e1 : q (IsLocalRing.closedPoint Y₁.Fn) =
      l.l (spMap (algebraMap V Y₁.Fn) (IsLocalRing.closedPoint Y₁.Fn)) := by
    have := congrArg (fun g : Sp Y₁.Fn ⟶ Y₂.X => g (IsLocalRing.closedPoint Y₁.Fn)) hl₁
    exact this.symm
  have h2 := (IsLocalRing.specializes_closedPoint
    (spMap (algebraMap V Y₁.Fn) (IsLocalRing.closedPoint Y₁.Fn))).map l.l.continuous
  convert h2 using 1
  exact e2.symm

end GlobalTheory.FlagBundle
