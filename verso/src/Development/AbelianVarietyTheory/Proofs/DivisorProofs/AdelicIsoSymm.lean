import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry
open GlobalTheory.TrueGeo

namespace GlobalTheory.ShFam.GalCarry.Symm

section Fn

variable {F : Type} [Field F] {Y Y' : Var F}

/- English proof (translation)
Establish `h : f (genericPoint Y.X) ⤳ genericPoint Y'.X`. Rewrite using `[genericPoint_eq_of_isOpenImmersion f]`. Use `⟨(Y'.X.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint Y.X)).hom, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Y.X.fromSpecStalk _ ≫ f = Spec.map (Y'.X.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint Y.X)) ≫ Y'.X.fromSpecStalk _`. Rewrite using `[Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]`.
-/
theorem exists_fnMap (f : Y.X ⟶ Y'.X) [IsOpenImmersion f] :
    ∃ ψ : Y'.Fn →+* Y.Fn, genericPt Y ≫ f = spMap ψ ≫ genericPt Y' := by
  have h : f (genericPoint Y.X) ⤳ genericPoint Y'.X := by
    rw [genericPoint_eq_of_isOpenImmersion f]
  refine ⟨(Y'.X.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint Y.X)).hom, ?_⟩
  change Y.X.fromSpecStalk _ ≫ f =
    Spec.map (Y'.X.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint Y.X)) ≫ Y'.X.fromSpecStalk _
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

/- English proof (translation)
Establish `e : (spMap ψ ≫ spMap ψ') ≫ genericPt Y = 𝟙 _ ≫ genericPt Y`. Rewrite using `[Category.assoc, ← h', ← Category.assoc, ← h, Category.assoc, hfg, Category.comp_id, Category.id_comp]`. Establish `e1 : spMap ψ ≫ spMap ψ' = 𝟙 _` using `(cancel_mono (Y.X.fromSpecStalk (genericPoint Y.X))).1 e`. Establish `e2 : Spec.map (CommRingCat.ofHom ψ' ≫ CommRingCat.ofHom ψ) = Spec.map (𝟙 _)` using `(Spec.map_comp _ _).trans (e1.trans (Spec.map_id _).symm)`. Conclude with `RingHom.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective e2)) a`.
-/
theorem fnMap_inv {f : Y.X ⟶ Y'.X} {g : Y'.X ⟶ Y.X} (hfg : f ≫ g = 𝟙 _) {ψ : Y'.Fn →+* Y.Fn} {ψ' : Y.Fn →+* Y'.Fn}
    (h : genericPt Y ≫ f = spMap ψ ≫ genericPt Y') (h' : genericPt Y' ≫ g = spMap ψ' ≫ genericPt Y) (a : Y.Fn) :
    ψ (ψ' a) = a := by
  have e : (spMap ψ ≫ spMap ψ') ≫ genericPt Y = 𝟙 _ ≫ genericPt Y := by
    rw [Category.assoc, ← h', ← Category.assoc, ← h, Category.assoc, hfg, Category.comp_id, Category.id_comp]
  have e1 : spMap ψ ≫ spMap ψ' = 𝟙 _ := (cancel_mono (Y.X.fromSpecStalk (genericPoint Y.X))).1 e
  have e2 : Spec.map (CommRingCat.ofHom ψ' ≫ CommRingCat.ofHom ψ) = Spec.map (𝟙 _) :=
    (Spec.map_comp _ _).trans (e1.trans (Spec.map_id _).symm)
  exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective e2)) a

end Fn

/- English proof (translation)
Take `⟨⟨h1, h2, h3, h4⟩, hn, hc, hm, hl⟩` from `h`. Take `⟨ψ', h2'⟩` from `exists_fnMap φ.inv`. Establish `e1` using `fnMap_inv φ.hom_inv_id h2 h2'`. Establish `e2` using `fnMap_inv φ.inv_hom_id h2' h2`. Establish `hD : ∀ (y' : Y'.X) (g : Y.Fnˣ), A.D.IsEqn (φ.inv y') g → A'.D.IsEqn y' (Units.map (ψ' : Y.Fn →* Y'.Fn) g * (Units.map (ψ' : Y.Fn →* Y'.Fn) u)⁻¹)`.

Introduce `y' g hg`. Establish `he` using `Base.isEqn_eqn A'.D y'`. Establish `hy : φ.hom (φ.inv y') = y'`. Rewrite using `[← Scheme.Hom.comp_apply, Iso.inv_hom_id]`. Both sides reduce to the same expression.

Establish `h5` using `unitAt_map h2' ((h4 (φ.inv y') (eqn A'.D y') (by rw [hy]; exact he)).iff_unitAt.1 hg)`. Use `he.iff_unitAt.2 ?_` and prove the remaining obligations. Use `h5 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_inv_eq_inv_val, map_div₀, map_mul, e2]`. Rewrite using `[div_mul_eq_div_div_swap, div_eq_mul_inv (ψ' _)]`.

Use `⟨ψ', (Units.map (ψ' : Y.Fn →* Y'.Fn) u)⁻¹, ⟨(Iso.inv_comp_eq _).2 h1.symm, h2', h3.symm, hD⟩, hn.symm, hc.symm, ?_, ?_⟩` and prove the remaining obligations. Introduce `σ p' p hp g hg`. Establish `hp' : p'.1 = p.1 ≫ φ.hom`. Rewrite using `[hp, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]`. Establish `hg' : A.D.IsEqn (φ.inv (under p')) g`.

Establish `: under p = φ.inv (under p')`. Express the relevant statement in the definitionally equal form `p.1 _ = _`. Rewrite using `[hp]`. Both sides reduce to the same expression. Conclude with `this ▸ hg`.

Establish `h6` using `hm σ p p' hp' _ (hD _ g hg')`. Establish `e : Units.map (ψ : Y'.Fn →* Y.Fn) (Units.map (ψ' : Y.Fn →* Y'.Fn) g * (Units.map (ψ' : Y.Fn →* Y'.Fn) u)⁻¹) * u = g`. Use `ext`. Simplify using `[e1]`. Rewrite `h6` using `[e]`.

Conclude with `h6.symm`. Introduce `v ε y' y hy`. Establish `hy' : y'.1 = y.1 ≫ φ.hom`. Rewrite using `[hy, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]`. Establish `h6` using `hl v ε y y' hy'`.

Establish `hb : φ.hom (below y.1) = below y'.1`. Rewrite using `[hy']`. Both sides reduce to the same expression. Establish `h7` using `(Base.isEqn_eqn A.D (below y.1)).iff_unitAt.1 (h4 (below y.1) (eqn A'.D (below y'.1)) (by rw [hb]; exact Base.isEqn_eqn _ _))`. Use `set b : Y.Fn := ((Units.map (ψ : Y'.Fn →* Y.Fn) (eqn A'.D (below y'.1)) * u * (eqn A.D (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn) with hbdef`.

Establish `hbu : UnitAt (below y.1) b`. Use `h7 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hbdef, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]`. Establish `h8 : TrueGeo.valAt y.1 b⁻¹ = (TrueGeo.valAt y.1 b)⁻¹`. Simplify using `using (Base.valAt_zpow y.1 hbu).2 (-1)`.

Establish `hy2 : y'.1 ≫ φ.inv = y.1` using `hy.symm`. Establish `h9 : TrueGeo.valAt y'.1 (ψ' b⁻¹) = TrueGeo.valAt y.1 b⁻¹`. Rewrite using `[valAt_map h2' y'.1 (by rw [hy2]; exact hbu.inv.regAt), hy2]`. Establish `e : ((Units.map (ψ' : Y.Fn →* Y'.Fn) (eqn A.D (below y.1)) * (Units.map (ψ' : Y.Fn →* Y'.Fn) u)⁻¹ * (eqn A'.D (below y'.1))⁻¹ : Y'.Fnˣ) : Y'.Fn) = ψ' b⁻¹`. Rewrite using `[hbdef]`.

Simplify using `only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_inv_eq_inv_val, map_inv₀, map_mul, e2, mul_inv, inv_inv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, h9, h8, map_inv₀, Real.log_inv, h6]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem adlIso_symm (F : Type) [Field F] [NumberField F] (C : GlobalTheory.TrueGeo.CxSt F) (Y Y' : Var F)
    (A : GlobalTheory.TrueGeo.Adl C Y) (A' : GlobalTheory.TrueGeo.Adl C Y') (φ : Y.X ≅ Y'.X) (ψ : Y'.Fn →+* Y.Fn) (u : Y.Fnˣ)
    (h : AdlIso A A' φ ψ u) : ∃ (ψ' : Y.Fn →+* Y'.Fn) (u' : Y'.Fnˣ), AdlIso A' A φ.symm ψ' u' := by
  obtain ⟨⟨h1, h2, h3, h4⟩, hn, hc, hm, hl⟩ := h
  obtain ⟨ψ', h2'⟩ := exists_fnMap φ.inv
  have e1 := fnMap_inv φ.hom_inv_id h2 h2'
  have e2 := fnMap_inv φ.inv_hom_id h2' h2
  have hD : ∀ (y' : Y'.X) (g : Y.Fnˣ), A.D.IsEqn (φ.inv y') g → A'.D.IsEqn y'
      (Units.map (ψ' : Y.Fn →* Y'.Fn) g * (Units.map (ψ' : Y.Fn →* Y'.Fn) u)⁻¹) := by
    intro y' g hg
    have he := Base.isEqn_eqn A'.D y'
    have hy : φ.hom (φ.inv y') = y' := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
    have h5 := unitAt_map h2' ((h4 (φ.inv y') (eqn A'.D y') (by rw [hy]; exact he)).iff_unitAt.1 hg)
    refine he.iff_unitAt.2 ?_
    convert h5 using 1
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_inv_eq_inv_val, map_div₀, map_mul, e2]
    rw [div_mul_eq_div_div_swap, div_eq_mul_inv (ψ' _)]
  refine ⟨ψ', (Units.map (ψ' : Y.Fn →* Y'.Fn) u)⁻¹,
    ⟨(Iso.inv_comp_eq _).2 h1.symm, h2', h3.symm, hD⟩, hn.symm, hc.symm, ?_, ?_⟩
  · intro σ p' p hp g hg
    have hp' : p'.1 = p.1 ≫ φ.hom := by
      rw [hp, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hg' : A.D.IsEqn (φ.inv (under p')) g := by
      have : under p = φ.inv (under p') := by
        change p.1 _ = _
        rw [hp]; rfl
      exact this ▸ hg
    have h6 := hm σ p p' hp' _ (hD _ g hg')
    have e : Units.map (ψ : Y'.Fn →* Y.Fn)
        (Units.map (ψ' : Y.Fn →* Y'.Fn) g * (Units.map (ψ' : Y.Fn →* Y'.Fn) u)⁻¹) * u = g := by
      ext
      simp [e1]
    rw [e] at h6
    exact h6.symm
  · intro v ε y' y hy
    have hy' : y'.1 = y.1 ≫ φ.hom := by
      rw [hy, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have h6 := hl v ε y y' hy'
    have hb : φ.hom (below y.1) = below y'.1 := by
      rw [hy']; rfl
    have h7 := (Base.isEqn_eqn A.D (below y.1)).iff_unitAt.1
      (h4 (below y.1) (eqn A'.D (below y'.1)) (by rw [hb]; exact Base.isEqn_eqn _ _))
    set b : Y.Fn := ((Units.map (ψ : Y'.Fn →* Y.Fn) (eqn A'.D (below y'.1)) * u * (eqn A.D (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn)
      with hbdef
    have hbu : UnitAt (below y.1) b := by
      convert h7 using 1
      rw [hbdef, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]
    have h8 : TrueGeo.valAt y.1 b⁻¹ = (TrueGeo.valAt y.1 b)⁻¹ := by
      simpa using (Base.valAt_zpow y.1 hbu).2 (-1)
    have hy2 : y'.1 ≫ φ.inv = y.1 := hy.symm
    have h9 : TrueGeo.valAt y'.1 (ψ' b⁻¹) = TrueGeo.valAt y.1 b⁻¹ := by
      rw [valAt_map h2' y'.1 (by rw [hy2]; exact hbu.inv.regAt), hy2]
    have e : ((Units.map (ψ' : Y.Fn →* Y'.Fn) (eqn A.D (below y.1)) * (Units.map (ψ' : Y.Fn →* Y'.Fn) u)⁻¹ *
        (eqn A'.D (below y'.1))⁻¹ : Y'.Fnˣ) : Y'.Fn) = ψ' b⁻¹ := by
      rw [hbdef]
      simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_inv_eq_inv_val, map_inv₀, map_mul, e2,
        mul_inv, inv_inv]
      ring
    rw [e, h9, h8, map_inv₀, Real.log_inv, h6]
    ring

end GlobalTheory.ShFam.GalCarry.Symm
