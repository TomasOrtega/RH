import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOneOfChartGenerators

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.PullReg

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {Ω' : Type} [Field Ω']

/- English proof (translation)
Establish `e : ζ = Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫ X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω))`. Rewrite using `[hζ, Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]`. Establish `hl : IsLocalHom (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i).hom`. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Establish `h1 : IsUnit (i ((Scheme.stalkClosedPointTo ξ).hom a))` using `ha`.

Establish `h2 : IsUnit ((Scheme.stalkClosedPointTo ξ).hom a : Ω)` using `isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at h1`. Conclude with `isUnit_of_map_unit (Scheme.stalkClosedPointTo ξ).hom a h2`. Substitute `e` using the available equality. Conclude with `Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk _ U hU`.
-/
theorem germ_stalkClosedPointTo_baseChange (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω →+* Ω')
    (ζ : Spec (CommRingCat.of Ω') ⟶ X) (hζ : ζ = Spec.map (CommRingCat.ofHom i) ≫ ξ) (U : X.Opens)
    (hU : ζ (IsLocalRing.closedPoint (CommRingCat.of Ω')) ∈ U) (hU' : genPt ξ ∈ U) :
    X.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo ζ =
      X.presheaf.germ U (genPt ξ) hU' ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
  have e : ζ = Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
      X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω)) := by
    rw [hζ, Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have hl : IsLocalHom (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i).hom := by
    refine ⟨fun a ha => ?_⟩
    have h1 : IsUnit (i ((Scheme.stalkClosedPointTo ξ).hom a)) := ha
    have h2 : IsUnit ((Scheme.stalkClosedPointTo ξ).hom a : Ω) :=
      isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at h1
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo ξ).hom a h2
  subst e
  exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk _ U hU

/- English proof (translation)
Establish `key : f.stalkMap p'.1 ≫ X'.presheaf.stalkSpecializes p'.2 ≫ Scheme.stalkClosedPointTo ξ' = X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i`. Use `TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_` and prove the remaining obligations. Establish `hg : genPt ξ ∈ U` using `h.mem_open U.2 hU`. Establish `hg' : (ξ' ≫ f) (IsLocalRing.closedPoint (CommRingCat.of Ω')) ∈ U`. Establish `: (ξ' ≫ f) (IsLocalRing.closedPoint (CommRingCat.of Ω')) = genPt ξ` using `(Scheme.Hom.comp_apply ξ' f _).trans hD.map_genPt`.

Rewrite using `[this]`. Conclude with `hg`. Establish `e` using `germ_stalkClosedPointTo_baseChange ξ i (ξ' ≫ f) hD U hg' hg`. Rewrite `e` using `[Scheme.stalkClosedPointTo_comp]`. Establish `e3 : f.stalkMap p'.1 ≫ X'.presheaf.stalkSpecializes p'.2 ≫ Scheme.stalkClosedPointTo ξ' = X.presheaf.stalkSpecializes (p'.2.map f.continuous) ≫ f.stalkMap (genPt ξ') ≫ Scheme.stalkClosedPointTo ξ'` using `(Scheme.Hom.stalkSpecializes_stalkMap_assoc f _ _ p'.2 _).symm`.

Rewrite using `[e3, TopCat.Presheaf.germ_stalkSpecializes_assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc]`. Conclude with `e`. Conclude with `congrArg (fun φ => φ.hom s) key`.
-/
theorem stalkMap_comp_genMap {X' : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'} (hD : Dominates ξ' ξ f i)
    (p' : Cpt ξ') (h : genPt ξ ⤳ f p'.1) (s : X.presheaf.stalk (f p'.1)) :
    genMap ξ' p' ((f.stalkMap p'.1).hom s) = i (genMap ξ ⟨f p'.1, h⟩ s) := by
  have key : f.stalkMap p'.1 ≫ X'.presheaf.stalkSpecializes p'.2 ≫ Scheme.stalkClosedPointTo ξ' =
      X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
    refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
    have hg : genPt ξ ∈ U := h.mem_open U.2 hU
    have hg' : (ξ' ≫ f) (IsLocalRing.closedPoint (CommRingCat.of Ω')) ∈ U := by
      have : (ξ' ≫ f) (IsLocalRing.closedPoint (CommRingCat.of Ω')) = genPt ξ :=
        (Scheme.Hom.comp_apply ξ' f _).trans hD.map_genPt
      rw [this]; exact hg
    have e := germ_stalkClosedPointTo_baseChange ξ i (ξ' ≫ f) hD U hg' hg
    rw [Scheme.stalkClosedPointTo_comp] at e
    have e3 : f.stalkMap p'.1 ≫ X'.presheaf.stalkSpecializes p'.2 ≫ Scheme.stalkClosedPointTo ξ' =
        X.presheaf.stalkSpecializes (p'.2.map f.continuous) ≫ f.stalkMap (genPt ξ') ≫
          Scheme.stalkClosedPointTo ξ' :=
      (Scheme.Hom.stalkSpecializes_stalkMap_assoc f _ _ p'.2 _).symm
    rw [e3, TopCat.Presheaf.germ_stalkSpecializes_assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc]
    exact e
  exact congrArg (fun φ => φ.hom s) key

end GlobalTheory.CompanionTheory.Ar.Flat.PullReg

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Introduce `X Ω _ ξ X' Ω' _ ξ' f i hD p'`. Establish `h` using `hD.specializes p'`. Establish `hreg : ∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p'`. Introduce and unpack `_ ⟨s, rfl⟩`. Conclude with `⟨_, PullReg.stalkMap_comp_genMap hD p' h s⟩`.

Use `⟨h, hreg, fun L t ht => ⟨(map_ne_zero i).2 ht.1, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Lat.pull_apply L hD]`. Establish `hL : L ⟨f p'.1, hD.specializes p'⟩ = Submodule.span (regAt ξ ⟨f p'.1, h⟩) {t}` using `ht.2`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨e, he, rfl⟩`. Establish `he' : e ∈ Submodule.span (regAt ξ ⟨f p'.1, h⟩) {t}`. Rewrite using `[← hL]`. Conclude with `he`. Take `⟨r, rfl⟩` from `Submodule.mem_span_singleton.1 he'`.

Use `Submodule.mem_span_singleton.2 ⟨⟨i r, hreg _ r.2⟩, ?_⟩` and prove the remaining obligations. Use `show i (r : Ω) * i t = i ((r : Ω) * t)`. Rewrite using `[map_mul]`. Rewrite using `[Submodule.span_singleton_le_iff_mem]`. Use `Submodule.subset_span ⟨t, ?_, rfl⟩` and prove the remaining obligations.

Use `show t ∈ (L ⟨f p'.1, hD.specializes p'⟩ : Set Ω)`. Rewrite using `[hL]`. Conclude with `Submodule.mem_span_singleton_self t`.
-/
theorem pull_reg_and_gen : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0})
    (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'),
    Dominates ξ' ξ f i → ∀ p' : Cpt ξ', ∃ h : genPt ξ ⤳ f p'.1,
      (∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p') ∧
        ∀ (L : Lat ξ Ω) (t : Ω), L.IsGenAt ⟨f p'.1, h⟩ t →
          (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' (i t) := by
  intro X Ω _ ξ X' Ω' _ ξ' f i hD p'
  have h := hD.specializes p'
  have hreg : ∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p' := by
    rintro _ ⟨s, rfl⟩
    exact ⟨_, PullReg.stalkMap_comp_genMap hD p' h s⟩
  refine ⟨h, hreg, fun L t ht => ⟨(map_ne_zero i).2 ht.1, ?_⟩⟩
  rw [Lat.pull_apply L hD]
  have hL : L ⟨f p'.1, hD.specializes p'⟩ = Submodule.span (regAt ξ ⟨f p'.1, h⟩) {t} := ht.2
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    have he' : e ∈ Submodule.span (regAt ξ ⟨f p'.1, h⟩) {t} := by
      rw [← hL]; exact he
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 he'
    refine Submodule.mem_span_singleton.2 ⟨⟨i r, hreg _ r.2⟩, ?_⟩
    show i (r : Ω) * i t = i ((r : Ω) * t)
    rw [map_mul]
  · rw [Submodule.span_singleton_le_iff_mem]
    refine Submodule.subset_span ⟨t, ?_, rfl⟩
    show t ∈ (L ⟨f p'.1, hD.specializes p'⟩ : Set Ω)
    rw [hL]
    exact Submodule.mem_span_singleton_self t

end GlobalTheory.CompanionTheory.Ar.Flat
