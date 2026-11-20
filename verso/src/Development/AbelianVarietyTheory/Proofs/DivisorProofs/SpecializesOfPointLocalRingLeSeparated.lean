import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Establish `hgz : genericPoint X ⤳ z` using `(genericPoint_spec X).specializes trivial`. Establish `hgx : genericPoint X ⤳ x` using `(genericPoint_spec X).specializes trivial`. Establish `hinjz : Function.Injective (algebraMap (X.presheaf.stalk z) X.functionField)` using `IsFractionRing.injective _ _`. Set `ez : X.presheaf.stalk z ≃+* locRing z` to `RingEquiv.ofBijective (algebraMap (X.presheaf.stalk z) X.functionField).rangeRestrict ⟨fun _ _ e => hinjz (congrArg Subtype.val e), RingHom.rangeRestrict_surjective _⟩`. Set `φ : X.presheaf.stalk x →+* X.presheaf.stalk z` to `ez.symm.toRingHom.comp ((Subring.inclusion h).comp (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict)`.

Establish `hφ (a : X.presheaf.stalk x) : algebraMap (X.presheaf.stalk z) X.functionField (φ a) = algebraMap (X.presheaf.stalk x) X.functionField a`. Establish `e1 : ez (φ a) = Subring.inclusion h ((algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict a)`. Conclude with `ez.apply_symm_apply _`. Conclude with `congrArg Subtype.val e1`. Establish `key : X.presheaf.stalkSpecializes hgx = CommRingCat.ofHom φ ≫ X.presheaf.stalkSpecializes hgz`.

Use extensionality with `a`. Conclude with `(hφ a).symm`. Set `ι` to `Spec.map (X.presheaf.stalkSpecializes hgz)`. Establish `hdom : IsDominant ι`. Rewrite using `[isDominant_iff]`.

Use `show DenseRange (PrimeSpectrum.comap (X.presheaf.stalkSpecializes hgz).hom)`. Rewrite using `[PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot (X.presheaf.stalkSpecializes hgz).hom).1 hinjz]`. Conclude with `bot_le`. Set `g` to `Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x`. Establish `hfg : X.fromSpecStalk z = g`.

Use `ext_of_isDominant_of_isSeparated (Limits.terminal.from X) (Limits.terminal.hom_ext _ _) ι ?_` and prove the remaining obligations. Rewrite using `[Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgz]`. Simplify using `only [g, ι, ← Category.assoc, ← Spec.map_comp, ← key, Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgx]`. Establish `hz : z = g (IsLocalRing.closedPoint (X.presheaf.stalk z))`. Rewrite using `[← hfg, Scheme.fromSpecStalk_closedPoint]`.

Establish `hr : g (IsLocalRing.closedPoint (X.presheaf.stalk z)) ∈ Set.range (X.fromSpecStalk x)` using `⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩`. Rewrite `hr` using `[Scheme.range_fromSpecStalk]`. Rewrite using `[hz]`. Conclude with `hr`.
-/
theorem specializes_of_locRing_le (X : Scheme.{0}) [IsIntegral X] [X.IsSeparated] (x z : X)
    (h : locRing x ≤ locRing z) : z ⤳ x := by
  have hgz : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
  have hgx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hinjz : Function.Injective (algebraMap (X.presheaf.stalk z) X.functionField) :=
    IsFractionRing.injective _ _
  let ez : X.presheaf.stalk z ≃+* locRing z := RingEquiv.ofBijective
    (algebraMap (X.presheaf.stalk z) X.functionField).rangeRestrict
    ⟨fun _ _ e => hinjz (congrArg Subtype.val e), RingHom.rangeRestrict_surjective _⟩
  let φ : X.presheaf.stalk x →+* X.presheaf.stalk z :=
    ez.symm.toRingHom.comp
      ((Subring.inclusion h).comp (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict)
  have hφ (a : X.presheaf.stalk x) :
      algebraMap (X.presheaf.stalk z) X.functionField (φ a) =
        algebraMap (X.presheaf.stalk x) X.functionField a := by
    have e1 : ez (φ a) = Subring.inclusion h
        ((algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict a) := by
      exact ez.apply_symm_apply _
    exact congrArg Subtype.val e1
  have key : X.presheaf.stalkSpecializes hgx =
      CommRingCat.ofHom φ ≫ X.presheaf.stalkSpecializes hgz := by
    ext a
    exact (hφ a).symm
  let ι := Spec.map (X.presheaf.stalkSpecializes hgz)
  have hdom : IsDominant ι := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap (X.presheaf.stalkSpecializes hgz).hom)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot (X.presheaf.stalkSpecializes hgz).hom).1 hinjz]
    exact bot_le
  let g := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x
  have hfg : X.fromSpecStalk z = g := by
    refine ext_of_isDominant_of_isSeparated (Limits.terminal.from X)
      (Limits.terminal.hom_ext _ _) ι ?_
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgz]
    simp only [g, ι, ← Category.assoc, ← Spec.map_comp, ← key,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgx]
  have hz : z = g (IsLocalRing.closedPoint (X.presheaf.stalk z)) := by
    rw [← hfg, Scheme.fromSpecStalk_closedPoint]
  have hr : g (IsLocalRing.closedPoint (X.presheaf.stalk z)) ∈ Set.range (X.fromSpecStalk x) :=
    ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rw [Scheme.range_fromSpecStalk] at hr
  rw [hz]
  exact hr

end GlobalTheory
