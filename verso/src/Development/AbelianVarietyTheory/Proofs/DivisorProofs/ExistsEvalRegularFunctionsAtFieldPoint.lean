import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

/- English proof (translation)
Introduce `F _ Y Z _ k _ w`. Use `set z := w (IsLocalRing.closedPoint k) with hz`. Set `ι` to `algebraMap (Z.presheaf.stalk z) Z.functionField`. Establish `hι : Function.Injective ι` using `FaithfulSMul.algebraMap_injective _ _`. Set `e : Z.presheaf.stalk z ≃+* ι.range` to `RingEquiv.ofBijective ι.rangeRestrict ⟨fun a b hab => hι (congrArg Subtype.val hab), fun u => by`.

Take `⟨a, ha⟩` from `u.2`. Conclude with `⟨a, Subtype.ext ha⟩⟩`. Set `s : Z.presheaf.stalk z →+* k` to `(Scheme.stalkClosedPointTo (R := .of k) w).hom`. Use `haveI : IsLocalHom s := Scheme.isLocalHom_stalkClosedPointTo' w`. Establish `he : ∀ a, e.symm ⟨ι a, ⟨a, rfl⟩⟩ = a` using `fun a => e.symm_apply_eq.2 rfl`.

Use `⟨s.comp e.symm.toRingHom, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨_, a, rfl⟩`. Express the relevant statement in the definitionally equal form `s (e.symm ⟨ι a, ⟨a, rfl⟩⟩) ≠ 0 ↔ _`. Rewrite using `[he]`. Prove the components needed by the constructor for the conclusion.

Introduce `h0`. Conclude with `⟨a, isUnit_of_map_unit s a (isUnit_iff_ne_zero.2 h0), rfl⟩`. Introduce and unpack `⟨b, hb, hba⟩`. Rewrite using `[← hι hba]`. Conclude with `(hb.map s).ne_zero`.

Introduce `q _ u ⟨a, ha⟩`. Substitute `ha` using the available equality. Establish `hm` using `functionFieldMap_algebraMap q z a`. Use `⟨⟨_, hm.symm⟩, ?_⟩` and prove the remaining obligations. Establish `h1 : (⟨functionFieldMap q (algebraMap _ Y.X.functionField a), ⟨_, hm.symm⟩⟩ : ι.range) = ⟨ι ((q.stalkMap z).hom a), ⟨_, rfl⟩⟩` using `Subtype.ext hm`.

Express the relevant statement in the definitionally equal form `s (e.symm _) = _`. Rewrite using `[h1, he]`. Establish `hw : w ≫ q = spMap (s.comp (q.stalkMap z).hom) ≫ Y.X.fromSpecStalk (q z)` using `by conv_lhs => rw [← spMap_stalkClosedPointTo w]`. Rewrite using `[Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc]`. Use `congr 1`.

Rewrite using `[spMap, spMap, ← Spec.map_comp]`. Both sides reduce to the same expression. Establish `hv` using `val_ratOf (Y := Y) (s.comp (q.stalkMap z).hom) a`. Conclude with `hv.symm.trans (congrArg (fun p => (ratOf Y).val p (algebraMap _ Y.X.functionField a)) hw.symm)`.
-/
theorem exists_eval_regular_at_fieldPoint :
    ∀ (F : Type) [Field F] (Y : Var F) (Z : Scheme.{0}) [IsIntegral Z] (k : Type) [Field k] (w : Sp k ⟶ Z),
      ∃ ev : (algebraMap (Z.presheaf.stalk (w (IsLocalRing.closedPoint k))) Z.functionField).range →+* k,
        (∀ u, ev u ≠ 0 ↔ UnitAt (w (IsLocalRing.closedPoint k)) (u : Z.functionField)) ∧
        ∀ (q : Z ⟶ Y.X) [IsDominant q] (u : Y.Fn), RegAt (q (w (IsLocalRing.closedPoint k))) u →
          ∃ h, ev ⟨functionFieldMap q u, h⟩ = (ratOf Y).val (w ≫ q) u := by
  intro F _ Y Z _ k _ w
  set z := w (IsLocalRing.closedPoint k) with hz
  let ι := algebraMap (Z.presheaf.stalk z) Z.functionField
  have hι : Function.Injective ι := FaithfulSMul.algebraMap_injective _ _
  let e : Z.presheaf.stalk z ≃+* ι.range := RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun a b hab => hι (congrArg Subtype.val hab), fun u => by
      obtain ⟨a, ha⟩ := u.2
      exact ⟨a, Subtype.ext ha⟩⟩
  let s : Z.presheaf.stalk z →+* k := (Scheme.stalkClosedPointTo (R := .of k) w).hom
  haveI : IsLocalHom s := Scheme.isLocalHom_stalkClosedPointTo' w
  have he : ∀ a, e.symm ⟨ι a, ⟨a, rfl⟩⟩ = a := fun a => e.symm_apply_eq.2 rfl
  refine ⟨s.comp e.symm.toRingHom, ?_, ?_⟩
  · rintro ⟨_, a, rfl⟩
    change s (e.symm ⟨ι a, ⟨a, rfl⟩⟩) ≠ 0 ↔ _
    rw [he]
    constructor
    · intro h0
      exact ⟨a, isUnit_of_map_unit s a (isUnit_iff_ne_zero.2 h0), rfl⟩
    · rintro ⟨b, hb, hba⟩
      rw [← hι hba]
      exact (hb.map s).ne_zero
  · intro q _ u ⟨a, ha⟩
    subst ha
    have hm := functionFieldMap_algebraMap q z a
    refine ⟨⟨_, hm.symm⟩, ?_⟩
    have h1 : (⟨functionFieldMap q (algebraMap _ Y.X.functionField a), ⟨_, hm.symm⟩⟩ : ι.range) =
        ⟨ι ((q.stalkMap z).hom a), ⟨_, rfl⟩⟩ := Subtype.ext hm
    change s (e.symm _) = _
    rw [h1, he]
    have hw : w ≫ q = spMap (s.comp (q.stalkMap z).hom) ≫ Y.X.fromSpecStalk (q z) := by
      conv_lhs => rw [← spMap_stalkClosedPointTo w]
      rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc]
      congr 1
      rw [spMap, spMap, ← Spec.map_comp]
      rfl
    have hv := val_ratOf (Y := Y) (s.comp (q.stalkMap z).hom) a
    exact hv.symm.trans (congrArg (fun p => (ratOf Y).val p (algebraMap _ Y.X.functionField a)) hw.symm)

end GlobalTheory.FlagPush
