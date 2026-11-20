import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfIsSchemeTheoreticallyDominantOfFractionRing

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Use `⟨fun L _ y W a b hW => ?_⟩` and prove the remaining obligations. Establish `hy : Flat y`. Take `⟨φ, rfl⟩` from `Spec.map_surjective y`. Conclude with `(HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.Flat.of_isField (Field.toIsField K) _)`. Establish `: Flat a` using `MorphismProperty.of_isPullback hW.flip hy`.

Establish `: IsReduced (pullback p a)` using `h.geometrically_isReduced y _ _ ((IsPullback.of_hasPullback p a).paste_vert hW)`. Conclude with `IsSchemeTheoreticallyDominant.isReduced (pullback.snd p a)`.
-/
theorem geometricallyReduced_of_schDominant_comp {K : Type} [Field K] {X Y : Scheme.{0}} (p : X ⟶ Y)
    (f : Y ⟶ Spec (.of K)) [IsSchemeTheoreticallyDominant p] [QuasiCompact p]
    [h : GeometricallyReduced (p ≫ f)] : GeometricallyReduced f := by
  refine ⟨fun L _ y W a b hW => ?_⟩
  have hy : Flat y := by
    obtain ⟨φ, rfl⟩ := Spec.map_surjective y
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.Flat.of_isField (Field.toIsField K) _)
  have : Flat a := MorphismProperty.of_isPullback hW.flip hy
  have : IsReduced (pullback p a) :=
    h.geometrically_isReduced y _ _ ((IsPullback.of_hasPullback p a).paste_vert hW)
  exact IsSchemeTheoreticallyDominant.isReduced (pullback.snd p a)

/- English proof (translation)
Use `⟨fun L _ y W a b hW => ?_⟩` and prove the remaining obligations. Establish `: IrreducibleSpace ↥(Limits.pullback p a)` using `h.geometrically_irreducibleSpace y _ _ ((IsPullback.of_hasPullback p a).paste_vert hW)`. Conclude with `Function.Surjective.irreducibleSpace (pullback.snd p a).continuous (pullback.snd p a).surjective`.
-/
theorem geometricallyIrreducible_of_surjective_comp {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z) [Surjective p]
    [h : GeometricallyIrreducible (p ≫ f)] : GeometricallyIrreducible f := by
  refine ⟨fun L _ y W a b hW => ?_⟩
  have : IrreducibleSpace ↥(Limits.pullback p a) :=
    h.geometrically_irreducibleSpace y _ _ ((IsPullback.of_hasPullback p a).paste_vert hW)
  exact Function.Surjective.irreducibleSpace (pullback.snd p a).continuous (pullback.snd p a).surjective

/- English proof (translation)
Introduce `K _ A B f`. Establish `hA` using `A.ab`. Establish `hB` using `B.ab`. Establish `: Smooth A.X.hom` using `hA.smooth`. Establish `: IsProper A.X.hom` using `hA.proper`.

Establish `: GeometricallyConnected A.X.hom` using `hA.geomConnected`. Establish `: IsProper B.X.hom` using `hB.proper`. Establish `hw : f.hom.left ≫ B.X.hom = A.X.hom` using `Over.w f.hom`. Establish `: IsProper (f.hom.left ≫ B.X.hom)` using `by rw [hw]; infer_instance`. Establish `: IsProper f.hom.left` using `IsProper.of_comp f.hom.left B.X.hom`.

Establish `: IsSchemeTheoreticallyDominant f.hom.left.toImage` using `GlobalTheory.isSchemeTheoreticallyDominant_toImage _`. Establish `hsurj : Surjective f.hom.left.toImage` using `⟨by`. Establish `h2 : IsClosed (Set.range f.hom.left.toImage)` using `f.hom.left.toImage.isClosedMap.isClosed_range`. Rewrite using `[← Set.range_eq_univ, ← h2.closure_eq]`. Conclude with `f.hom.left.toImage.denseRange.closure_range⟩`.

Establish `hwi : f.hom.left.toImage ≫ (f.hom.left.imageι ≫ B.X.hom) = A.X.hom`. Rewrite using `[Scheme.Hom.toImage_imageι_assoc, hw]`. Establish `: GeometricallyIntegral A.X.hom` using `GlobalTheory.geometricallyIntegral_of_smooth _`. Establish `: GeometricallyIntegral (f.hom.left.toImage ≫ (f.hom.left.imageι ≫ B.X.hom))`. Rewrite using `[hwi]`.

Use `infer_instance`. Use `geometricallyReduced_of_schDominant_comp f.hom.left.toImage (f.hom.left.imageι ≫ B.X.hom)` as an intermediate fact. Use `geometricallyIrreducible_of_surjective_comp f.hom.left.toImage (f.hom.left.imageι ≫ B.X.hom)` as an intermediate fact. Use `⟨Over.mk (f.hom.left.imageι ≫ B.X.hom), Over.homMk f.hom.left.toImage hwi, Over.homMk f.hom.left.imageι rfl, ?_, hsurj, ?_, ?_⟩` and prove the remaining obligations. Use `ext1`.

Simplify using the standard rewrite rules. Conclude with `inferInstanceAs (IsClosedImmersion f.hom.left.imageι)`. Use `show GeometricallyIntegral (f.hom.left.imageι ≫ B.X.hom)`. Conclude with `GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _`.
-/
theorem exists_image_geometricallyIntegral :
    ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), ∃ (Z : Over (Sp K)) (p : A.X ⟶ Z) (i : Z ⟶ B.X),
      p ≫ i = f.hom ∧ Surjective p.left ∧ IsClosedImmersion i.left ∧ GeometricallyIntegral Z.hom := by
  intro K _ A B f
  have hA := A.ab
  have hB := B.ab
  have : Smooth A.X.hom := hA.smooth
  have : IsProper A.X.hom := hA.proper
  have : GeometricallyConnected A.X.hom := hA.geomConnected
  have : IsProper B.X.hom := hB.proper
  have hw : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
  have : IsProper (f.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
  have : IsProper f.hom.left := IsProper.of_comp f.hom.left B.X.hom
  have : IsSchemeTheoreticallyDominant f.hom.left.toImage := GlobalTheory.isSchemeTheoreticallyDominant_toImage _
  have hsurj : Surjective f.hom.left.toImage := ⟨by
    have h2 : IsClosed (Set.range f.hom.left.toImage) := f.hom.left.toImage.isClosedMap.isClosed_range
    rw [← Set.range_eq_univ, ← h2.closure_eq]
    exact f.hom.left.toImage.denseRange.closure_range⟩
  have hwi : f.hom.left.toImage ≫ (f.hom.left.imageι ≫ B.X.hom) = A.X.hom := by
    rw [Scheme.Hom.toImage_imageι_assoc, hw]
  have : GeometricallyIntegral A.X.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have : GeometricallyIntegral (f.hom.left.toImage ≫ (f.hom.left.imageι ≫ B.X.hom)) := by
    rw [hwi]; infer_instance
  have := geometricallyReduced_of_schDominant_comp f.hom.left.toImage (f.hom.left.imageι ≫ B.X.hom)
  have := geometricallyIrreducible_of_surjective_comp f.hom.left.toImage (f.hom.left.imageι ≫ B.X.hom)
  refine ⟨Over.mk (f.hom.left.imageι ≫ B.X.hom), Over.homMk f.hom.left.toImage hwi,
    Over.homMk f.hom.left.imageι rfl, ?_, hsurj, ?_, ?_⟩
  · ext1
    simp
  · exact inferInstanceAs (IsClosedImmersion f.hom.left.imageι)
  · show GeometricallyIntegral (f.hom.left.imageι ≫ B.X.hom)
    exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

end GlobalTheory.AV.AbVar
