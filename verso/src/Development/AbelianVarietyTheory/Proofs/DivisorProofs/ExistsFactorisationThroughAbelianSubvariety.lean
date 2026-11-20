import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjSmoothOfGeometricallyReduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeometricallyIntegralImageOfHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubgroupSchemeOfGeometricallyIntegralImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFieldSmoothOfRelativeDimensionExistStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Introduce `K _ A B f`. Take `⟨Z, p, i, hpi, hp, hi, hg⟩` from `GlobalTheory.T.exists_geometricallyIntegral_image_of_hom K A B f`. Take `⟨hG, hpm, him⟩` from `GlobalTheory.T.exists_subgroupScheme_of_geometricallyIntegral_image K A B f Z p i hpi hp hi hg`. Use `letI := hG`. Establish `hmono : Mono i`.

Establish `: Mono i.left` using `inferInstance`. Conclude with `Over.mono_of_mono_left i`. Establish `hcomm : IsCommMonObj Z` using `⟨by`. Apply `(cancel_mono i).1` to reduce the goal to its premises. Rewrite using `[Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]⟩`.

Establish `hw : i.left ≫ B.X.hom = Z.hom` using `Over.w i`. Establish `hB` using `B.ab`. Establish `: Smooth B.X.hom` using `hB.smooth`. Establish `: IsProper B.X.hom` using `hB.proper`. Establish `hlft : LocallyOfFiniteType Z.hom` using `by rw [← hw]; infer_instance`.

Establish `hpr : IsProper Z.hom` using `by rw [← hw]; infer_instance`. Establish `hsm : Smooth Z.hom` using `GlobalTheory.grpObj_smooth_of_geometricallyReduced K Z hlft inferInstance`. Establish `hgc : GeometricallyConnected Z.hom` using `⟨fun L _ y W fst snd h => by`. Establish `: IsIntegral W` using `hg.geometrically_isIntegral y fst snd h`. Use the proof step `infer_instance⟩`.

Establish `hab : IsAbelianScheme Z` using `⟨hcomm, hsm, hpr, hgc⟩`. Take `⟨g, hd⟩` from `GlobalTheory.T.abelianScheme_field_smoothOfRelativeDimension_exists K Z hab`. Set `C : AbVar K` to `{ X := Z, ab := hab, dim := g, smooth := hd }`. Use `⟨C, Hom.mk (B := C) p, Hom.mk (A := C) i, hp, hi, ?_⟩` and prove the remaining obligations. Conclude with `hom_ext hpi`.
-/
theorem exists_factor_abelianSubvariety : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    ∃ (C : AbVar K) (p : A ⟶ C) (i : C ⟶ B), Surjective p.hom.left ∧ IsClosedImmersion i.hom.left ∧ p ≫ i = f := by
  intro K _ A B f
  obtain ⟨Z, p, i, hpi, hp, hi, hg⟩ := GlobalTheory.T.exists_geometricallyIntegral_image_of_hom K A B f
  obtain ⟨hG, hpm, him⟩ := GlobalTheory.T.exists_subgroupScheme_of_geometricallyIntegral_image K A B f Z p i hpi hp hi hg
  letI := hG
  have hmono : Mono i := by
    have : Mono i.left := inferInstance
    exact Over.mono_of_mono_left i
  have hcomm : IsCommMonObj Z := ⟨by
    apply (cancel_mono i).1
    rw [Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]⟩
  have hw : i.left ≫ B.X.hom = Z.hom := Over.w i
  have hB := B.ab
  have : Smooth B.X.hom := hB.smooth
  have : IsProper B.X.hom := hB.proper
  have hlft : LocallyOfFiniteType Z.hom := by rw [← hw]; infer_instance
  have hpr : IsProper Z.hom := by rw [← hw]; infer_instance
  have hsm : Smooth Z.hom := GlobalTheory.grpObj_smooth_of_geometricallyReduced K Z hlft inferInstance
  have hgc : GeometricallyConnected Z.hom := ⟨fun L _ y W fst snd h => by
    have : IsIntegral W := hg.geometrically_isIntegral y fst snd h
    infer_instance⟩
  have hab : IsAbelianScheme Z := ⟨hcomm, hsm, hpr, hgc⟩
  obtain ⟨g, hd⟩ := GlobalTheory.T.abelianScheme_field_smoothOfRelativeDimension_exists K Z hab
  let C : AbVar K := { X := Z, ab := hab, dim := g, smooth := hd }
  refine ⟨C, Hom.mk (B := C) p, Hom.mk (A := C) i, hp, hi, ?_⟩
  exact hom_ext hpi

end GlobalTheory.AV.AbVar
