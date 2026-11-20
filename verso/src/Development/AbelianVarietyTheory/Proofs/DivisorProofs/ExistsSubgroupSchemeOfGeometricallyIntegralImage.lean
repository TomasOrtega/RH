import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftOfReducedOfSupport
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Take `⟨e, he⟩` from `GlobalTheory.lift_of_reduced_of_support i.left g.left (fun t => by`. Take `⟨t', rfl⟩` from `hq.surj t`. Apply `i.left.range_subset_ker_support` to reduce the goal to its premises. Use `⟨r.left t', ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← Over.comp_left, ← h, Over.comp_left, Scheme.Hom.comp_apply])`.

Conclude with `⟨Over.homMk e (by rw [← Over.w i, ← Category.assoc, he, Over.w g]), Over.OverMorphism.ext he⟩`.
-/
theorem exists_lift_of_surjective_of_isReduced {K : Type} [Field K] {T T' Z Y : Over (Sp K)}
    (i : Z ⟶ Y) [IsClosedImmersion i.left] [IsReduced T.left] (q : T' ⟶ T) (g : T ⟶ Y) (r : T' ⟶ Z)
    (hq : Surjective q.left) (h : q ≫ g = r ≫ i) : ∃ e : T ⟶ Z, e ≫ i = g := by
  obtain ⟨e, he⟩ := GlobalTheory.lift_of_reduced_of_support i.left g.left (fun t => by
    obtain ⟨t', rfl⟩ := hq.surj t
    apply i.left.range_subset_ker_support
    refine ⟨r.left t', ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ← h, Over.comp_left, Scheme.Hom.comp_apply])
  exact ⟨Over.homMk e (by rw [← Over.w i, ← Category.assoc, he, Over.w g]), Over.OverMorphism.ext he⟩

/- English proof (translation)
Introduce `K _ A B f Z p i hf hp hi hZ`. Establish `hmono : Mono i` using `Over.mono_of_mono_left i`. Use `haveI : IsIntegral Z.left := GeometricallyIntegral.isIntegral_of_subsingleton Z.hom`. Use `haveI := B.smooth`. Use `haveI : Smooth B.X.hom := SmoothOfRelativeDimension.smooth B.dim _`.

Use `haveI : LocallyOfFiniteType Z.hom := by rw [← Over.w i]; infer_instance`. Use `haveI : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom`. Use `haveI : IsReduced (Z ⊗ Z).left := (inferInstance : IsReduced (pullback Z.hom Z.hom))`. Use `haveI : MorphismProperty.IsStableUnderComposition @Surjective := ⟨fun f g hf hg => by haveI := hf; haveI := hg; infer_instance⟩`. Establish `hpp : Surjective (p ⊗ₘ p).left` using `MorphismProperty.pullbackMap (P := @Surjective) hp hp (Over.w p).symm (Over.w p).symm`.

Establish `hinv : ι[A.X] ≫ f.hom = f.hom ≫ ι[B.X]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨m, hm⟩` from `exists_lift_of_surjective_of_isReduced i (p ⊗ₘ p) ((i ⊗ₘ i) ≫ μ[B.X]) (μ[A.X] ≫ p) hpp (by`. Rewrite using `[← Category.assoc, tensorHom_comp_tensorHom, hf, ← IsMonHom.mul_hom, Category.assoc, hf])`. Take `⟨v, hv⟩` from `exists_lift_of_surjective_of_isReduced i p (i ≫ ι[B.X]) (ι[A.X] ≫ p) hp (by`.

Rewrite using `[← Category.assoc, hf, Category.assoc, hf, hinv])`. Establish `h1 : (η[A.X] ≫ p) ≫ i = η[B.X]` using `by rw [Category.assoc, hf, IsMonHom.one_hom]`. Establish `h1a : η[A.X] ≫ p ≫ i = η[B.X]` using `by rw [← Category.assoc, h1]`. Use `letI M : MonObj Z := { one := η[A.X] ≫ p mul := m one_mul := by`. Rewrite using `[← cancel_mono i, Category.assoc, hm, ← tensorHom_id, tensorHom_comp_tensorHom_assoc, h1, Category.id_comp, tensorHom_def', Category.assoc, MonObj.one_mul, leftUnitor_naturality]`.

Use `mul_one := by`. Rewrite using `[← cancel_mono i, Category.assoc, hm, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, h1, Category.id_comp, MonoidalCategory.tensorHom_def, Category.assoc, MonObj.mul_one, rightUnitor_naturality]`. Use `mul_assoc := by`. Rewrite using `[← cancel_mono i]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Category.assoc, hm, ← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]`. Use `_ = ((i ⊗ₘ i) ⊗ₘ i) ≫ (α_ _ _ _).hom ≫ B.X ◁ μ[B.X] ≫ μ[B.X] := by rw [MonObj.mul_assoc]`. Use `_ = (α_ Z Z Z).hom ≫ (i ⊗ₘ (i ⊗ₘ i)) ≫ B.X ◁ μ[B.X] ≫ μ[B.X] := by`. Rewrite using `[associator_naturality_assoc]`. Use `_ = ((α_ Z Z Z).hom ≫ Z ◁ m ≫ m) ≫ i := by`.

Simplify using `only [Category.assoc, hm, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id] }`. Use `letI G : GrpObj Z := { inv := v left_inv := by`. Rewrite using `[← cancel_mono i, Category.assoc]`. Express the relevant statement in the definitionally equal form `lift v (𝟙 Z) ≫ m ≫ i = (toUnit Z ≫ η[A.X] ≫ p) ≫ i`. Rewrite using `[hm, lift_map_assoc, hv, Category.id_comp, show lift (i ≫ ι[B.X]) i = i ≫ lift ι[B.X] (𝟙 B.X) by rw [comp_lift, Category.comp_id], Category.assoc, GrpObj.left_inv, ← Category.assoc, comp_toUnit]`.

Simplify using `only [Category.assoc, h1a]`. Use `right_inv := by`. Rewrite using `[← cancel_mono i, Category.assoc]`. Express the relevant statement in the definitionally equal form `lift (𝟙 Z) v ≫ m ≫ i = (toUnit Z ≫ η[A.X] ≫ p) ≫ i`. Rewrite using `[hm, lift_map_assoc, hv, Category.id_comp, show lift i (i ≫ ι[B.X]) = i ≫ lift (𝟙 B.X) ι[B.X] by rw [comp_lift, Category.comp_id], Category.assoc, GrpObj.right_inv, ← Category.assoc, comp_toUnit]`.

Simplify using `only [Category.assoc, h1a] }`. Use `⟨G, ⟨rfl, ?_⟩, ⟨h1, hm⟩⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `μ[A.X] ≫ p = (p ⊗ₘ p) ≫ m`. Rewrite using `[← cancel_mono i, Category.assoc, Category.assoc, hm, hf, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, hf]`.
-/
theorem exists_grpObj_of_image :
    ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (Z : Over (Sp K)) (p : A.X ⟶ Z) (i : Z ⟶ B.X), p ≫ i = f.hom → Surjective p.left → IsClosedImmersion i.left → GeometricallyIntegral Z.hom → ∃ _ : GrpObj Z, IsMonHom p ∧ IsMonHom i := by
  intro K _ A B f Z p i hf hp hi hZ
  have hmono : Mono i := Over.mono_of_mono_left i
  haveI : IsIntegral Z.left := GeometricallyIntegral.isIntegral_of_subsingleton Z.hom
  haveI := B.smooth
  haveI : Smooth B.X.hom := SmoothOfRelativeDimension.smooth B.dim _
  haveI : LocallyOfFiniteType Z.hom := by rw [← Over.w i]; infer_instance
  haveI : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  haveI : IsReduced (Z ⊗ Z).left := (inferInstance : IsReduced (pullback Z.hom Z.hom))
  haveI : MorphismProperty.IsStableUnderComposition @Surjective :=
    ⟨fun f g hf hg => by haveI := hf; haveI := hg; infer_instance⟩
  have hpp : Surjective (p ⊗ₘ p).left :=
    MorphismProperty.pullbackMap (P := @Surjective) hp hp (Over.w p).symm (Over.w p).symm
  have hinv : ι[A.X] ≫ f.hom = f.hom ≫ ι[B.X] := by
    calc ι[A.X] ≫ f.hom = (𝟙 A.X)⁻¹ ≫ f.hom := by rw [Hom.inv_def, Category.id_comp]
      _ = (𝟙 A.X ≫ f.hom)⁻¹ := GrpObj.inv_comp _ _
      _ = f.hom ≫ ι[B.X] := by rw [Category.id_comp, Hom.inv_def]
  obtain ⟨m, hm⟩ := exists_lift_of_surjective_of_isReduced i (p ⊗ₘ p) ((i ⊗ₘ i) ≫ μ[B.X]) (μ[A.X] ≫ p) hpp (by
    rw [← Category.assoc, tensorHom_comp_tensorHom, hf, ← IsMonHom.mul_hom, Category.assoc, hf])
  obtain ⟨v, hv⟩ := exists_lift_of_surjective_of_isReduced i p (i ≫ ι[B.X]) (ι[A.X] ≫ p) hp (by
    rw [← Category.assoc, hf, Category.assoc, hf, hinv])
  have h1 : (η[A.X] ≫ p) ≫ i = η[B.X] := by rw [Category.assoc, hf, IsMonHom.one_hom]
  have h1a : η[A.X] ≫ p ≫ i = η[B.X] := by rw [← Category.assoc, h1]
  letI M : MonObj Z :=
    { one := η[A.X] ≫ p
      mul := m
      one_mul := by
        rw [← cancel_mono i, Category.assoc, hm, ← tensorHom_id, tensorHom_comp_tensorHom_assoc, h1,
          Category.id_comp, tensorHom_def', Category.assoc, MonObj.one_mul, leftUnitor_naturality]
      mul_one := by
        rw [← cancel_mono i, Category.assoc, hm, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, h1,
          Category.id_comp, MonoidalCategory.tensorHom_def, Category.assoc, MonObj.mul_one, rightUnitor_naturality]
      mul_assoc := by
        rw [← cancel_mono i]
        calc (m ▷ Z ≫ m) ≫ i = ((i ⊗ₘ i) ⊗ₘ i) ≫ μ[B.X] ▷ B.X ≫ μ[B.X] := by
              simp only [Category.assoc, hm, ← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp,
                Category.comp_id]
          _ = ((i ⊗ₘ i) ⊗ₘ i) ≫ (α_ _ _ _).hom ≫ B.X ◁ μ[B.X] ≫ μ[B.X] := by rw [MonObj.mul_assoc]
          _ = (α_ Z Z Z).hom ≫ (i ⊗ₘ (i ⊗ₘ i)) ≫ B.X ◁ μ[B.X] ≫ μ[B.X] := by
              rw [associator_naturality_assoc]
          _ = ((α_ Z Z Z).hom ≫ Z ◁ m ≫ m) ≫ i := by
              simp only [Category.assoc, hm, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp,
                Category.comp_id] }
  letI G : GrpObj Z :=
    { inv := v
      left_inv := by
        rw [← cancel_mono i, Category.assoc]
        change lift v (𝟙 Z) ≫ m ≫ i = (toUnit Z ≫ η[A.X] ≫ p) ≫ i
        rw [hm, lift_map_assoc, hv, Category.id_comp,
          show lift (i ≫ ι[B.X]) i = i ≫ lift ι[B.X] (𝟙 B.X) by rw [comp_lift, Category.comp_id],
          Category.assoc, GrpObj.left_inv, ← Category.assoc, comp_toUnit]
        simp only [Category.assoc, h1a]
      right_inv := by
        rw [← cancel_mono i, Category.assoc]
        change lift (𝟙 Z) v ≫ m ≫ i = (toUnit Z ≫ η[A.X] ≫ p) ≫ i
        rw [hm, lift_map_assoc, hv, Category.id_comp,
          show lift i (i ≫ ι[B.X]) = i ≫ lift (𝟙 B.X) ι[B.X] by rw [comp_lift, Category.comp_id],
          Category.assoc, GrpObj.right_inv, ← Category.assoc, comp_toUnit]
        simp only [Category.assoc, h1a] }
  refine ⟨G, ⟨rfl, ?_⟩, ⟨h1, hm⟩⟩
  change μ[A.X] ≫ p = (p ⊗ₘ p) ≫ m
  rw [← cancel_mono i, Category.assoc, Category.assoc, hm, hf, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, hf]

end GlobalTheory.AV.AbVar
