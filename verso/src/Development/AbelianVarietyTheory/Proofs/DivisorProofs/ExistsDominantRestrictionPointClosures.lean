import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

/- English proof (translation)
Introduce `X Y π y`. Use `set i := cloι (π y)`. Use `set j := cloι y`. Establish `hi : i (genericPoint (clo (π y))) = π y` using `cloι_genericPoint _`. Establish `hj : j (genericPoint (clo y)) = y` using `cloι_genericPoint _`.

Establish `hr : Set.range i = closure {π y}`. Establish `h₁` using `(genericPoint_spec (clo (π y))).image i.continuous`. Rewrite `h₁` using `[Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi]`. Conclude with `h₁.def.symm`. Establish `: Surjective (Limits.pullback.snd i (j ≫ π))` using `⟨by`.

Rewrite using `[← Set.range_eq_univ, Scheme.Pullback.range_snd, hr]`. Use `Set.eq_univ_of_forall fun w => ?_` and prove the remaining obligations. Use `((genericPoint_specializes w).map (j ≫ π).continuous)` as an intermediate fact. Rewrite using `[Set.mem_preimage]`. Establish `e : (j ≫ π) (genericPoint (clo y)) = π y`.

Rewrite using `[Scheme.Hom.comp_apply, hj]`. Rewrite `this` using `[e]`. Conclude with `this.mem_closure⟩`. Use `isIso_of_isClosedImmersion_of_surjective (Limits.pullback.snd i (j ≫ π))` as an intermediate fact. Use `⟨inv (Limits.pullback.snd i (j ≫ π)) ≫ Limits.pullback.fst i (j ≫ π), ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc]`. Apply `i.isClosedEmbedding.injective` to reduce the goal to its premises. Rewrite using `[← Scheme.Hom.comp_apply, Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc, Scheme.Hom.comp_apply, hj, hi]`. Introduce `w`. Establish `e₁` using `GlobalTheory.CurveDegreesCompare.residueDegree_comp (inv (Limits.pullback.snd i (j ≫ π)) ≫ Limits.pullback.fst i (j ≫ π)) i w`.

Establish `e₂` using `GlobalTheory.CurveDegreesCompare.residueDegree_comp j π w`. Rewrite `e₁` using `[Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc, GlobalTheory.Published.residueDegree_of_isClosedImmersion i, one_mul]`. Rewrite `e₂` using `[GlobalTheory.Published.residueDegree_of_isClosedImmersion j, mul_one]`. Rewrite using `[← e₁, e₂]`.
-/
theorem clo_restrict_dominant : ∀ (X Y : Scheme.{0}) (π : Y ⟶ X) (y : Y), ∃ g : clo y ⟶ clo (π y), g ≫ cloι (π y) = cloι y ≫ π ∧ g (genericPoint _) = genericPoint _ ∧ ∀ w : clo y, g.residueDegree w = π.residueDegree (cloι y w) := by
  intro X Y π y
  set i := cloι (π y)
  set j := cloι y
  have hi : i (genericPoint (clo (π y))) = π y := cloι_genericPoint _
  have hj : j (genericPoint (clo y)) = y := cloι_genericPoint _
  have hr : Set.range i = closure {π y} := by
    have h₁ := (genericPoint_spec (clo (π y))).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi] at h₁
    exact h₁.def.symm
  have : Surjective (Limits.pullback.snd i (j ≫ π)) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, hr]
    refine Set.eq_univ_of_forall fun w => ?_
    have := ((genericPoint_specializes w).map (j ≫ π).continuous)
    rw [Set.mem_preimage]
    have e : (j ≫ π) (genericPoint (clo y)) = π y := by
      rw [Scheme.Hom.comp_apply, hj]
    rw [e] at this
    exact this.mem_closure⟩
  have := isIso_of_isClosedImmersion_of_surjective (Limits.pullback.snd i (j ≫ π))
  refine ⟨inv (Limits.pullback.snd i (j ≫ π)) ≫ Limits.pullback.fst i (j ≫ π), ?_, ?_, ?_⟩
  · rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc]
  · apply i.isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc,
      Scheme.Hom.comp_apply, hj, hi]
  · intro w
    have e₁ := GlobalTheory.CurveDegreesCompare.residueDegree_comp (inv (Limits.pullback.snd i (j ≫ π)) ≫ Limits.pullback.fst i (j ≫ π)) i w
    have e₂ := GlobalTheory.CurveDegreesCompare.residueDegree_comp j π w
    rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc,
      GlobalTheory.Published.residueDegree_of_isClosedImmersion i, one_mul] at e₁
    rw [GlobalTheory.Published.residueDegree_of_isClosedImmersion j, mul_one] at e₂
    rw [← e₁, e₂]

end GlobalTheory.MixHt
