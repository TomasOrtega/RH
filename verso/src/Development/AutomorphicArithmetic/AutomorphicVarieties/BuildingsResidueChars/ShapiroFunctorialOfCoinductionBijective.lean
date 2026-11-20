import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology

open CategoryTheory UpperTheory.V.Af.CohB in
/- English proof (translation)
Introduce `hi hs Γ X Y _ _ _ p hp y hy d ξ`. Set `e` to `LinearEquiv.ofBijective (toCo p hp y ξ) ⟨hi Γ X Y p hp y hy d ξ, hs Γ X Y p hp y hy d ξ⟩`. Establish `he : ∀ g : Γ, e.toLinearMap ∘ₗ funRep X ξ g = Representation.coind (MulAction.stabilizer Γ y).subtype (fibRep p hp y ξ) g ∘ₗ e.toLinearMap`. Introduce `g`. Use `LinearMap.ext fun f => Subtype.ext (funext fun h => funext fun x => ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `funRep X ξ h (funRep X ξ g f) x.1 = funRep X ξ (h * g) f x.1`. Rewrite using `[map_mul]`. Both sides reduce to the same expression. Set `i : Rep.of (funRep X ξ) ≅ Rep.coind (MulAction.stabilizer Γ y).subtype (Rep.of (fibRep p hp y ξ))` to `Rep.mkIso (Representation.Equiv.mk e he)`. Unfold `totCoh`.

Use `congr 1`. Use function extensionality and compare the values at `q`. Conclude with `(((groupCohomology.functor ℂ Γ q).mapIso i) ≪≫ groupCohomology.coindIso (Rep.of (fibRep p hp y ξ)) q).toLinearEquiv.rank_eq`.
-/
theorem UpperTheory.shapiro_functorial_of_coinduction_bijective :
    UpperTheory.V.Af.CohB.ToCoInj → UpperTheory.V.Af.CohB.ToCoSurj → UpperTheory.V.Af.CohB.ShapiroFun := by
  intro hi hs Γ X Y _ _ _ p hp y hy d ξ
  let e := LinearEquiv.ofBijective (toCo p hp y ξ) ⟨hi Γ X Y p hp y hy d ξ, hs Γ X Y p hp y hy d ξ⟩
  have he : ∀ g : Γ, e.toLinearMap ∘ₗ funRep X ξ g =
      Representation.coind (MulAction.stabilizer Γ y).subtype (fibRep p hp y ξ) g ∘ₗ e.toLinearMap := by
    intro g
    refine LinearMap.ext fun f => Subtype.ext (funext fun h => funext fun x => ?_)
    change funRep X ξ h (funRep X ξ g f) x.1 = funRep X ξ (h * g) f x.1
    rw [map_mul]
    rfl
  let i : Rep.of (funRep X ξ) ≅ Rep.coind (MulAction.stabilizer Γ y).subtype (Rep.of (fibRep p hp y ξ)) :=
    Rep.mkIso (Representation.Equiv.mk e he)
  unfold totCoh
  congr 1
  funext q
  exact (((groupCohomology.functor ℂ Γ q).mapIso i) ≪≫
    groupCohomology.coindIso (Rep.of (fibRep p hp y ξ)) q).toLinearEquiv.rank_eq
