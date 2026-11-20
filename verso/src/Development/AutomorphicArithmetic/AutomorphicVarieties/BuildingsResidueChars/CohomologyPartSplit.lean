import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology

open CategoryTheory UpperTheory.V.Af.CohB

/- English proof (translation)
Introduce `Γ X I _ _ _ c hc d ξ`. Set `p : ∀ i, (X → Fin d → ℂ) →ₗ[ℂ] (↥(part c hc i) → Fin d → ℂ)` to `fun i => { toFun := fun f x => f x.1 map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Set `e : ∀ i, (↥(part c hc i) → Fin d → ℂ) →ₗ[ℂ] (X → Fin d → ℂ)` to `fun i => { toFun := fun f x => if h : c x = i then f ⟨x, h⟩ else 0 map_add' := fun f g => funext fun x => by`. Apply the tactic sequence `by_cases h : c x = i <;> simp [h]`. Use the proof step `map_smul' := fun a f => funext fun x => by`.

Apply the tactic sequence `by_cases h : c x = i <;> simp [h] }`. Use `⟨fun i => Rep.ofHom ⟨p i, fun γ => ?_⟩, fun i => Rep.ofHom ⟨e i, fun γ => ?_⟩, ?_⟩` and prove the remaining obligations. Use `LinearMap.ext fun f => funext fun x => ?_` and prove the remaining obligations. Both sides reduce to the same expression. Use `LinearMap.ext fun f => funext fun x => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(if h : c x = i then (funRep ↥(part c hc i) ξ γ f) ⟨x, h⟩ else 0) = Matrix.mulVec (ξ γ) (if h : c (γ⁻¹ • x) = i then f ⟨γ⁻¹ • x, h⟩ else 0)`. Distinguish the cases in `h : c x = i`. Rewrite using `[dif_pos h, dif_pos ((hc _ _).trans h)]`. Both sides reduce to the same expression. Rewrite using `[dif_neg h, dif_neg (fun h' => h ((hc _ _).symm.trans h')), Matrix.mulVec_zero]`.

Apply `Rep.hom_ext` to reduce the goal to its premises. Rewrite using `[Rep.sum_hom]`. Apply `Representation.IntertwiningMap.ext` to reduce the goal to its premises. Use `LinearMap.ext fun f => funext fun x => ?_` and prove the remaining obligations. Rewrite using `[Representation.IntertwiningMap.toLinearMap_sum, LinearMap.sum_apply, Finset.sum_apply]`.

Express the relevant statement in the definitionally equal form `∑ i, (if h : c x = i then f x else 0) = f x`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.cohomology_part_split :
    UpperTheory.V.Af.CohB.PartSplit := by
  classical
  intro Γ X I _ _ _ c hc d ξ
  let p : ∀ i, (X → Fin d → ℂ) →ₗ[ℂ] (↥(part c hc i) → Fin d → ℂ) := fun i =>
    { toFun := fun f x => f x.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let e : ∀ i, (↥(part c hc i) → Fin d → ℂ) →ₗ[ℂ] (X → Fin d → ℂ) := fun i =>
    { toFun := fun f x => if h : c x = i then f ⟨x, h⟩ else 0
      map_add' := fun f g => funext fun x => by
        by_cases h : c x = i <;> simp [h]
      map_smul' := fun a f => funext fun x => by
        by_cases h : c x = i <;> simp [h] }
  refine ⟨fun i => Rep.ofHom ⟨p i, fun γ => ?_⟩, fun i => Rep.ofHom ⟨e i, fun γ => ?_⟩, ?_⟩
  · refine LinearMap.ext fun f => funext fun x => ?_
    rfl
  · refine LinearMap.ext fun f => funext fun x => ?_
    change (if h : c x = i then (funRep ↥(part c hc i) ξ γ f) ⟨x, h⟩ else 0) =
      Matrix.mulVec (ξ γ) (if h : c (γ⁻¹ • x) = i then f ⟨γ⁻¹ • x, h⟩ else 0)
    by_cases h : c x = i
    · rw [dif_pos h, dif_pos ((hc _ _).trans h)]
      rfl
    · rw [dif_neg h, dif_neg (fun h' => h ((hc _ _).symm.trans h')), Matrix.mulVec_zero]
  · apply Rep.hom_ext
    rw [Rep.sum_hom]
    apply Representation.IntertwiningMap.ext
    refine LinearMap.ext fun f => funext fun x => ?_
    rw [Representation.IntertwiningMap.toLinearMap_sum, LinearMap.sum_apply, Finset.sum_apply]
    change ∑ i, (if h : c x = i then f x else 0) = f x
    simp
