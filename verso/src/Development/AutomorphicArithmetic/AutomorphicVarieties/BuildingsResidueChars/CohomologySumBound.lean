import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology

/- English proof (translation)
Use `Fintype.induction_empty_option (P := fun I _ => ∀ f : I → Cardinal.{0}, Cardinal.sum f = ∑ i, f i) ?_ ?_ ?_ I` and prove the remaining obligations. Introduce `α β _ e h f`. Use `letI : Fintype α := Fintype.ofEquiv β e.symm`. Rewrite using `[← Equiv.sum_comp e f, ← h]`. Conclude with `Cardinal.mk_congr (Equiv.sigmaCongrLeft (β := fun b => (f b).out) e).symm`.

Introduce `f`. Simplify using `[Cardinal.sum]`. Introduce `α _ h f`. Rewrite using `[Fintype.sum_option, ← h]`. Establish `e0 : (Σ o : Option α, (f o).out) ≃ (f none).out ⊕ (Σ a : α, (f (some a)).out)` using `{ toFun := fun x => match x with`.

Consider the case `⟨none, y⟩ => Sum.inl y`. Consider the case `⟨some a, y⟩ => Sum.inr ⟨a, y⟩`. Use `invFun := fun x => match x with`. Consider the case `Sum.inl y => ⟨none, y⟩`. Consider the case `Sum.inr ⟨a, y⟩ => ⟨some a, y⟩`.

Apply the tactic sequence `left_inv := by rintro ⟨_ | a, y⟩ <;> rfl`. Apply the tactic sequence `right_inv := by rintro (y | ⟨a, y⟩) <;> rfl }`. Establish `e` using `Cardinal.mk_congr e0`. Rewrite `e` using `[Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_out]`. Conclude with `e`.
-/
private theorem UpperTheory.V.Af.CohB.cardSum_eq (I : Type) [hI : Fintype I] :
    ∀ f : I → Cardinal.{0}, Cardinal.sum f = ∑ i, f i := by
  refine Fintype.induction_empty_option (P := fun I _ => ∀ f : I → Cardinal.{0}, Cardinal.sum f = ∑ i, f i)
    ?_ ?_ ?_ I
  · intro α β _ e h f
    letI : Fintype α := Fintype.ofEquiv β e.symm
    rw [← Equiv.sum_comp e f, ← h]
    exact Cardinal.mk_congr (Equiv.sigmaCongrLeft (β := fun b => (f b).out) e).symm
  · intro f
    simp [Cardinal.sum]
  · intro α _ h f
    rw [Fintype.sum_option, ← h]
    have e0 : (Σ o : Option α, (f o).out) ≃ (f none).out ⊕ (Σ a : α, (f (some a)).out) :=
      { toFun := fun x => match x with
          | ⟨none, y⟩ => Sum.inl y
          | ⟨some a, y⟩ => Sum.inr ⟨a, y⟩
        invFun := fun x => match x with
          | Sum.inl y => ⟨none, y⟩
          | Sum.inr ⟨a, y⟩ => ⟨some a, y⟩
        left_inv := by rintro ⟨_ | a, y⟩ <;> rfl
        right_inv := by rintro (y | ⟨a, y⟩) <;> rfl }
    have e := Cardinal.mk_congr e0
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_out] at e
    exact e

open CategoryTheory in
/- English proof (translation)
Introduce `Γ I _ _ A B π ι h q`. Set `F : Rep.{0} ℂ Γ ⥤ ModuleCat.{0} ℂ` to `groupCohomology.cochainsFunctor ℂ Γ ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{0} ℂ) (ComplexShape.up ℕ) q`. Establish `hF : ∑ i, F.map (π i) ≫ F.map (ι i) = 𝟙 (F.obj A)`. Rewrite using `[← F.map_id, ← h, F.map_sum]`. Simplify using `only [Functor.map_comp]`.

Express the relevant statement in the definitionally equal form `Module.rank ℂ (F.obj A) ≤ ∑ i, Module.rank ℂ (F.obj (B i))`. Set `φ : F.obj A →ₗ[ℂ] (∀ i, F.obj (B i))` to `LinearMap.pi fun i => (F.map (π i)).hom`. Establish `hφ : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Establish `h1` using `congrArg (fun f => ModuleCat.Hom.hom f x) hF`. Simplify using `only [ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] at h1`. Rewrite using `[← h1]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Establish `h2 : (F.map (π i)).hom x = 0` using `congrFun hx i`.

Rewrite using `[h2, map_zero]`. Establish `h3` using `LinearMap.rank_le_of_injective φ hφ`. Rewrite `h3` using `[rank_pi]`. Rewrite using `[← UpperTheory.V.Af.CohB.cardSum_eq]`. Simplify using `using h3`.
-/
theorem UpperTheory.cohomology_sum_bound :
    UpperTheory.V.Af.CohB.SumBound := by
  intro Γ I _ _ A B π ι h q
  let F : Rep.{0} ℂ Γ ⥤ ModuleCat.{0} ℂ :=
    groupCohomology.cochainsFunctor ℂ Γ ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{0} ℂ) (ComplexShape.up ℕ) q
  have hF : ∑ i, F.map (π i) ≫ F.map (ι i) = 𝟙 (F.obj A) := by
    rw [← F.map_id, ← h, F.map_sum]
    simp only [Functor.map_comp]
  change Module.rank ℂ (F.obj A) ≤ ∑ i, Module.rank ℂ (F.obj (B i))
  let φ : F.obj A →ₗ[ℂ] (∀ i, F.obj (B i)) := LinearMap.pi fun i => (F.map (π i)).hom
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 := congrArg (fun f => ModuleCat.Hom.hom f x) hF
    simp only [ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.sum_apply,
      LinearMap.comp_apply, LinearMap.id_apply] at h1
    rw [← h1]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h2 : (F.map (π i)).hom x = 0 := congrFun hx i
    rw [h2, map_zero]
  have h3 := LinearMap.rank_le_of_injective φ hφ
  rw [rank_pi] at h3
  rw [← UpperTheory.V.Af.CohB.cardSum_eq]
  simpa using h3
