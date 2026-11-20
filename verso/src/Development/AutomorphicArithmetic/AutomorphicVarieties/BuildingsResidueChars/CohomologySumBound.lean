import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Treat this case separately.

Treat this case separately. Treat this case separately. Treat this case separately. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Express the relevant assertion in an equivalent form by its definition. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
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
