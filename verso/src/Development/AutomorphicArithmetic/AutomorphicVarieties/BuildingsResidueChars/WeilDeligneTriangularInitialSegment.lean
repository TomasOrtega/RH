import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs

open Module

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem UpperTheory.weilDeligne_triangular_initial_segment :
    UpperTheory.V.Af.Wd.TriInit := by
  intro k W ι _ _ _ n T d hT
  obtain ⟨b, hb⟩ := hT
  have hp : ∀ a x, b.coord (Fin.last n) (T a x) = d a (Fin.last n) * b.coord (Fin.last n) x := by
    intro a x
    have h : (b.coord (Fin.last n)) ∘ₗ (T a) = d a (Fin.last n) • b.coord (Fin.last n) := by
      refine b.ext fun j => ?_
      have h1 := (hb a).1 (Fin.last n) j
      have h2 := (hb a).2 (Fin.last n)
      rw [LinearMap.toMatrix_apply] at h1 h2
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self, smul_eq_mul]
      by_cases hj : j = Fin.last n
      · subst hj
        rw [h2]; simp
      · rw [h1 (lt_of_le_of_ne (Fin.le_last j) hj), Finsupp.single_apply, if_neg hj, mul_zero]
    simpa using LinearMap.congr_fun h x
  have hS : ∀ a, ∀ x ∈ LinearMap.ker (b.coord (Fin.last n)), T a x ∈ LinearMap.ker (b.coord (Fin.last n)) := by
    intro a x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hp, hx, mul_zero]
  refine ⟨LinearMap.ker (b.coord (Fin.last n)), hS, b.coord (Fin.last n), ?_, rfl, hp, ?_⟩
  · intro c
    exact ⟨c • b (Fin.last n), by simp⟩
  · let v : Fin n → LinearMap.ker (b.coord (Fin.last n)) := fun i =>
      ⟨b (Fin.castSucc i), by
        rw [LinearMap.mem_ker, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply,
          if_neg (Fin.castSucc_lt_last i).ne]⟩
    have hv : LinearIndependent k v := by
      apply LinearIndependent.of_comp (LinearMap.ker (b.coord (Fin.last n))).subtype
      exact b.linearIndependent.comp Fin.castSucc (Fin.castSucc_injective n)
    have key : ∀ x : LinearMap.ker (b.coord (Fin.last n)),
        x = ∑ i, b.repr (x : W) (Fin.castSucc i) • v i := by
      intro x
      apply Subtype.ext
      have hx : b.repr (x : W) (Fin.last n) = 0 := x.2
      have h := b.sum_repr (x : W)
      rw [Fin.sum_univ_castSucc, hx, zero_smul, add_zero] at h
      rw [Submodule.coe_sum]
      exact h.symm
    have hsp : ⊤ ≤ Submodule.span k (Set.range v) := by
      intro x _
      rw [key x]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    let b' := Basis.mk hv hsp
    have hb' : ∀ i, b' i = v i := fun i => Basis.mk_apply hv hsp i
    have hr : ∀ (x : LinearMap.ker (b.coord (Fin.last n))) i, b'.repr x i = b.repr (x : W) (Fin.castSucc i) := by
      intro x i
      have h := congrFun (b'.repr_sum_self fun i => b.repr (x : W) (Fin.castSucc i)) i
      simp only [hb'] at h
      rw [← key x] at h
      exact h
    have hm : ∀ a i j, LinearMap.toMatrix b' b' ((T a).restrict (hS a)) i j =
        LinearMap.toMatrix b b (T a) (Fin.castSucc i) (Fin.castSucc j) := by
      intro a i j
      rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hr, hb']
      rfl
    refine ⟨b', fun a => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
    · exact (hm a i j).trans ((hb a).1 _ _ (Fin.castSucc_lt_castSucc_iff.2 hij))
    · exact (hm a i i).trans ((hb a).2 _)
