import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction

noncomputable section

namespace UpperTheory.V.Lit.Dr

open groupCohomology

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Introduce a local definition for the expression. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem shiftOne : ShiftOne := by
  intro Γ M Ω Z _ _ _ _ _ _ _ ρM ρΩ ρZ ι π hι hπ hinj hsurj hex n w hw hlift
  classical
  choose y hy using fun i => hsurj (w i)
  have hker : ∀ i γ, π (ρΩ γ (y i) - y i) = 0 := by
    intro i γ
    rw [map_sub, hπ, hy, hw, sub_self]
  choose φ hφ using fun i γ => (hex (ρΩ γ (y i) - y i)).1 (hker i γ)
  have hcoc : ∀ i, φ i ∈ groupCohomology.cocycles₁ (Rep.of ρM) := by
    intro i
    rw [groupCohomology.mem_cocycles₁_iff]
    intro g h
    apply hinj
    rw [Rep.of_ρ]
    change ι (φ i (g * h)) = ι ((ρM g) (φ i h) + φ i g)
    rw [map_add, hι, hφ, hφ, hφ, map_mul, Module.End.mul_apply, map_sub]
    abel
  let v : Fin n → groupCohomology (Rep.of ρM) 1 :=
    fun i => (groupCohomology.H1π (Rep.of ρM)).hom ⟨φ i, hcoc i⟩
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : (∑ i, g i • v i) =
        (groupCohomology.H1π (Rep.of ρM)).hom (∑ i, g i • (⟨φ i, hcoc i⟩ : groupCohomology.cocycles₁ (Rep.of ρM))) := by
      simp only [map_sum, map_smul, v]
    rw [hsum, groupCohomology.H1π_eq_zero_iff] at hg
    obtain ⟨m, hm⟩ := hg
    have key : Subtype.val (∑ i, g i • (⟨φ i, hcoc i⟩ : groupCohomology.cocycles₁ (Rep.of ρM))) = ∑ i, g i • φ i := by
      rw [Submodule.coe_sum]
      rfl
    have hm' : ∀ γ, ρM γ m - m = ∑ i, g i • φ i γ := by
      intro γ
      have := congrFun hm γ
      rw [groupCohomology.d₀₁_hom_apply, Rep.of_ρ] at this
      rw [this]
      exact (congrFun key γ).trans (Finset.sum_apply _ _ _)
    have hzero := hlift g ⟨(∑ i, g i • y i) - ι m, ?_, ?_⟩
    · intro i
      rw [hzero]
      rfl
    · intro γ
      have h1 : ι (ρM γ m) - ι m = ∑ i, g i • (ρΩ γ (y i) - y i) := by
        rw [← map_sub, hm', map_sum]
        simp only [map_smul, hφ]
      rw [hι] at h1
      rw [map_sub, map_sum]
      simp only [map_smul]
      simp only [smul_sub, Finset.sum_sub_distrib] at h1
      rw [sub_eq_iff_eq_add] at h1
      rw [h1]
      abel
    · rw [map_sub, hex.apply_apply_eq_zero, sub_zero, map_sum]
      simp only [map_smul, hy]
  have := hli.cardinal_le_rank
  simpa using this

end UpperTheory.V.Lit.Dr
