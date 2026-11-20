import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection

noncomputable section

open Filter Topology

namespace UpperTheory.V.Cj.H

set_option maxHeartbeats 400000 in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem absSolve : AbsSolve := by
  intro I J L c cn hcn hlim
  classical
  let ψ : (J →₀ ℂ) →ₗ[ℂ] (I →₀ ℂ) := Finsupp.linearCombination ℂ L
  let φ : (J →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ c
  have hsum : ∀ (b : I → ℂ) (v : I →₀ ℂ),
      (v.sum fun i x => x * b i) = Finsupp.linearCombination ℂ b v := by
    intro b v
    rw [Finsupp.linearCombination_apply]
    rfl
  have hcomp : ∀ (b : I → ℂ), (Finsupp.linearCombination ℂ b) ∘ₗ ψ
      = Finsupp.linearCombination ℂ (fun j => Finsupp.linearCombination ℂ b (L j)) := by
    intro b
    apply Finsupp.lhom_ext
    intro j x
    simp [ψ, Finsupp.linearCombination_single]
  have hker : LinearMap.ker ψ ≤ LinearMap.ker φ := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    have h0 : ∀ k, Finsupp.linearCombination ℂ (cn k) a = 0 := by
      intro k
      obtain ⟨b, hb⟩ := hcn k
      have h1 := congrArg (fun m => m a) (hcomp b)
      simp only [LinearMap.comp_apply, ha, map_zero] at h1
      rw [show cn k = fun j => Finsupp.linearCombination ℂ b (L j) from
        funext fun j => ((hsum b (L j)).symm.trans (hb j)).symm]
      exact h1.symm
    have hT : Tendsto (fun k => Finsupp.linearCombination ℂ (cn k) a) atTop (𝓝 (φ a)) := by
      simp only [φ, Finsupp.linearCombination_apply, Finsupp.sum]
      apply tendsto_finset_sum
      intro j _
      exact (hlim j).const_smul (a j)
    simp only [h0] at hT
    exact tendsto_nhds_unique hT tendsto_const_nhds
  let f0 : LinearMap.range ψ →ₗ[ℂ] ℂ :=
    ((LinearMap.ker ψ).liftQ φ hker) ∘ₗ
      (ψ.quotKerEquivRange.symm : LinearMap.range ψ →ₗ[ℂ] (J →₀ ℂ) ⧸ LinearMap.ker ψ)
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f0
  have hgψ : ∀ a, g (ψ a) = φ a := by
    intro a
    have h2 := congrArg (fun m => m ⟨ψ a, LinearMap.mem_range_self ψ a⟩) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h2
    rw [h2]
    simp [f0, LinearMap.quotKerEquivRange_symm_apply_image]
  have hgb : Finsupp.linearCombination ℂ (fun i => g (Finsupp.single i 1)) = g := by
    apply Finsupp.lhom_ext
    intro i x
    rw [Finsupp.linearCombination_single, ← map_smul, Finsupp.smul_single_one]
  refine ⟨fun i => g (Finsupp.single i 1), fun j => ?_⟩
  refine (hsum (fun i => g (Finsupp.single i 1)) (L j)).trans ?_
  rw [hgb]
  have h3 := hgψ (Finsupp.single j 1)
  simpa [ψ, φ, Finsupp.linearCombination_single] using h3

end UpperTheory.V.Cj.H
