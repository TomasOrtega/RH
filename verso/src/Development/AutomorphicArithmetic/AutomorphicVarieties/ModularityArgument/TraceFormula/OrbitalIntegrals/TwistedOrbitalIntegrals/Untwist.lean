import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

/- English proof (translation)
Substitute using the available equality. Supply the required witnesses or components.
-/
private theorem aux {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μG : Measure G) (H H' : Subgroup G) (e : H' = H)
    (μ : Measure H) (hμ : μ.IsHaarMeasure) : ∃ μ' : Measure H', μ'.IsHaarMeasure ∧
      (∀ ρ, IsQuotNormaliser H' μ' ρ ↔ IsQuotNormaliser H μ ρ) ∧ ∀ F, quotIntegral μG H' μ' F = quotIntegral μG H μ F := by
  subst e
  exact ⟨μ, hμ, fun _ => Iff.rfl, fun _ => rfl⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Tf.Orb.untwist :
    UpperTheory.V.Z.Tf.Orb.Untwist := by
  intro k _ _ _ _ n _ _ μk γ
  have h1 : ∀ g : GL (Fin n) k, sigmaGL (1 : k ≃ₐ[k] k) g = g := fun g => by rw [sigmaGL_one]; rfl
  refine ⟨fun τ => ?_, h1, fun h => ?_, fun μ hμ => ?_⟩
  · have : τ = 1 := AlgEquiv.ext fun x => τ.commutes x
    rw [this]
    exact one_mem _
  · have : normGL (1 : k ≃ₐ[k] k) γ = γ := by
      rw [normGL, Module.finrank_self]
      simp [twNorm]
    rwa [IsTwRegSemisimple, this]
  · have e : twCent (sigmaGL (1 : k ≃ₐ[k] k)) γ = Subgroup.centralizer {γ} := by
      ext x
      rw [mem_twCent, h1, Subgroup.mem_centralizer_singleton_iff, mul_assoc, inv_mul_eq_iff_eq_mul, eq_comm]
    obtain ⟨μ', a, b, c⟩ := aux μk _ _ e μ hμ
    refine ⟨μ', a, b, fun f => ?_⟩
    rw [twOrbIntegralC, orbIntegralC, c]
    simp only [twConj, h1]
