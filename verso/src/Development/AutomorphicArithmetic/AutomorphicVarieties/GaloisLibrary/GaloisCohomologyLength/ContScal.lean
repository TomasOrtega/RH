import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QzTorsionZmodEmbeddingStatement

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem UpperTheory.V.LDataCardLeFinrank.contScal :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ψ : Γ →* ℤ_[l]ˣ), (Continuous fun g => ((ψ g : ℤ_[l]ˣ) : ℤ_[l])) → ContAction (scalRep (QZ l) ψ) := by
  intro l _ Γ _ _ ψ hψ
  haveI hd : DiscreteTopology (QZ l) := ⟨rfl⟩
  unfold ReciprocityTheory.Gal.ContAction
  apply continuous_prod_of_discrete_right.mpr
  intro a
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) a
  let q : ℚ_[l] → QZ l := fun z => Submodule.Quotient.mk z
  have hmk : Continuous q := by
    refine (continuous_discrete_rng (β := QZ l)).mpr ?_
    intro b
    obtain ⟨y, rfl⟩ : ∃ y, q y = b := Submodule.Quotient.mk_surjective (ZlSub l) b
    have e : q ⁻¹' {q y} = Metric.closedBall y 1 := by
      ext z
      have h1 : q z = q y ↔ z - y ∈ ZlSub l := Submodule.Quotient.eq (ZlSub l)
      rw [Set.mem_preimage, Set.mem_singleton_iff, h1, LinearMap.mem_range,
        Metric.mem_closedBall, dist_eq_norm]
      constructor
      · rintro ⟨w, hw⟩
        rw [← hw]
        exact w.norm_le_one
      · intro h
        exact ⟨⟨z - y, h⟩, rfl⟩
    rw [e]
    exact IsUltrametricDist.isOpen_closedBall y one_ne_zero
  have hc : Continuous fun g : Γ => ((ψ g : ℤ_[l]) : ℚ_[l]) * x :=
    (continuous_subtype_val.comp hψ).mul continuous_const
  refine (hmk.comp hc).congr ?_
  intro g
  rfl
