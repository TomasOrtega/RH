import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.cohomology_bounded_equiv :
    UpperTheory.V.Af.CohB.BddEquiv := by
  intro Γ Γ' _ _ ⟨φ⟩ ⟨c, hc⟩
  refine ⟨c, fun A => ?_⟩
  have key := hc (Rep.res φ.toMonoidHom A)
  have heq : ∀ q, Module.rank ℂ (groupCohomology (Rep.res φ.toMonoidHom A) q) =
      Module.rank ℂ (groupCohomology A q) := fun q =>
    ((groupCohomology.mapIso φ (LinearEquiv.refl ℂ A.V) (fun g => rfl) q).toLinearEquiv).rank_eq
  unfold UpperTheory.V.Af.CohB.totCoh at key ⊢
  simp only [heq] at key
  exact key
