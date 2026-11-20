import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.complex_conjugations_are_conjugate :
    UpperTheory.V.Sd.S2.ConjCc := by
  intro Ω _ _ _ a b ha hb
  obtain ⟨j, hj⟩ := ha
  obtain ⟨j', hj'⟩ := hb
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) j j'
    (Subsingleton.elim _ _)
  have h : ∀ x, j (σ.symm x) = j' x := fun x => by
    rw [← hσ]; rfl
  refine isConj_iff.2 ⟨σ, ?_⟩
  refine AlgEquiv.ext fun x => ?_
  apply j'.injective
  rw [hj', ← h, ← h]
  change j (σ.symm (σ (a (σ.symm x)))) = _
  rw [AlgEquiv.symm_apply_apply, hj]
