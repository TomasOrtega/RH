import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CtSplitOfParts

noncomputable section

open scoped TensorProduct Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PositivityTheory.SiegelWeilFormula.Act.CL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem sigma_sigma_cm (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  apply w.embedding.injective
  rw [h.2.2.2 w.embedding, h.2.2.2 w.embedding, star_star]

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_sigma_ne (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hne
  push_neg at hne
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hc : w.IsComplex := h.2.1.isComplex w
  apply InfinitePlace.not_isReal_iff_isComplex.2 hc
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  change star (w.embedding x) = w.embedding x
  rw [← h.2.2.2 w.embedding, hne]

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Supply the required witnesses or components.
-/
theorem deltaEx' (h : IsCMExt F E σ) (ε : ℤˣ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -(((ε : ℤ) : E) * δ) := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · obtain ⟨x, hx⟩ := exists_sigma_ne h
    refine ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
    rw [map_sub, sigma_sigma_cm h]
    simp
  · exact ⟨1, one_ne_zero, by simp⟩

end PositivityTheory.SiegelWeilFormula.Act.CL

end
