import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CtSplitOfParts

noncomputable section

open scoped TensorProduct Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PositivityTheory.SiegelWeilFormula.Act.CL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Apply `w.embedding.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2 w.embedding, h.2.2.2 w.embedding, star_star]`.
-/
theorem sigma_sigma_cm (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  apply w.embedding.injective
  rw [h.2.2.2 w.embedding, h.2.2.2 w.embedding, star_star]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨w⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Establish `hc : w.IsComplex` using `h.2.1.isComplex w`. Apply `InfinitePlace.not_isReal_iff_isComplex.2 hc` to reduce the goal to its premises.

Rewrite using `[InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Express the relevant statement in the definitionally equal form `star (w.embedding x) = w.embedding x`. Rewrite using `[← h.2.2.2 w.embedding, hne]`.
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
Break down `Int.units_eq_one_or ε with rfl | rfl` into its components or cases. Take `⟨x, hx⟩` from `exists_sigma_ne h`. Use `⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, sigma_sigma_cm h]`. Simplify using the standard rewrite rules.

Conclude with `⟨1, one_ne_zero, by simp⟩`.
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
