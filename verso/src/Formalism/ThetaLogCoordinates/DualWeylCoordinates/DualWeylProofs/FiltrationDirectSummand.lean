import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.MemSpanStandardIffProjZero

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

/- English proof (translation)
Introduce `hA n _ M CF pi hpi`. Use `⟨Submodule.span ℤ (qb_basis hA CF ℤ '' {y | CF.mu y.1 ∈ pi}ᶜ), ?_⟩` and prove the remaining obligations. Rewrite using `[qb_Mpi_eq_image hA CF pi hpi]`. Prove the components needed by the constructor for the conclusion. Conclude with `(qb_basis hA CF ℤ).linearIndependent.disjoint_span_image disjoint_compl_right`.

Rewrite using `[codisjoint_iff, ← Submodule.span_union, ← Set.image_union, Set.union_compl_self, Set.image_univ]`. Conclude with `(qb_basis hA CF ℤ).span_eq`.
-/
theorem filtration_direct_summand_of : LemmaA → FiltrationDirectSummand := by
  intro hA n _ M CF pi hpi
  refine ⟨Submodule.span ℤ (qb_basis hA CF ℤ '' {y | CF.mu y.1 ∈ pi}ᶜ), ?_⟩
  rw [qb_Mpi_eq_image hA CF pi hpi]
  constructor
  · exact (qb_basis hA CF ℤ).linearIndependent.disjoint_span_image disjoint_compl_right
  · rw [codisjoint_iff, ← Submodule.span_union, ← Set.image_union, Set.union_compl_self, Set.image_univ]
    exact (qb_basis hA CF ℤ).span_eq

end Formalism.InvariantFactorPaths.ColumnFamilies
