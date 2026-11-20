import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicIndependentOfAdjoin
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitOfSumEqOne
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FAlgebraicIndependentOfAdjoin.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.algebraic_independent_of_adjoin : ∀ {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} [Finite ι] (u v : ι → K), AlgebraicIndependent Ω u → (∀ a, u a ∈ IntermediateField.adjoin Ω (Set.range v)) → AlgebraicIndependent Ω v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.algebraicIndependent_of_mem_adjoin_range | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.algebraicIndependent_of_mem_adjoin_range | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.algebraicIndependent_of_mem_adjoin_range <;> assumption)
