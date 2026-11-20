import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeSummandCriterion
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Num.summand_of_locFree_quot` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FLocallyFreeSummandCriterion.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.locally_free_summand_criterion : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {V : Type} [AddCommGroup V] [Module Ω V] (U : Submodule Ω V) (N m : ℕ) (L : AddSubgroup V), LocFree R N L → (LocFree R m (L.map U.mkQ.toAddMonoidHom) → Summand L U) ∧ (Summand L U → LocFree R (Module.finrank Ω U) (L.comap U.subtype.toAddMonoidHom) ∧ LocFree R (N - Module.finrank Ω U) (L.map U.mkQ.toAddMonoidHom)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.summand_of_locFree_quot | exact GlobalTheory.CompanionTheory.Ar.Num.summand_of_locFree_quot | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.summand_of_locFree_quot <;> assumption)
