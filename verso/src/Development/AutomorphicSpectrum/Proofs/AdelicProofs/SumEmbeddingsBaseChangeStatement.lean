import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SumEmbeddingsBaseChange
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAdelicProofs%2FSumEmbeddingsBaseChange.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.sum_embeddings_base_change : ∀ (k k' A : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Field A] [CharZero A] [IsAlgClosed A] (f : k →+* k') (F : (k →+* A) → ℝ), (Module.finrank ℚ k : ℝ) * ∑ j : k' →+* A, F (j.comp f) = (Module.finrank ℚ k' : ℝ) * ∑ j : k →+* A, F j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.finrank_mul_sum_comp_eq | exact GlobalTheory.CompanionTheory.Ar.Fl.finrank_mul_sum_comp_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.finrank_mul_sum_comp_eq <;> assumption)
