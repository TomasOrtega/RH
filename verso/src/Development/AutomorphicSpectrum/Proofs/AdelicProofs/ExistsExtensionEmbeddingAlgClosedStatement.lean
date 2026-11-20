import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.ExistsExtensionEmbeddingAlgClosed
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAdelicProofs%2FExistsExtensionEmbeddingAlgClosed.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_extension_embedding_alg_closed : ∀ (k k' A : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Field A] [CharZero A] [IsAlgClosed A] (f : k →+* k') (j : k →+* A), ∃ j' : k' →+* A, j'.comp f = j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.exists_comp_eq_of_numberField | exact GlobalTheory.CompanionTheory.Ar.Fl.exists_comp_eq_of_numberField | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.exists_comp_eq_of_numberField <;> assumption)
