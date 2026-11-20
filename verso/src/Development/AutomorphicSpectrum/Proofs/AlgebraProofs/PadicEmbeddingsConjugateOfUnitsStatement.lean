import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicEmbeddingsConjugateOfUnits
import Mathlib
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
open NumberField IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FPadicEmbeddingsConjugateOfUnits.lean&line=150#L150)
-/
theorem _root_.GlobalTheory.T.padic_embeddings_conjugate_of_units : ∀ (K : Type) [Field K] [NumberField K] (p : Nat.Primes) (κ κ' : K →+* ℂ_[p]), (∀ a : K, ‖κ a‖ ≤ 1 ↔ ‖κ' a‖ ≤ 1) → ∃ g : ℂ_[p] ≃+* ℂ_[p], (∀ z, ‖g z‖ = ‖z‖) ∧ ∀ a, g (κ a) = κ' a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.Conj.exists_isometry_conj_of_unit_ball | exact GlobalTheory.CompanionTheory.Ar.Br.Conj.exists_isometry_conj_of_unit_ball | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.Conj.exists_isometry_conj_of_unit_ball <;> assumption)
