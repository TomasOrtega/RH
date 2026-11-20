import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicLogIdealMaxElement
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAdelicProofs%2FPadicLogIdealMaxElement.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.padic_logIdeal_max_element : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (j : 𝓞 E →+* ℂ_[p]) (I : Ideal (𝓞 E)), Function.Injective j → I ≠ ⊥ → ∃ a ∈ I, a ≠ 0 ∧ (∀ b ∈ I, ‖j b‖ ≤ ‖j a‖) ∧ logIdeal j I = Real.log ‖j a‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.exists_logIdeal_attained | exact GlobalTheory.CompanionTheory.Ar.Fl.exists_logIdeal_attained | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.exists_logIdeal_attained <;> assumption)
