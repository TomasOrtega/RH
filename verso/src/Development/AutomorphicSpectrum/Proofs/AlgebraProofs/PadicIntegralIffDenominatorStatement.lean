import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicIntegralIffDenominator
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FPadicIntegralIffDenominator.lean&line=70#L70)
-/
theorem _root_.GlobalTheory.T.padic_integral_iff_denominator : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (x : E), ((∀ j : E →+* ℂ_[p], ‖j x‖ ≤ 1) ↔ ∃ (n : ℕ) (a : 𝓞 E), ¬ (p : ℕ) ∣ n ∧ (n : E) * x = a) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.padic_integral_iff_denominator | exact GlobalTheory.CompanionTheory.Relay.padic_integral_iff_denominator | (intros; apply GlobalTheory.CompanionTheory.Relay.padic_integral_iff_denominator <;> assumption)
