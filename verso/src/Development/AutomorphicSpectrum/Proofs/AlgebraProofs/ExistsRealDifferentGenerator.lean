import Mathlib
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.WeilBound.CoreStatements.SesquilinearFractions.DifferentIdealEqTopOfUnramified
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `PositivityTheory.Xgf.exists_real_different_generator` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FSesquilinearFractions%2FDifferentIdealEqTopOfUnramified.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_real_different_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ p : Nat.Primes, ∃ δ ∈ differentIdeal ℤ (𝓞 E), δ ≠ 0 ∧ IsCMField.complexConj E (δ : E) = δ ∧ ∀ j : E →+* ℂ_[p], Real.log ‖j (δ : E)‖ = logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  first | exact @PositivityTheory.Xgf.exists_real_different_generator | exact PositivityTheory.Xgf.exists_real_different_generator
