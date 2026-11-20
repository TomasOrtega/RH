import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralZeroOfTwistedPeriodic
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TwistIntegral.setIntegral_eq_zero_of_twist` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegralZeroOfTwistedPeriodic.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.integral_zero_of_twisted_periodic : ∀ {g : ℕ} (M : Submodule ℤ (Fl g)), IsLat M → ∀ (D : Set (Fl g)), IsAddFundamentalDomain M D volume → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (ψ : Fl g → V) (l₀ : Fl g) (a : ℂ), (∀ l ∈ M, ∀ x, ψ (x + l) = ψ x) → (∀ x, ψ (x + l₀) = a • ψ x) → a ≠ 1 → ∫ x in D, ψ x = 0 := by
  first | exact @GlobalTheory.TwistIntegral.setIntegral_eq_zero_of_twist | exact GlobalTheory.TwistIntegral.setIntegral_eq_zero_of_twist | (intros; apply GlobalTheory.TwistIntegral.setIntegral_eq_zero_of_twist <;> assumption)
