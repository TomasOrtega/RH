import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfTraceDualElement
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.traceDual_integral_of_not_dvd_discr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLiftOfTraceDualElement.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_lift_of_trace_dual_element : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime → ¬ (l : ℤ) ∣ discr E → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = σ y := by
  first | exact @GlobalTheory.traceDual_integral_of_not_dvd_discr | exact GlobalTheory.traceDual_integral_of_not_dvd_discr | (intros; apply GlobalTheory.traceDual_integral_of_not_dvd_discr <;> assumption)
