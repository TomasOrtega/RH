import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotPowMaximalIdealDiscreteFinite
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NatQuot.quot_pow_maximalIdeal_discrete_finite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FQuotPowMaximalIdealDiscreteFinite.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.quotient_maximalIdeal_pow_discrete_and_finite : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O], PadicCoeff p O → ∀ k : ℕ, DiscreteTopology (O ⧸ IsLocalRing.maximalIdeal O ^ k) ∧ Finite (O ⧸ IsLocalRing.maximalIdeal O ^ k) := by
  first | exact @GlobalTheory.NatQuot.quot_pow_maximalIdeal_discrete_finite | exact GlobalTheory.NatQuot.quot_pow_maximalIdeal_discrete_finite | (intros; apply GlobalTheory.NatQuot.quot_pow_maximalIdeal_discrete_finite <;> assumption)
