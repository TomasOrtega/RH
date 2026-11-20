import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivisorCycleListAdditive
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FDivisorCycleListAdditive.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.divisor_cycle_list_additive : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (a : K → ℕ) (f : MRing ι O), IsMultiHomog f a → f ∉ P → ∀ (b b' : K → ℤ) (l : List (K → ℤ)), l.length + 1 = d → cycList (divCycle P f) ((b + b') :: l) = cycList (divCycle P f) (b :: l) + cycList (divCycle P f) (b' :: l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.cycList_divCycle_add_first | exact GlobalTheory.CompanionTheory.Ar.Num.cycList_divCycle_add_first | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.cycList_divCycle_add_first <;> assumption)
