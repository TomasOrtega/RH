import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankLocalFieldEqCardDecompositionGroup
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocStab.finrank_adjoin_range_eq_card_stabilizer` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FFinrankLocalFieldEqCardDecompositionGroup.lean&line=290#L290)
-/
theorem _root_.GlobalTheory.T.finrank_local_field_eq_card_decomposition_group : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (c : E →+* PadicAlgCl l) [IsGalois ℚ E] (v : HeightOneSpectrum (𝓞 E)), (∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1) → Module.finrank ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range c)) = Nat.card (MulAction.stabilizer (E ≃ₐ[ℚ] E) v.asIdeal) := by
  first | exact @GlobalTheory.LocStab.finrank_adjoin_range_eq_card_stabilizer | exact GlobalTheory.LocStab.finrank_adjoin_range_eq_card_stabilizer | (intros; apply GlobalTheory.LocStab.finrank_adjoin_range_eq_card_stabilizer <;> assumption)
