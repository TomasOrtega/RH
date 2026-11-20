import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardDecompositionGroupEqLocalDegree
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FCardDecompositionGroupEqLocalDegree.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.card_decomposition_group_eq_local_degree : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (v w : HeightOneSpectrum (𝓞 E)), v ∈ placesOver E l → w ∈ placesOver E l → Nat.card (MulAction.stabilizer (E ≃ₐ[ℚ] E) v.asIdeal) = locDeg E w := by
  first | exact @GlobalTheory.DecompCard.card_stabilizer_eq_locDeg | exact GlobalTheory.DecompCard.card_stabilizer_eq_locDeg | (intros; apply GlobalTheory.DecompCard.card_stabilizer_eq_locDeg <;> assumption)
