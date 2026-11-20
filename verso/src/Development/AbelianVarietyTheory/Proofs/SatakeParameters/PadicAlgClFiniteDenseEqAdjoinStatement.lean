import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicAlgClFiniteDenseEqAdjoin
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FPadicAlgClFiniteDenseEqAdjoin.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.padicAlgCl_finite_dense_eq_adjoin' : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (c : E →+* PadicAlgCl l) (K : IntermediateField ℚ_[l] (PadicAlgCl l)), (∀ x, c x ∈ K) → FiniteDimensional ℚ_[l] K → (K : Set (PadicAlgCl l)) ⊆ closure (Set.range c) → K = IntermediateField.adjoin ℚ_[l] (Set.range c) := by
  first | exact @GlobalTheory.padicAlgCl_finite_dense_eq_adjoin | exact GlobalTheory.padicAlgCl_finite_dense_eq_adjoin | (intros; apply GlobalTheory.padicAlgCl_finite_dense_eq_adjoin <;> assumption)
