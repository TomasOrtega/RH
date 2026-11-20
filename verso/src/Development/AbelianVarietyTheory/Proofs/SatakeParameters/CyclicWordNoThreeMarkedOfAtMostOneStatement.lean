import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordNoThreeMarkedOfAtMostOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.noThree_of_atMostOne` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FCyclicWordNoThreeMarkedOfAtMostOne.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.cyclicWord_noThreeMarked_of_atMostOne : ∀ {n : ℕ} (th : ZMod n → Prop), 2 ≤ n → (∀ a b, th a → th b → a = b) → NoThree th ∧ ∃ i, ¬ th i := by
  first | exact @GlobalTheory.noThree_of_atMostOne | exact GlobalTheory.noThree_of_atMostOne | (intros; apply GlobalTheory.noThree_of_atMostOne <;> assumption)
