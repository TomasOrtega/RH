import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexConjugationOrbitOneRealPlace
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HTW.ConjWord.conj_word_one_place` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FComplexConjugationOrbitOneRealPlace.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.complexConjugation_orbit_one_realPlace : ∀ {fr : Formalism.HC.Frame} (τ : fr.GG), orderOf fr.cc = 2 ∧ ∀ i : ZMod (orderOf fr.cc), plc (letter τ fr.cc i) = plc τ := by
  first | exact @GlobalTheory.HTW.ConjWord.conj_word_one_place | exact GlobalTheory.HTW.ConjWord.conj_word_one_place | (intros; apply GlobalTheory.HTW.ConjWord.conj_word_one_place <;> assumption)
