import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordConjHypATAllThick
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FTwistedDualOrbitPageWordConjHypATAllThick.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.twistedDualOrbitPageWord_conj_hypAT_allThick : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ : D.R.GG) (l : ℕ), Roomy L C → 11 ≤ l → Thick D.host τ → (pageWord L j ε τ (D.R.cc)).HypAT l ∧ ∀ i, (pageWord L j ε τ (D.R.cc)).thick i := by
  first | exact @GlobalTheory.HTW.conjWord_hypAT | exact GlobalTheory.HTW.conjWord_hypAT | (intros; apply GlobalTheory.HTW.conjWord_hypAT <;> assumption)
