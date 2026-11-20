import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EmbeddingSignAlternateOfSignNeg
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FEmbeddingSignAlternateOfSignNeg.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.embeddingSign_alternate_of_sign_neg : ∀ {fr : Formalism.HC.Frame} (ε : ℤˣ) (τ φ : fr.GG), φ.1.2 = -1 → Alternates (fun i : ZMod (orderOf φ) => pos ε (letter τ φ i)) ∧ Alternates (fun i : ZMod (orderOf φ) => !pos ε (letter τ φ i)) := by
  first | exact @GlobalTheory.signs_alternate_inert | exact GlobalTheory.signs_alternate_inert | (intros; apply GlobalTheory.signs_alternate_inert <;> assumption)
