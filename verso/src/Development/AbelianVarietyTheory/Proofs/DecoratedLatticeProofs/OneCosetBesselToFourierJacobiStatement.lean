import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneCosetBesselToFourierJacobi
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FOneCosetBesselToFourierJacobi.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.oneCoset_besselToFourierJacobi : ∀ D : D7, GlobalTheory.FinPl.OneCosetBF D := by
  first | exact @GlobalTheory.FinPl.oneCosetBF | exact GlobalTheory.FinPl.oneCosetBF | (intros; apply GlobalTheory.FinPl.oneCosetBF <;> assumption)
