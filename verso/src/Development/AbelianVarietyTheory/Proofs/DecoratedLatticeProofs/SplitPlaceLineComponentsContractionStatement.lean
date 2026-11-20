import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineComponentsContraction
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSplitPlaceLineComponentsContraction.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.splitPlace_lineComponents_contraction : ∀ D : D7, GlobalTheory.FinPl.Contraction D := by
  first | exact @GlobalTheory.FinPl.contraction_all | exact GlobalTheory.FinPl.contraction_all | (intros; apply GlobalTheory.FinPl.contraction_all <;> assumption)
