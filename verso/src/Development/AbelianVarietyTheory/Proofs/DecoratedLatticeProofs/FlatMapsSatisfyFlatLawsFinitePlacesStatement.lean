import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinPl.flatLaws_all` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FFlatMapsSatisfyFlatLawsFinitePlaces.lean&line=139#L139)
-/
theorem _root_.GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces : ∀ D : D7, GlobalTheory.FinPl.FlatLaws D := by
  first | exact @GlobalTheory.FinPl.flatLaws_all | exact GlobalTheory.FinPl.flatLaws_all | (intros; apply GlobalTheory.FinPl.flatLaws_all <;> assumption)
