import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelSplitPlaceCharacterEquivariance
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleUnif
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FLinearModelSplitPlaceCharacterEquivariance.lean&line=183#L183)
-/
theorem _root_.GlobalTheory.T.linearModel_splitPlace_characterEquivariance : ∀ D : D7, GlobalTheory.FinPl.LinExact D := by
  first | exact @GlobalTheory.LinExactAt.linExact | exact GlobalTheory.LinExactAt.linExact | (intros; apply GlobalTheory.LinExactAt.linExact <;> assumption)
