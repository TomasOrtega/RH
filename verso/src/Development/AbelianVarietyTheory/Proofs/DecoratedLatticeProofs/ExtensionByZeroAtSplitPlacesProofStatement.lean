import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionByZeroAtSplitPlacesProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExtensionByZeroAtSplitPlacesProof.lean&line=209#L209)
-/
theorem _root_.GlobalTheory.T.extensionByZeroAtSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.ExtAll D := by
  first | exact @GlobalTheory.FinPl.ExtAllPf.ext_all | exact GlobalTheory.FinPl.ExtAllPf.ext_all | (intros; apply GlobalTheory.FinPl.ExtAllPf.ext_all <;> assumption)
