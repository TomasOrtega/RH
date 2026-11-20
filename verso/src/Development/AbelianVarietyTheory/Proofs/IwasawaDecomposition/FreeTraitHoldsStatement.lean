import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FreeTraitHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
open GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFreeTraitHolds.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.free_trait_holds : FreeTraitSt := by
  first | exact @GlobalTheory.TorRef.freeTrait | exact GlobalTheory.TorRef.freeTrait | (intros; apply GlobalTheory.TorRef.freeTrait <;> assumption)
