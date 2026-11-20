import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHens
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlatHens.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.flat_hens' : ∀ (R : Type) [CommRing R] [IsLocalRing R], Module.Flat R (Hens R) := by
  first | exact @GlobalTheory.Henselisation.flat_hens | exact GlobalTheory.Henselisation.flat_hens | (intros; apply GlobalTheory.Henselisation.flat_hens <;> assumption)
