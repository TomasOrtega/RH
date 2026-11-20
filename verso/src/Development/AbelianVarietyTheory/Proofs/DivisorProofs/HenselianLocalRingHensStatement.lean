import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianLocalRingHens
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Henselisation.henselianLocalRing_hens` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHenselianLocalRingHens.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.henselianLocalRing_hens' : ∀ (R : Type) [CommRing R] [IsLocalRing R], HenselianLocalRing (Hens R) := by
  first | exact @GlobalTheory.Henselisation.henselianLocalRing_hens | exact GlobalTheory.Henselisation.henselianLocalRing_hens | (intros; apply GlobalTheory.Henselisation.henselianLocalRing_hens <;> assumption)
