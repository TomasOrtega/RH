import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HensIsLocalRingAndIsLocalHomOf
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHensIsLocalRingAndIsLocalHomOf.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.isLocalRing_hens_and_isLocalHom_of : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsLocalRing (Hens R) ∧ ∀ i : EtNbhd R, IsLocalHom (Hens.of i) := by
  first | exact @GlobalTheory.Henselisation.hens_isLocalRing_and_isLocalHom_of | exact GlobalTheory.Henselisation.hens_isLocalRing_and_isLocalHom_of | (intros; apply GlobalTheory.Henselisation.hens_isLocalRing_and_isLocalHom_of <;> assumption)
