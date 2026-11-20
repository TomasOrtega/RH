import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingToHenselisationInjectiveOfNbhd
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEtaleNbhdLocalRingToHenselisationInjectiveOfNbhd.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.etaleNbhdLocalRingToHenselisation_injective_of_nbhd : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R), Function.Injective (Hens.of i) := by
  first | exact @GlobalTheory.Henselisation.Hens.of_injective_of_nbhd | exact GlobalTheory.Henselisation.Hens.of_injective_of_nbhd | (intros; apply GlobalTheory.Henselisation.Hens.of_injective_of_nbhd <;> assumption)
