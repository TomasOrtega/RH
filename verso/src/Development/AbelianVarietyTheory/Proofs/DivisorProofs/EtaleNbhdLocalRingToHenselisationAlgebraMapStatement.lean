import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingToHenselisationAlgebraMap
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEtaleNbhdLocalRingToHenselisationAlgebraMap.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) (r : R), Hens.of i (algebraMap R i.B r) = algebraMap R (Hens R) r := by
  first | exact @GlobalTheory.Henselisation.Hens.of_algebraMap | exact GlobalTheory.Henselisation.Hens.of_algebraMap | (intros; apply GlobalTheory.Henselisation.Hens.of_algebraMap <;> assumption)
