import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLocalRingPointedEtaleNeighbourhood
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.Henselisation.EtNbhd.flat_B | exact GlobalTheory.Henselisation.EtNbhd.flat_B | (intros; apply GlobalTheory.Henselisation.EtNbhd.flat_B <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.flat_localRing_pointedEtaleNeighbourhood : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R), Module.Flat R i.B := by
  first | exact @GlobalTheory.Henselisation.EtNbhd.flat_B | exact GlobalTheory.Henselisation.EtNbhd.flat_B | (intros; apply GlobalTheory.Henselisation.EtNbhd.flat_B <;> assumption)
