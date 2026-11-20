import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointedEtaleNeighbourhoodLocalRingIsDirected
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Henselisation.etNbhd_isDirected` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPointedEtaleNeighbourhoodLocalRingIsDirected.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsDirected (EtNbhd R) (· ≤ ·) := by
  first | exact @GlobalTheory.Henselisation.etNbhd_isDirected | exact GlobalTheory.Henselisation.etNbhd_isDirected | (intros; apply GlobalTheory.Henselisation.etNbhd_isDirected <;> assumption)
