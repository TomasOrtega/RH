import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubMemMaximalIdealPointedEtaleNeighbourhoo
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSubMemMaximalIdealPointedEtaleNeighbourhoo.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_sub_mem_maximalIdeal_pointedEtaleNeighbourhood : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) (b : i.B), ∃ r : R, b - algebraMap R i.B r ∈ maximalIdeal i.B := by
  first | exact @GlobalTheory.Henselisation.EtNbhd.exists_sub_mem_maximalIdeal | exact GlobalTheory.Henselisation.EtNbhd.exists_sub_mem_maximalIdeal | (intros; apply GlobalTheory.Henselisation.EtNbhd.exists_sub_mem_maximalIdeal <;> assumption)
