import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefLatticeIndepCoefMapProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCoefLatticeIndepCoefMapProof.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.coefLattice_indep_coefMap_proof : GlobalTheory.BaseCmp.CoefIndep := by
  first | exact @GlobalTheory.CoefIndepProof.coefIndep | exact GlobalTheory.CoefIndepProof.coefIndep | (intros; apply GlobalTheory.CoefIndepProof.coefIndep <;> assumption)
