import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilPairingGaloisEquivariantCmTorsion
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FWeilPairingGaloisEquivariantCmTorsion.lean&line=215#L215)
-/
theorem _root_.GlobalTheory.T.weilPairing_galois_equivariant_cm_torsion : ∀ D : D7, WeilPairingGaloisAlt D := by
  first | exact @GlobalTheory.WeilPairingGalois.weilPairingGalois_all | exact GlobalTheory.WeilPairingGalois.weilPairingGalois_all | (intros; apply GlobalTheory.WeilPairingGalois.weilPairingGalois_all <;> assumption)
