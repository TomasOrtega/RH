import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleFrameAdjointMatrixHalfIdempotentSmul
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AdjScalar.adjA_half_smul` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIdeleFrameAdjointMatrixHalfIdempotentSmul.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.ideleFrameAdjointMatrix_half_idempotent_smul : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (e : AE D) (c : D.host.E) (x : WO S T), IsHalf (cA D e) x → adjA S T βS βT (e * incA D (star c)) x = adjA S T βS βT 1 (incA D c • x) := by
  first | exact @GlobalTheory.AdjScalar.adjA_half_smul | exact GlobalTheory.AdjScalar.adjA_half_smul | (intros; apply GlobalTheory.AdjScalar.adjA_half_smul <;> assumption)
