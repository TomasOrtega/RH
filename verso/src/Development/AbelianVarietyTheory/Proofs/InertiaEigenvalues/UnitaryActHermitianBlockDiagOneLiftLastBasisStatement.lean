import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActHermitianBlockDiagOneLiftLastBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.Step.actU_uEmb_liftH` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnitaryActHermitianBlockDiagOneLiftLastBasis.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.unitaryActHermitianBlock_diagOne_liftLastBasis : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (s : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (ν : E) (l : F), actU (GlobalTheory.JR.Step.uEmb r E s) (GlobalTheory.JR.Step.liftH X ν l) = GlobalTheory.JR.Step.liftH (actU s X) ν l := by
  first | exact @GlobalTheory.JR.Step.actU_uEmb_liftH | exact GlobalTheory.JR.Step.actU_uEmb_liftH | (intros; apply GlobalTheory.JR.Step.actU_uEmb_liftH <;> assumption)
