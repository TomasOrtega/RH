import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusCompatibleThetaZero
import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AinfK.Sep.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFrobeniusCompatibleThetaZero.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.frobenius_compatible_theta_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (w : ℕ → AK K), (∀ n, frobq K (w (n + 1)) = w n) →
    (∀ n, thetaK K (w n) = 0) → w 0 = 0 := by
  first | exact @GlobalTheory.AinfK.Sep.main | exact GlobalTheory.AinfK.Sep.main | (intros; apply GlobalTheory.AinfK.Sep.main <;> assumption)
