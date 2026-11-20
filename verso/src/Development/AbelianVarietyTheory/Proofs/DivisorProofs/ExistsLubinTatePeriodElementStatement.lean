import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLubinTatePeriodElement
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LTPeriodShape.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLubinTatePeriodElement.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.exists_lubin_tate_period_element : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l),
    LTData K χ π z → ∃ (ω : AK K) (t u : BK K), thetaK K ω = 0 ∧ ω ∉ RingHom.ker (thetaK K) ^ 2 ∧
      t = toB K (ofA K ω) * (1 + toB K (ofA K ω) * u) ∧ ∀ g : ↥(GK K), galB g t = inK K (χ g : ↥K.1) * t := by
  first | exact @GlobalTheory.LTPeriodShape.main | exact GlobalTheory.LTPeriodShape.main | (intros; apply GlobalTheory.LTPeriodShape.main <;> assumption)
