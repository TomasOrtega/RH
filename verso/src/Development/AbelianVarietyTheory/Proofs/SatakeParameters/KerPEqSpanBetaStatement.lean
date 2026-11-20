import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerPEqSpanBeta
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Pst.StLat.ker_localizedTheta_eq_span_beta` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FKerPEqSpanBeta.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.kerP_eq_span_beta_of_untilt_eq : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), ϖ.untilt = ((l : ℕ) : Per.OC l) → Per.kerP l = Ideal.span {beta ϖ} := by
  first | exact @GlobalTheory.Pst.StLat.ker_localizedTheta_eq_span_beta | exact GlobalTheory.Pst.StLat.ker_localizedTheta_eq_span_beta | (intros; apply GlobalTheory.Pst.StLat.ker_localizedTheta_eq_span_beta <;> assumption)
