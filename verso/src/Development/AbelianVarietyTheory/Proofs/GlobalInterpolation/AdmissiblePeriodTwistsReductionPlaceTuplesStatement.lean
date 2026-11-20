import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodTwistsReductionPlaceTuples
import Formalism.SharpRestriction.Divisibility.StatementFT.PeriodPointConditions
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FAdmissiblePeriodTwistsReductionPlaceTuples.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.admissiblePeriodTwists_reduction_placeTuples : ∀ (D : D7) (Dx : DivX D) (T : TwForms D), (∀ u μ, μ ≠ D.what₂.mu0 → (∃ w, μ = D.what₂.muAt w) → Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Dx T u μ) → Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible D Dx T := by
  first | exact @GlobalTheory.PerRedU.main | exact GlobalTheory.PerRedU.main | (intros; apply GlobalTheory.PerRedU.main <;> assumption)
