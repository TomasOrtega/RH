import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowTOLower
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EX.szRow_TO_lower` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FSzRowTOLower.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.sizes_PP_pow_mul_dim_pow_div_le_TOv : SzRow (fun C D L => ((C.T.CP * zBase L ^ C.T.eP) ^ 4 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ C.T.Cp / ((D.R.m : ℝ) * L.de2) ≤ ((TOv L.sc : ℕ) : ℝ)) ∧ (((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) * D.R.k / D.R.m ≤ ((TOv L.sc : ℕ) : ℝ))) := by
  first | exact @GlobalTheory.EX.szRow_TO_lower | exact GlobalTheory.EX.szRow_TO_lower | (intros; apply GlobalTheory.EX.szRow_TO_lower <;> assumption)
