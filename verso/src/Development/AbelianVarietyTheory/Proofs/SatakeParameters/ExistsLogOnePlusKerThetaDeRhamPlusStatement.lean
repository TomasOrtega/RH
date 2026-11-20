import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLogOnePlusKerThetaDeRhamPlus
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsLogOnePlusKerThetaDeRhamPlus.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.exists_logOnePlus_kerTheta_deRhamPlus : ∀ (l : ℕ) [Fact l.Prime] (w : Per.AinfP l), w ∈ Per.kerP l → ∃ u : Per.BdRp l, IsLogP w u := by
  first | exact @GlobalTheory.Pst.LogExist.exists_isLogP | exact GlobalTheory.Pst.LogExist.exists_isLogP | (intros; apply GlobalTheory.Pst.LogExist.exists_isLogP <;> assumption)
