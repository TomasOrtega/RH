import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicInstanceExistsFundamentalDomain
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FAutomorphicInstanceExistsFundamentalDomain.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.automorphicInstance_exists_fundamental_domain : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf], ∃ fund, I.IsFundDom (I.muA μf) fund := by
  first | exact @GlobalTheory.FundExists.exists_isFundDom | exact GlobalTheory.FundExists.exists_isFundDom | (intros; apply GlobalTheory.FundExists.exists_isFundDom <;> assumption)
