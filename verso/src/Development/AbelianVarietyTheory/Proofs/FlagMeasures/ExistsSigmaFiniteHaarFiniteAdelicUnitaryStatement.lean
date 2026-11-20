import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSigmaFiniteHaarFiniteAdelicUnitary
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsSigmaFiniteHaarFiniteAdelicUnitary.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_sigmaFinite_haar_finiteAdelicUnitary : ∀ (I : AutInst), ∃ μf : Measure I.Gf, μf.IsHaarMeasure ∧ SigmaFinite μf := by
  first | exact @GlobalTheory.CongTop.exists_haar_sigmaFinite | exact GlobalTheory.CongTop.exists_haar_sigmaFinite | (intros; apply GlobalTheory.CongTop.exists_haar_sigmaFinite <;> assumption)
