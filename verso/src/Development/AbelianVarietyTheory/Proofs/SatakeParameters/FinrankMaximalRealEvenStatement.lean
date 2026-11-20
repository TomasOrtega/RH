import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankMaximalRealEven
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RealGal.QCM.even_finrank_maximalRealSubfield` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FFinrankMaximalRealEven.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.finrank_maximal_real_even : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] (Q : GlobalTheory.RealGal.QCM E Ω), Even (Module.finrank ℚ (maximalRealSubfield Q.K)) := by
  first | exact @GlobalTheory.RealGal.QCM.even_finrank_maximalRealSubfield | exact GlobalTheory.RealGal.QCM.even_finrank_maximalRealSubfield | (intros; apply GlobalTheory.RealGal.QCM.even_finrank_maximalRealSubfield <;> assumption)
