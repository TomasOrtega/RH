import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicChainDatumCharacterLawsJointKernel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TwV.adLawAt_xiAd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FAdelicChainDatumCharacterLawsJointKernel.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.adelicChainDatum_characterLaws_jointKernel : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => AdLawAt A dtU a (xiAd A a) (muOf t u μ dtU)) := by
  first | exact @GlobalTheory.TwV.adLawAt_xiAd | exact GlobalTheory.TwV.adLawAt_xiAd | (intros; apply GlobalTheory.TwV.adLawAt_xiAd <;> assumption)
