import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicDatumRationalInvarianceOfKernelChain
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FFiniteAdelicDatumRationalInvarianceOfKernelChain.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.finiteAdelicDatum_rationalInvariance_of_kernelChain : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → (∀ i hi, PtAway A a i hi) → RatLaw A a) := by
  first | exact @GlobalTheory.RatPt.ratLaw_of_tie | exact GlobalTheory.RatPt.ratLaw_of_tie | (intros; apply GlobalTheory.RatPt.ratLaw_of_tie <;> assumption)
