import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SgnIdent.sgnLaw_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FSignedUnitaryGroupCompat.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.signedUnitaryGroup_compat : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (V : HSp D), SgnLaw θ ε V := by
  first | exact @GlobalTheory.SgnIdent.sgnLaw_holds | exact GlobalTheory.SgnIdent.sgnLaw_holds | (intros; apply GlobalTheory.SgnIdent.sgnLaw_holds <;> assumption)
