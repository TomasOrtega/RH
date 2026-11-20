import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaWeilRepFirstVariable
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BiTransfer.isBiTheta_act_left` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FIsJointlySmoothBiThetaWeilRepFirstVariable.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.isJointlySmoothBiTheta_weilRep_first_variable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χA χS : (AE D)ˣ →* Circle) (oma : Om A S), IsWeilDatumO ψ A S χA χS oma → ∀ C, IsBiTheta ψ A S A' C → ∀ p, IsBiTheta ψ A S A' fun u v => oma p (fun u' => C u' v) u := by
  first | exact @GlobalTheory.BiTransfer.isBiTheta_act_left | exact GlobalTheory.BiTransfer.isBiTheta_act_left | (intros; apply GlobalTheory.BiTransfer.isBiTheta_act_left <;> assumption)
