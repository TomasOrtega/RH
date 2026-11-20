import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatSchwartzAddSmul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FJacobiToBesselFlatSchwartzAddSmul.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.jacobiToBesselFlatSchwartz_add_smul : ∀ (D : D7), FlatLaw D → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (f g : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V f → IsThetaFunO ψ J.W B.V g → flatFB st (f + g) = flatFB st f + flatFB st g ∧ ∀ a : ℂ, flatFB st (a • f) = a • flatFB st f := by
  first | exact @GlobalTheory.FlatAdd.flatFB_add_smul | exact GlobalTheory.FlatAdd.flatFB_add_smul | (intros; apply GlobalTheory.FlatAdd.flatFB_add_smul <;> assumption)
