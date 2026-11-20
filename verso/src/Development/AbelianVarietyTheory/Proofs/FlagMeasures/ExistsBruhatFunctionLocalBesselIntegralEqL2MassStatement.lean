import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBruhatFunctionLocalBesselIntegralEqL2Mass
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NinfGClosed
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SlocTie.loc_main` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsBruhatFunctionLocalBesselIntegralEqL2Mass.lean&line=106#L106)
-/
theorem _root_.GlobalTheory.T.exists_bruhatFunction_localBesselIntegral_eq_L2Mass : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau), ∃ β : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞, Measurable β ∧ (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))) = 1) ∧ ∫⁻ y, β y * ‖X.Wloc u (vOf X τ) y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) = l2SG (C.nuS u τ) (phiOf hB u τ) := by
  first | exact @GlobalTheory.SlocTie.loc_main | exact GlobalTheory.SlocTie.loc_main | (intros; apply GlobalTheory.SlocTie.loc_main <;> assumption)
