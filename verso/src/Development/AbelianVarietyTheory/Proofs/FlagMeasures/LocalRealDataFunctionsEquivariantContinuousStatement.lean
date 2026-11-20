import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalRealDataFunctionsEquivariantContinuous
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLocalRealDataFunctionsEquivariantContinuous.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.localRealData_functions_equivariant_continuous : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → IsSPsiEquiv (locW C u u' τ).z (psiS D (locW C u u' τ).z) (locW C u u' τ).π (locS hB u u' τ).Φ ∧ IsSPsiEquiv (locW C u u' τ).z' (psiS D (locW C u u' τ).z') (locW C u u' τ).π' (locS hB u u' τ).Φ' ∧ ContinuousOn (locS hB u u' τ).Φ (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) ∧ ContinuousOn (locS hB u u' τ).Φ' (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) := by
  first | exact @GlobalTheory.SlocTie.locS_phi_equiv_cont | exact GlobalTheory.SlocTie.locS_phi_equiv_cont | (intros; apply GlobalTheory.SlocTie.locS_phi_equiv_cont <;> assumption)
