import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.UniformRestrictionOfFiniteEnergy
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.RealObjInInfinityXJsz
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.MultiplicityOneUnitaryBranchingOfGapHyp
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.DoubleCosetBesselBoundOfGapConstantLe
import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.StepThmBPinnedCOfN
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.ThmBFinal

open Formalism.L2.SG Formalism.L2.SG.RealObj Formalism.L2.SG.Pf

namespace Formalism.MainStatements.RowRest

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem energyFin : EnergyFin := by
  intro D hG X u u' h
  have h1 := (EnergyConvJ.BM.realObj_inInfinityX_jsz CompanionTheory.Lime.BM.uniqGap_holds hG X u u' 1 one_pos).2.2
  rw [realObj_inNuX X u u' 1, h, ENNReal.mul_top (ENNReal.ofReal_pos.2 (MassDataPos.cooOf_pos X u u')).ne'] at h1
  exact ENNReal.ofReal_ne_top (top_le_iff.1 h1)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uniform_restriction_bound : ThmBChain6.AmplitudeBoundsAllChoicesUniform := uniform_restriction_of_finite_energy energyFin

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem analytic_pinnedTheoremB_uniform : NGAnalytic.StepThmBPinnedC :=
  stepThmBPinnedC_ofN (ThmBChain.theoremB_uniform_rotated CompanionTheory.WaveGrid.weighted_bound_rotated_uniform) CompanionTheory.Lime.BM.ampUnif_holds
    PointUniformity.ptUnif' (rowDataUnifN_of_6 Formalism.MainNotions.BridgeCS3dBOW.besselOfW_holds uniform_restriction_bound)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bDat_theoremB_global : BDat.StepThmBG :=
  stepThmBG_ofN (ThmBChain.theoremB_uniform_rotated CompanionTheory.WaveGrid.weighted_bound_rotated_uniform) CompanionTheory.Lime.BM.ampUnif_holds
    PointUniformity.ptUnifG (rowDataUnifN_of_6 Formalism.MainNotions.BridgeCS3dBOW.besselOfW_holds uniform_restriction_bound)

end Formalism.MainStatements.RowRest
