import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinConv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocLaArtinLit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem UpperTheory.V.Z.Win.T2.laArtinLit' :
    _root_.UpperTheory.V.Loc.localArtinReciprocity_type := by
  intro N F Ω _ _ _ _ _ A w h
  obtain ⟨rc, hrc⟩ := _root_.UpperTheory.V.Z.Win.exRec'_alt N h
  obtain ⟨a, ha, ε, -⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  exact ⟨a, ha⟩
end
