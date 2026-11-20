import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinConv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocLaArtinLit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
/- English proof (translation)
Introduce `N F Ω _ _ _ _ _ A w h`. Take `⟨rc, hrc⟩` from `_root_.UpperTheory.V.Z.Win.exRec'_alt N h`. Take `⟨a, ha, ε, -⟩` from `_root_.UpperTheory.V.Z.Win.toV' hrc`. Conclude with `⟨a, ha⟩`.
-/
theorem UpperTheory.V.Z.Win.T2.laArtinLit' :
    _root_.UpperTheory.V.Loc.localArtinReciprocity_type := by
  intro N F Ω _ _ _ _ _ A w h
  obtain ⟨rc, hrc⟩ := _root_.UpperTheory.V.Z.Win.exRec'_alt N h
  obtain ⟨a, ha, ε, -⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  exact ⟨a, ha⟩
end
