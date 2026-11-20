import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.MixWOfAdel
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.AdelicEstimatesHolds

/- English proof (translation)
The claim follows from `PositivityTheory.ThKF0.mixW_of_adel PositivityTheory.Mix.adelic_estimates_holds`.
-/
theorem PositivityTheory.Mix.mixW_closed : PositivityTheory.ThKG.MixW := PositivityTheory.ThKF0.mixW_of_adel PositivityTheory.Mix.adelic_estimates_holds
