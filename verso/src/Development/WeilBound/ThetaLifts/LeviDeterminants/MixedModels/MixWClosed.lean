import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.MixWOfAdel
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.AdelicEstimatesHolds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PositivityTheory.Mix.mixW_closed : PositivityTheory.ThKG.MixW := PositivityTheory.ThKF0.mixW_of_adel PositivityTheory.Mix.adelic_estimates_holds
