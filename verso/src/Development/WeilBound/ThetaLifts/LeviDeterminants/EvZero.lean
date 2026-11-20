import Development.WeilBound.ThetaLifts.LeviDeterminants.EvCone
import Development.WeilBound.ThetaLifts.LeviDeterminants.ExistsAdaptedModelSkewPlane

/- English proof (translation)
The claim follows from `PositivityTheory.ThKF0.evZero_of_adapted PositivityTheory.ThKF0.exists_adapted_model_evaluation`.
-/
theorem PositivityTheory.ThKF0.evZero : GlobalTheory.ThK.EvZero := PositivityTheory.ThKF0.evZero_of_adapted PositivityTheory.ThKF0.exists_adapted_model_evaluation
