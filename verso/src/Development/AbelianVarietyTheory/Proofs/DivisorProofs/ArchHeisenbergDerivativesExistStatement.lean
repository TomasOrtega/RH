import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HeisDer.derEx | exact GlobalTheory.HeisDer.derEx | (intros; apply GlobalTheory.HeisDer.derEx <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.archHeisenbergDerivatives_exist : GlobalTheory.RealLift.DerEx := by
  first | exact @GlobalTheory.HeisDer.derEx | exact GlobalTheory.HeisDer.derEx | (intros; apply GlobalTheory.HeisDer.derEx <;> assumption)
