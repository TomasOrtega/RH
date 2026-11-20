import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveRealTensorToProdMatrixAlgebrasInfPlaces
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.bijective_realTensor_to_prod_matrixAlgebras_infPlaces : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Function.Bijective (fun x : ℝ ⊗[ℚ] G.C => fun v : InfinitePlace G.F => G.psiR v x) := by
  first | (exact @GlobalTheory.LKTrip.HTGroup.psiR_pi_bijective) | (exact GlobalTheory.LKTrip.HTGroup.psiR_pi_bijective) | (intros; apply GlobalTheory.LKTrip.HTGroup.psiR_pi_bijective  <;> assumption)
