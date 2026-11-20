import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemSurjectivityAndCountOrderZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemGeneralLemmaOrderOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemIntegralSurjectivityOfOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemIntegralSolutionCountOfOrderOneStatement
open GlobalTheory.PMonE

namespace GlobalTheory

/- English proof (translation)
Introduce `N`. Break down `Nat.eq_zero_or_pos N with rfl | hN` into its components or cases. Conclude with `GlobalTheory.T.additiveSystem_surjectivity_and_count_order_zero`. Conclude with `⟨GlobalTheory.T.additiveSystemIntegralSurjectivity_of_one N hN GlobalTheory.T.additiveSystem_generalLemma_orderOne.1, GlobalTheory.T.additiveSystemIntegralSolutionCount_of_order_one N hN GlobalTheory.T.additiveSystem_generalLemma_orderOne.2⟩`.
-/
theorem PMonE.generalLemma_allOrders : ∀ N : ℕ, GLOnto N ∧ GLCount N := by
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact GlobalTheory.T.additiveSystem_surjectivity_and_count_order_zero
  · exact ⟨GlobalTheory.T.additiveSystemIntegralSurjectivity_of_one N hN GlobalTheory.T.additiveSystem_generalLemma_orderOne.1, GlobalTheory.T.additiveSystemIntegralSolutionCount_of_order_one N hN GlobalTheory.T.additiveSystem_generalLemma_orderOne.2⟩

end GlobalTheory
