import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemGeneralLemmaAllOrders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.PMonE.generalLemma_allOrders | exact GlobalTheory.PMonE.generalLemma_allOrders | (intros; apply GlobalTheory.PMonE.generalLemma_allOrders <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.additiveSystem_generalLemma_all_orders : ∀ N : ℕ, GLOnto N ∧ GLCount N := by
  first | exact @GlobalTheory.PMonE.generalLemma_allOrders | exact GlobalTheory.PMonE.generalLemma_allOrders | (intros; apply GlobalTheory.PMonE.generalLemma_allOrders <;> assumption)
