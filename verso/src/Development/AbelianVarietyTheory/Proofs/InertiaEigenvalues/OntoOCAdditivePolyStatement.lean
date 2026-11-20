import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OntoOCAdditivePoly
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.onto_OC_additive_poly | exact GlobalTheory.onto_OC_additive_poly | (intros; apply GlobalTheory.onto_OC_additive_poly <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.exists_root_additive_poly_eq_of_unit_coeff : ∀ (l : ℕ) [Fact l.Prime] (E N : ℕ) (a : ℕ → ℂ_[l]), N ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖a N‖ = 1 → ∀ b : ℂ_[l], ‖b‖ ≤ 1 → ∃ W : ℂ_[l], ‖W‖ ≤ 1 ∧ ∑ k ∈ Finset.range (E + 1), a k * W ^ l ^ k = b := by
  first | exact @GlobalTheory.onto_OC_additive_poly | exact GlobalTheory.onto_OC_additive_poly | (intros; apply GlobalTheory.onto_OC_additive_poly <;> assumption)
