import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirCentralAndOnHighestWeight
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCasimirCentralAndOnHighestWeight.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.casimir_central_and_on_highestWeight : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → (∀ Z, casimir act * act Z = act Z * casimir act) ∧ ∀ (μ : Ix p q → ℚ) (v : V), v ∈ hwSub act μ → (∑ a, ∑ b, if sameBlock a b then act (Eab a b) (act (Eab b a) v) else 0) = ((∑ a, μ a ^ 2 + (∑ i : Fin p, μ (.inl i) * ((p : ℚ) - 1 - 2 * (i : ℕ))) + (∑ j : Fin q, μ (.inr j) * ((q : ℚ) - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • v := by
  first | exact @GlobalTheory.CasimirHighest.casimir_central_and_highest | exact GlobalTheory.CasimirHighest.casimir_central_and_highest | (intros; apply GlobalTheory.CasimirHighest.casimir_central_and_highest <;> assumption)
