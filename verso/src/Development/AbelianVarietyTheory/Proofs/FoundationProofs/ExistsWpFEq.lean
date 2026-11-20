import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_wpF_eq : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ r : ℂ, ∃ Q, Q ∉ Λ ∧ wpF Λ Q = r := by
  intro Λ h r
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  obtain ⟨z, hz, e⟩ := GlobalTheory.exists_weierstrassP_eq L r
  exact ⟨z, (hL z).not.2 hz, (GlobalTheory.OddTheta.wpF_eq L Λ hL z).trans e⟩

end GlobalTheory.EvenTheta
