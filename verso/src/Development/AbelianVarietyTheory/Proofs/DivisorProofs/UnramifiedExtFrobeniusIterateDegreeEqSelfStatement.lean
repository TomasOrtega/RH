import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedExtFrobeniusIterateDegreeEqSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LKLoc.frobR_iterate_self` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnramifiedExtFrobeniusIterateDegreeEqSelf.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.unramifiedExtFrobenius_iterate_degree_eq_self : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (r : ℕ), 0 < r → ∀ x : Kn p K r, (⇑(frobR p K r))^[r] x = x := by
  first | exact @GlobalTheory.LKLoc.frobR_iterate_self | exact GlobalTheory.LKLoc.frobR_iterate_self | (intros; apply GlobalTheory.LKLoc.frobR_iterate_self <;> assumption)
