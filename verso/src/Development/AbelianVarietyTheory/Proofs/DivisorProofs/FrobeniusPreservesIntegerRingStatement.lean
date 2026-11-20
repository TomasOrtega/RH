import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPreservesIntegerRing
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFrobeniusPreservesIntegerRing.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.frobenius_preserves_integer_ring : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), ∀ x ∈ intR p K r, frobR p K r x ∈ intR p K r := by
  first | exact @GlobalTheory.LKLoc.frobR_mem_intR | exact GlobalTheory.LKLoc.frobR_mem_intR | (intros; apply GlobalTheory.LKLoc.frobR_mem_intR <;> assumption)
