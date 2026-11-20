import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfCommutingFiniteAlgebraJointEi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteDimensionalOfCommutingFiniteAlgebraJointEi.lean&line=120#L120)
-/
theorem _root_.GlobalTheory.T.finiteDimensional_of_commuting_finiteAlgebra_jointEigen : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (S : Set (Module.End ℂ M)), (∀ s ∈ S, ∀ t ∈ S, s * t = t * s) → FiniteDimensional ℂ (Algebra.adjoin ℂ S) → (∀ c : Module.End ℂ M → ℂ, FiniteDimensional ℂ ↥(⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ M) (c s)))) → FiniteDimensional ℂ M := by
  first | exact @GlobalTheory.AutGrowth.finiteDimensional_of_commuting_finite_eigen | exact GlobalTheory.AutGrowth.finiteDimensional_of_commuting_finite_eigen | (intros; apply GlobalTheory.AutGrowth.finiteDimensional_of_commuting_finite_eigen <;> assumption)
