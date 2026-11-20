import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FixedByAutomorphismsMemField
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Flat.mem_of_fixed_aut` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FFixedByAutomorphismsMemField.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.fixed_by_automorphisms_mem_field : ∀ (F : IntermediateField ℚ ℂ) (c : ℂ), FiniteDimensional ℚ F → (∀ g : ℂ ≃+* ℂ, (∀ a ∈ F, g a = a) → g c = c) → c ∈ F := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.mem_of_fixed_aut | exact GlobalTheory.CompanionTheory.Ar.Flat.mem_of_fixed_aut | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.mem_of_fixed_aut <;> assumption)
