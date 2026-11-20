import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemSubmoduleOfComplexPolyValuesMem
import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.coeff_mem_of_poly_values_mem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCoeffMemSubmoduleOfComplexPolyValuesMem.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.coeff_mem_submodule_of_complex_poly_values_mem : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) (N : ℕ) (c : ℕ → V), (∀ u : ℂ, ∑ k ∈ Finset.range N, u ^ k • c k ∈ S) → ∀ k < N, c k ∈ S := by
  first | exact @GlobalTheory.coeff_mem_of_poly_values_mem | exact GlobalTheory.coeff_mem_of_poly_values_mem | (intros; apply GlobalTheory.coeff_mem_of_poly_values_mem <;> assumption)
