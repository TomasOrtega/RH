import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonIrreducibleQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CommonQuot.common_quotient` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCommonIrreducibleQuotient.lean&line=403#L403)
-/
theorem _root_.GlobalTheory.T.exists_common_irreducible_quotient : GlobalTheory.RealLift.MultOne → ∀ (R S : ℕ) (M M' : Formalism.BasicNotions.TH.GKMod R S) (Λ : Formalism.BasicNotions.TH.Ix R S → ℚ), GlobalTheory.RealLift.GenBy M Λ → GlobalTheory.RealLift.GenBy M' Λ → GlobalTheory.RealLift.Steep M Λ → GlobalTheory.RealLift.Steep M' Λ → ∃ (N : Formalism.BasicNotions.TH.GKMod R S) (π : M.V →ₗ[ℂ] N.V) (π' : M'.V →ₗ[ℂ] N.V), GlobalTheory.RealLift.IsQuot M N π ∧ GlobalTheory.RealLift.IsQuot M' N π' ∧ Formalism.MainNotions.SchurIrreducible.IrrGK N ∧ GlobalTheory.RealLift.ScalarEnd N := by
  first | exact @GlobalTheory.CommonQuot.common_quotient | exact GlobalTheory.CommonQuot.common_quotient | (intros; apply GlobalTheory.CommonQuot.common_quotient <;> assumption)
