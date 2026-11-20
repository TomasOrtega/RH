import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCombinationGlNormalForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
open ValuativeRel
open scoped Matrix

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IntRowLattice.exists_gl_integral_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegralCombinationGlNormalForm.lean&line=88#L88)
-/
theorem _root_.GlobalTheory.T.integral_combination_gl_normal_form : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (X : Matrix (Fin n) (Fin d) k) (c : k), c ≠ 0 →
    ∃ h : GL (Fin d) k, ∀ Y : Matrix (Fin n) (Fin d) k,
      (∃ (A : Matrix (Fin n) (Fin n) k) (B : Matrix (Fin n) (Fin d) k), (∀ i j, A i j ∈ 𝒪[k]) ∧ (∀ i j, B i j ∈ 𝒪[k]) ∧ Y = A * X + c • B) ↔
        ∀ i j, (Y * (h : Matrix (Fin d) (Fin d) k)) i j ∈ 𝒪[k] := by
  first | exact @GlobalTheory.IntRowLattice.exists_gl_integral_iff | exact GlobalTheory.IntRowLattice.exists_gl_integral_iff | (intros; apply GlobalTheory.IntRowLattice.exists_gl_integral_iff <;> assumption)
