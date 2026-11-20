import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulEqSumVecMulVecSpanningFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Poinc.SumSq.exists_smul_eq_sum_vecMulVec_span` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSmulEqSumVecMulVecSpanningFamily.lean&line=143#L143)
-/
theorem _root_.GlobalTheory.T.exists_smul_eq_sum_vecMulVec_spanning_family : ∀ (r : ℕ) (L : Matrix (Fin r) (Fin r) ℤ), (L.map (Int.cast : ℤ → ℝ)).PosDef → ∃ (D m : ℕ) (a : Fin m → Fin r → ℤ), 1 ≤ D ∧ Submodule.span ℤ (Set.range a) = ⊤ ∧ (D : ℤ) • L = ∑ i, Matrix.vecMulVec (a i) (a i) := by
  first | exact @GlobalTheory.Poinc.SumSq.exists_smul_eq_sum_vecMulVec_span | exact GlobalTheory.Poinc.SumSq.exists_smul_eq_sum_vecMulVec_span | (intros; apply GlobalTheory.Poinc.SumSq.exists_smul_eq_sum_vecMulVec_span <;> assumption)
