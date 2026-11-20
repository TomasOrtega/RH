import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageLinearTranslateConst
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSubgroupAverageLinearTranslateConst.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.subgroupAverage_linear_translate_const : ∀ (H : Type) [Group H] (u v : H → ℂ) (c : ℂ) (g : H), (rStab u).index ≠ 0 → (rStab v).index ≠ 0 → avg (u + v) = avg u + avg v ∧ avg (c • u) = c * avg u ∧ avg (fun x => u (g * x)) = avg u ∧ avg (fun _ : H => c) = c := by
  first | exact @GlobalTheory.AvgLin.avg_linear_translate_const | exact GlobalTheory.AvgLin.avg_linear_translate_const | (intros; apply GlobalTheory.AvgLin.avg_linear_translate_const <;> assumption)
