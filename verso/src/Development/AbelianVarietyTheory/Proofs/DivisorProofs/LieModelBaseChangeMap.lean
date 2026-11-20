import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceDefiniteFormEqSumConjClassesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentSumEqZeroOfOrbitalIntegralEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiInvariantTestFunctionSum

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

/- English proof (translation)
Introduce `p _ G ha V _ _ _ ξ wt hξ L f hf hfb K' f' hf' hf'b hvan`. Rewrite using `[GlobalTheory.T.bi_invariant_test_function_sum p G ha wt L f hf hfb K' f' hf' hf'b]`. Unfold `dTrace`. Use `finsum_congr (fun q => ?_)` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.heckeTrace_definiteForm_eq_sum_conjClasses p G ha V ξ L f hf hfb K' f' hf' hf'b (Quot.out q)]`.

Use `finsum_congr (fun c => ?_)` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[hξ (Quot.out q) (Quotient.out c) h.1 h.2.1]`. Rewrite using `[GlobalTheory.T.centSum_eq_zero_of_orbitalIntegral_eq_zero p G ha L f hf hfb K' f' hf' hf'b (Quot.out q) (Quotient.out c) (hvan (Quot.out q) _ _ _ (Quotient.out c) h), mul_zero]`.
-/
theorem trace_definite_forms_identity : TraceDefinitePairsEqAutomorphicTrace := by
  intro p _ G ha V _ _ _ ξ wt hξ L f hf hfb K' f' hf' hf'b hvan
  rw [GlobalTheory.T.bi_invariant_test_function_sum p G ha wt L f hf hfb K' f' hf' hf'b]
  unfold dTrace
  refine finsum_congr (fun q => ?_)
  rw [GlobalTheory.T.heckeTrace_definiteForm_eq_sum_conjClasses p G ha V ξ L f hf hfb K' f' hf' hf'b (Quot.out q)]
  refine finsum_congr (fun c => ?_)
  split_ifs with h
  · rw [hξ (Quot.out q) (Quotient.out c) h.1 h.2.1]
  · rw [GlobalTheory.T.centSum_eq_zero_of_orbitalIntegral_eq_zero p G ha L f hf hfb K' f' hf' hf'b (Quot.out q) (Quotient.out c)
      (hvan (Quot.out q) _ _ _ (Quotient.out c) h), mul_zero]

end GlobalTheory.LKDef
