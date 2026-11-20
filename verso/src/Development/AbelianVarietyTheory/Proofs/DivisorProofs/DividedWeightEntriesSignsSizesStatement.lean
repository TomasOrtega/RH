import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightEntriesSignsSizes
import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDividedWeightEntriesSignsSizes.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.dividedWeight_entries_signs_sizes : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ i, ((W.T : ℤ) + W.Dd + 1) * |W.u1 τ i| ≤ |W.u τ i| + W.c0 + 4 * N ∧ (W.kc ≤ (i : ℕ) + 1 → W.u1 τ i ≤ 0) ∧ ((i : ℕ) < W.kc → 0 ≤ W.u1 τ i) := by
  first | exact @GlobalTheory.MeanTop.divided_entries | exact GlobalTheory.MeanTop.divided_entries | (intros; apply GlobalTheory.MeanTop.divided_entries <;> assumption)
