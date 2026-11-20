import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSemidirectProductFormula
import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ModChar.modularCharacterFun_semidirect` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHaarMeasureSemidirectProductFormula.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.haar_measure_semidirect_product_formula : ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [T2Space Q] [SecondCountableTopology Q] [MeasurableSpace Q] [BorelSpace Q] (N M : Subgroup Q) [N.Normal] [LocallyCompactSpace N] [LocallyCompactSpace M], IsClosed (N : Set Q) → IsClosed (M : Set Q) → (∀ q, ∃ n ∈ N, ∃ m ∈ M, q = n * m) → (∀ x, x ∈ N → x ∈ M → x = 1) → ∀ (νN : Measure N) (νM : Measure M), νN.IsHaarMeasure → νN.IsMulRightInvariant → νM.IsHaarMeasure → νM.IsMulRightInvariant → ∀ δ : Q →* ℝ≥0, (∀ n ∈ N, δ n = 1) → (∀ m ∈ M, νN.map (fun n : N => MulAut.conjNormal m n) = (δ m)⁻¹ • νN) → ∀ q : Q, Measure.modularCharacterFun q = δ q := by
  first | exact @GlobalTheory.CompanionTheory.ModChar.modularCharacterFun_semidirect | exact GlobalTheory.CompanionTheory.ModChar.modularCharacterFun_semidirect | (intros; apply GlobalTheory.CompanionTheory.ModChar.modularCharacterFun_semidirect <;> assumption)
