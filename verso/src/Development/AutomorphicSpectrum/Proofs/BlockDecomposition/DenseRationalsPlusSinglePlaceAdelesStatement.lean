import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseRationalsPlusSinglePlaceAdeles
open scoped Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.AddSA.dense_add_place` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDenseRationalsPlusSinglePlaceAdeles.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.dense_rationals_plus_single_place_adeles : ∀ (F : Type) [Field F] [NumberField F] (w : NumberField.InfinitePlace F), Dense ((Set.range (algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F))) + {a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F | a.2 = 0 ∧ ∀ w', w' ≠ w → a.1 w' = 0}) := by
  first | exact @GlobalTheory.CompanionTheory.AddSA.dense_add_place | exact GlobalTheory.CompanionTheory.AddSA.dense_add_place | (intros; apply GlobalTheory.CompanionTheory.AddSA.dense_add_place <;> assumption)
