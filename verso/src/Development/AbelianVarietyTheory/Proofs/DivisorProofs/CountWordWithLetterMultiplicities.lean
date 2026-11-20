import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

/- English proof (translation)
Unfold `word`. Rewrite using `[List.count_flatMap]`. Simplify using `[List.count_replicate, Function.comp_def]`.
-/
theorem count_word_eq (I : Type) [Fintype I] [DecidableEq I] (κ : I → ℕ) (i : I) :
    (word κ).count i = κ i := by
  unfold word
  rw [List.count_flatMap]
  simp [List.count_replicate, Function.comp_def]

end GlobalTheory.HilbFam
