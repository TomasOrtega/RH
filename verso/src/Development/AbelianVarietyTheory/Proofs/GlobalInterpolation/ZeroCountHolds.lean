import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinsumMemLeOfSubset

namespace GlobalTheory.Mem.An

/- English proof (translation)
Take `⟨C, -, H⟩` from `GlobalTheory.ZeroWindow.count_zeros_window`. Use `⟨C, fun q _ χ hχ t => ?_⟩` and prove the remaining obligations. Establish `h` using `(H q χ hχ t).2`. Simplify `h` using `only [zsumR, zerosIn, zmult, mul_one]`.
-/
theorem zeroCount_holds : GlobalTheory.Mem.An.ZeroCount := by
  obtain ⟨C, -, H⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  refine ⟨C, fun q _ χ hχ t => ?_⟩
  have h := (H q χ hχ t).2
  simpa only [zsumR, zerosIn, zmult, mul_one] using h

end GlobalTheory.Mem.An
