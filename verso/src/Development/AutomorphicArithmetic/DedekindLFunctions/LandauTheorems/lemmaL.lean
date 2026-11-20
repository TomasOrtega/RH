import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.poleData
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.landauWindow
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.WindowHypUOfWindowHyp
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.CharFamilyLFunctionNeZeroOfOneLeRe

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

/- English proof (translation)
Introduce `i s hs hzero`. Take `⟨Φ, hP⟩` from `poleData F`. Establish `hZ` using `landau_window hP hθ hθ1 hδ (windowHypU_of_windowHyp F hδ h)`. Distinguish the cases in `h1 : 1 ≤ s.re`. Conclude with `charFamily_LFunction_ne_zero_of_one_le_re F i s h1 hzero`.

Establish `hmem : s ∈ zeroSet F` using `⟨by linarith, i, Or.inl hzero⟩`. Use `hZ s hmem` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lemmaL (F : CharFamily) {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (h : WindowHyp F θ δ) :
    ZeroFree F θ := by
  intro i s hs hzero
  obtain ⟨Φ, hP⟩ := poleData F
  have hZ := landau_window hP hθ hθ1 hδ (windowHypU_of_windowHyp F hδ h)
  by_cases h1 : 1 ≤ s.re
  · exact charFamily_LFunction_ne_zero_of_one_le_re F i s h1 hzero
  · have hmem : s ∈ zeroSet F := ⟨by linarith, i, Or.inl hzero⟩
    have := hZ s hmem
    linarith

end Deduction

end
