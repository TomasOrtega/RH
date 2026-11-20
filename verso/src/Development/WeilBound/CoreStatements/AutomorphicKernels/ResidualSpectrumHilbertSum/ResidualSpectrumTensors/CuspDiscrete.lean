import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Development
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec

namespace PositivityTheory.RSHS.L1

/- English proof (translation)
Introduce `π hu hn`. Use `⟨fun φ hφ => (π.cusp φ hφ).1, fun φ hφ => ?_, π.stable, π.ne_bot, π.irred⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL.of_isUnitary hu hφ`. Conclude with `GlobalTheory.DiscChar.isSqInt_of_bounded (hn φ hφ) hC`.
-/
theorem cuspDiscrete (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (hN : 1 ≤ N) :
    PositivityTheory.RSHS.CuspDiscrete E N := by
  intro π hu hn
  refine ⟨fun φ hφ => (π.cusp φ hφ).1, fun φ hφ => ?_, π.stable, π.ne_bot, π.irred⟩
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL.of_isUnitary hu hφ
  exact GlobalTheory.DiscChar.isSqInt_of_bounded (hn φ hφ) hC

end PositivityTheory.RSHS.L1

end
