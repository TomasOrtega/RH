import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.SquareIntegrableAtPlace.SqIntAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.AutomorphicL2Unitary PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.FD
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.SqIntFD

/- English proof (translation)
Introduce `E _ _ _ N mG bG μ _ 𝓕 h𝓕 φ h h'`. Take `rfl : mG = borel _` from `bG.measurable_eq`. Establish `hm` using `GlobalTheory.CuspRep.CuspidalL2GL.memL2_of_isAutForm (μ := μ) h h'`. Establish `hc` using `((memL2_iff_fundamental_domain h𝓕).1 hm).2`. Use `hc.2` as an intermediate fact.

Rewrite `this` using `[eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]`. Simplify using `using this`.
-/
theorem sqIntAt : PositivityTheory.Rg.BcB.SpectralAccumulation.FD.SqIntAt := by
  intro E _ _ _ N mG bG μ _ 𝓕 h𝓕 φ h h'
  obtain rfl : mG = borel _ := bG.measurable_eq
  have hm := GlobalTheory.CuspRep.CuspidalL2GL.memL2_of_isAutForm (μ := μ) h h'
  have hc := ((memL2_iff_fundamental_domain h𝓕).1 hm).2
  have := hc.2
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top] at this
  simpa using this

end GlobalTheory.CompanionTheory.SqIntFD
