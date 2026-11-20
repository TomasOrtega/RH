import Mathlib
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm

namespace GlobalTheory.LocalQuad

/- English proof (translation)
Introduce `H` and use `GlobalTheory.Published.landherrSt_of_landherr (landherr_of_hasseNormSt H)`.
-/
theorem landherrSt_of_hasseNormSt : GlobalTheory.Published.HasseNormSt → GlobalTheory.Published.LandherrSt :=
  fun H => GlobalTheory.Published.landherrSt_of_landherr (landherr_of_hasseNormSt H)

end GlobalTheory.LocalQuad
