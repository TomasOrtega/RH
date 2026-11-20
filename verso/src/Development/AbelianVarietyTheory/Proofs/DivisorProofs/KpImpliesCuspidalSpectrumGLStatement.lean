import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KpImpliesCuspidalSpectrumGL
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThK.cuspidalSpectrumGL_of_KP` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKpImpliesCuspidalSpectrumGL.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.kp_implies_cuspidal_spectrum_GL : GlobalTheory.ThK.KP → GlobalTheory.Published.CuspidalSpectrumGL := by
  first | exact @GlobalTheory.ThK.cuspidalSpectrumGL_of_KP | exact GlobalTheory.ThK.cuspidalSpectrumGL_of_KP | (intros; apply GlobalTheory.ThK.cuspidalSpectrumGL_of_KP <;> assumption)
