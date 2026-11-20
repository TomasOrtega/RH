import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlMapStandardLatticeEqIffMemGLintAdic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RpowNegLeNormOfComponent
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FGlMapStandardLatticeEqIffMemGLintAdic.lean&line=113#L113)
-/
theorem _root_.GlobalTheory.T.glMap_standardLattice_eq_iff_mem_GLint_adic : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (g : GL (Fin n) (w.adicCompletion E)), glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 = (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ↔ g ∈ GLint (Fin n) (Ov E w) := by
  first | exact @GlobalTheory.LatHecke.glMap_std_eq_iff_mem_GLint | exact GlobalTheory.LatHecke.glMap_std_eq_iff_mem_GLint | (intros; apply GlobalTheory.LatHecke.glMap_std_eq_iff_mem_GLint <;> assumption)
