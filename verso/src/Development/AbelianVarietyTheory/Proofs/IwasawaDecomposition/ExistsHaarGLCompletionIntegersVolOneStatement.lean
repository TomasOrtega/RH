import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHaarGLCompletionIntegersVolOne
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Formalism.DoubleCosetMeasures.LatticeCoset
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsHaarGLCompletionIntegersVolOne.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_haar_GL_completion_integers_vol_one : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (r : ℕ), ∃ μ : Measure (GL (Fin r) (P.adicCompletion L)), μ.IsMulLeftInvariant ∧ μ ((GLint (OP P) r : Subgroup (GL (Fin r) (P.adicCompletion L))) : Set (GL (Fin r) (P.adicCompletion L))) = 1 := by
  first | exact @GlobalTheory.haar_glInt_one | exact GlobalTheory.haar_glInt_one | (intros; apply GlobalTheory.haar_glInt_one <;> assumption)
