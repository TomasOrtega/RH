import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeUnramifiedUniformizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LevelUnram.unram` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FLevelPrimeUnramifiedUniformizer.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.levelPrime_unramifiedUniformizer : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (v : (D.mem u).A.vT), Unram (A.res v) (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) := by
  first | exact @GlobalTheory.LevelUnram.unram | exact GlobalTheory.LevelUnram.unram | (intros; apply GlobalTheory.LevelUnram.unram <;> assumption)
