import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmExtensionConjMemInverseDifferentIdealPow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FCmExtensionConjMemInverseDifferentIdealPow.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.cmExtension_conj_mem_inverseDifferentIdealPow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j : ℕ) (x : E), x ∈ dInv E j → σ x ∈ dInv E j := by
  first | exact @GlobalTheory.SnMass.VolN.conj_mem_dInv | exact GlobalTheory.SnMass.VolN.conj_mem_dInv | (intros; apply GlobalTheory.SnMass.VolN.conj_mem_dInv <;> assumption)
