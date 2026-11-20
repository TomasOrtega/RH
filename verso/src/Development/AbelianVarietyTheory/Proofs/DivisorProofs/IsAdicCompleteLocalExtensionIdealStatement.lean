import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteLocalExtensionIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdelicU GlobalTheory.TamOne
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TamOne.IntLocComplete.isAdicComplete` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsAdicCompleteLocalExtensionIdeal.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.isAdicComplete_local_extension_ideal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), IsAdicComplete ((extIdeal v).map (intLocIncl (E := E) v)) (intLoc (maximalRealSubfield E) E v) := by
  first | exact @GlobalTheory.TamOne.IntLocComplete.isAdicComplete | exact GlobalTheory.TamOne.IntLocComplete.isAdicComplete | (intros; apply GlobalTheory.TamOne.IntLocComplete.isAdicComplete <;> assumption)
