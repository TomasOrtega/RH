import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureAdicCompletion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsDeltaRingStructureAdicCompletion.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.exists_deltaRingStructure_adicCompletion : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [CommRing L] (Q : Type) [CommRing Q] (i : L →+* Q) (J : Ideal L), IsCompl i J → (l : L) ∈ J → ∀ D : Delta l L, ∃ D' : Delta l Q, IsδMap D D' i := by
  first | exact @GlobalTheory.BSP.exists_delta_completion | exact GlobalTheory.BSP.exists_delta_completion | (intros; apply GlobalTheory.BSP.exists_delta_completion <;> assumption)
