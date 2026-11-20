import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaRingStructureDeltaFrobeniusComm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FDeltaRingStructureDeltaFrobeniusComm.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.deltaRingStructure_delta_frobenius_comm : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (a : A), D.δ (D.φ a) = D.φ (D.δ a) := by
  first | exact @GlobalTheory.BSP.Delta.δ_φ_comm | exact GlobalTheory.BSP.Delta.δ_φ_comm | (intros; apply GlobalTheory.BSP.Delta.δ_φ_comm <;> assumption)
