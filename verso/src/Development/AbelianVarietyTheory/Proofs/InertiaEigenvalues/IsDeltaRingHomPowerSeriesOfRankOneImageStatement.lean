import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeltaRingHomPowerSeriesOfRankOneImage
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsDeltaRingHomPowerSeriesOfRankOneImage.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.isDeltaRingHom_powerSeries_of_rank_one_image : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Type) [CommRing C] (DC : Delta l C) (J : Ideal C), (l : C) ∈ J → IsHausdorff J C → ∀ (σ : (Wq l a)⟦X⟧ →+* C) (e : ℕ), σ X ^ e ∈ J → DC.δ (σ X) = 0 → IsδMap (deltaS l a) DC σ := by
  first | exact @GlobalTheory.sdelta_of_rank_one | exact GlobalTheory.sdelta_of_rank_one | (intros; apply GlobalTheory.sdelta_of_rank_one <;> assumption)
