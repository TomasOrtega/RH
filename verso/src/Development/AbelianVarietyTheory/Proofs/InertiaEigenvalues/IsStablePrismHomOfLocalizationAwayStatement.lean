import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStablePrismHomOfLocalizationAway
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BSP.stable_of_isLoc` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsStablePrismHomOfLocalizationAway.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.isStablePrismHom_of_localizationAway : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (s : B.A) (h : Hom B C), (∃ t ∈ B.I, ∀ x ∈ B.I, ∃ k : ℕ, s ^ k * x ∈ Ideal.span {t}) → IsLoc s h → Stable h := by
  first | exact @GlobalTheory.BSP.stable_of_isLoc | exact GlobalTheory.BSP.stable_of_isLoc | (intros; apply GlobalTheory.BSP.stable_of_isLoc <;> assumption)
