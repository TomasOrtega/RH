import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStablePrismHomComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsStablePrismHomComp.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.isStablePrismHom_comp : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C D : Obj l R) (h : Hom B C) (h₂ : Hom C D), Stable h → Stable h₂ → Stable (h₂.comp h) := by
  first | exact @GlobalTheory.BSP.stable_comp | exact GlobalTheory.BSP.stable_comp | (intros; apply GlobalTheory.BSP.stable_comp <;> assumption)
