import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCoverInjectiveAndDescent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BSP.cover_injective_and_descent` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FPrismCoverInjectiveAndDescent.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.prism_cover_injective_and_descent : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (h : Hom B C), Cover h → Function.Injective h.f ∧ ∀ (D : Obj l R) (p q : Hom C D), IsPO h h p q → ∀ c, p.f c = q.f c → c ∈ h.f.range := by
  first | exact @GlobalTheory.BSP.cover_injective_and_descent | exact GlobalTheory.BSP.cover_injective_and_descent | (intros; apply GlobalTheory.BSP.cover_injective_and_descent <;> assumption)
