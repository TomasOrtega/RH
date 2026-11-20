import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFullLatticeOverUnramifiedExtIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfValNonneg
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsFullLatticeOverUnramifiedExtIff.lean&line=123#L123)
-/
theorem _root_.GlobalTheory.T.isFullLatticeOver_unramifiedExt_iff : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (L : Submodule K'.O (overExt φ B ψ hψ hσ).A) (M : Submodule K.O B.A), (L : Set (overExt φ B ψ hψ hσ).A) = (M : Set B.A) → (IsLat K'.O K'.E L ↔ IsLat K.O K.E M) := by
  first | exact @GlobalTheory.UnitLemma.Unr.isLat_overExt_iff | exact GlobalTheory.UnitLemma.Unr.isLat_overExt_iff | (intros; apply GlobalTheory.UnitLemma.Unr.isLat_overExt_iff <;> assumption)
