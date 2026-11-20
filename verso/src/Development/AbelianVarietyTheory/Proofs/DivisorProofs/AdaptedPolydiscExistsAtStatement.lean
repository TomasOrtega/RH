import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPolydiscExistsAt
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AdaptedCover.exists_adaptedPolydisc_centred` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdaptedPolydiscExistsAt.lean&line=139#L139)
-/
theorem _root_.GlobalTheory.T.adapted_polydisc_exists_at : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X), IsBoundary A L s D → ∀ x : X, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (σ : Fin m → Option (Fin e)), IsAdaptedPolydisc A D ψ σ ∧ x ∈ ψ.source ∧ ψ x = 0 := by
  first | exact @GlobalTheory.AdaptedCover.exists_adaptedPolydisc_centred | exact GlobalTheory.AdaptedCover.exists_adaptedPolydisc_centred | (intros; apply GlobalTheory.AdaptedCover.exists_adaptedPolydisc_centred <;> assumption)
