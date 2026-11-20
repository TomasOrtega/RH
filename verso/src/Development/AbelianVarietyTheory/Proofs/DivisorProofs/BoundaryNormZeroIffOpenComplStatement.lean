import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryNormZeroIffOpenCompl
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Proof.boundary_norm_zero_iff_open_compl.main` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBoundaryNormZeroIffOpenCompl.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.boundary_norm_zero_iff_open_compl : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X), IsBoundary A L s D → (∀ i y, normSec (L i) (s i) y = 0 ↔ y ∈ D i) ∧ IsOpen (⋃ i, D i)ᶜ := by
  first | exact @GlobalTheory.Proof.boundary_norm_zero_iff_open_compl.main | exact GlobalTheory.Proof.boundary_norm_zero_iff_open_compl.main | (intros; apply GlobalTheory.Proof.boundary_norm_zero_iff_open_compl.main <;> assumption)
