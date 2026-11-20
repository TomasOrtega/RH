import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincarePotentialIsPotential
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PoincarePotOn.poincarePot_isPotentialOn` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPoincarePotentialIsPotential.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.poincare_potential_is_potential : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (K : LocPot X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X) (c : ℝ), IsPotential A K → IsBoundary A L s D → IsPotentialOn A (⋃ i, D i)ᶜ (poincarePot K L s c) := by
  first | exact @GlobalTheory.PoincarePotOn.poincarePot_isPotentialOn | exact GlobalTheory.PoincarePotOn.poincarePot_isPotentialOn | (intros; apply GlobalTheory.PoincarePotOn.poincarePot_isPotentialOn <;> assumption)
