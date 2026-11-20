import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseMapCoordDerivativeNeZero
open scoped ContDiff Topology
open Filter
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FInverseMapCoordDerivativeNeZero.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.inverse_map_coord_derivative_ne_zero : ∀ {e : ℕ} (T S : (Fin e → ℂ) → (Fin e → ℂ)) (z0 : Fin e → ℂ) (j k : Fin e), DifferentiableAt ℂ T z0 → DifferentiableAt ℂ S (T z0) → S (T z0) = z0 → (∀ᶠ w in 𝓝 (T z0), T (S w) = w) → z0 k = 0 → (∀ᶠ z in 𝓝 z0, z k = 0 → T z j = 0) → fderiv ℂ (fun z => T z j) z0 (Pi.single k 1) ≠ 0 := by
  first | exact @GlobalTheory.localBiholom_partial_ne_zero_of_vanishing | exact GlobalTheory.localBiholom_partial_ne_zero_of_vanishing | (intros; apply GlobalTheory.localBiholom_partial_ne_zero_of_vanishing <;> assumption)
