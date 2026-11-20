import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionUniformizerNilpotent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FReductionUniformizerNilpotent.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.reduction_uniformizer_nilpotent : ∀ (p : ℕ) (W k Λ : Type) [CommRing W] [IsDomain W] [Field k] [CommRing Λ] (h e : ℕ) (c : W →+* k) (ρ : Λ →+* Matrix (Fin h) (Fin h) W) (π : Λ) (u : Λˣ), (p : W) ≠ 0 → Function.Surjective c → (∀ w, c w = 0 → (p : W) ∣ w) → c p = 0 → 0 < e → (p : Λ) = π ^ e * u → ((ρ π).map c) ^ e = 0 ∧ ∀ x : Fin h → k, (ρ π).map c *ᵥ x = 0 → ∃ y, x = ((ρ π).map c) ^ (e - 1) *ᵥ y := by
  first | exact @GlobalTheory.reduction_ker_uniformiser_eq_range_pow | exact GlobalTheory.reduction_ker_uniformiser_eq_range_pow | (intros; apply GlobalTheory.reduction_ker_uniformiser_eq_range_pow <;> assumption)
