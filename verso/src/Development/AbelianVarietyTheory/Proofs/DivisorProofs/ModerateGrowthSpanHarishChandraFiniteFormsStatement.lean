import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthSpanHarishChandraFiniteForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HCF.ModGrowth.modGrowth_span` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FModerateGrowthSpanHarishChandraFiniteForms.lean&line=162#L162)
-/
theorem _root_.GlobalTheory.T.moderateGrowth_span_harishChandraFiniteForms : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ), ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ Ω : Set (GA E a), IsCompact Ω → ∃ (C : ℝ) (N₀ : ℕ), 0 ≤ C ∧ ∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), ∀ k ∈ (maxCompact : Subgroup (GA E a)), ∀ y : GL (Fin a) (Cinf E), ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k * infGL E a y)‖ ≤ C * (∑ i, (r i + (r i)⁻¹)) ^ N₀ * height y ^ N₀ := by
  first | exact @GlobalTheory.HCF.ModGrowth.modGrowth_span | exact GlobalTheory.HCF.ModGrowth.modGrowth_span | (intros; apply GlobalTheory.HCF.ModGrowth.modGrowth_span <;> assumption)
