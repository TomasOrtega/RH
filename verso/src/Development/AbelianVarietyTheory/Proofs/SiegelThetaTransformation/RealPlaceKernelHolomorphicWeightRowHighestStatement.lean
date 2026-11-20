import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPlaceKernelHolomorphicWeightRowHighest
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KernHol.kern_hol_weight` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSiegelThetaTransformation%2FRealPlaceKernelHolomorphicWeightRowHighest.lean&line=559#L559)
-/
theorem _root_.GlobalTheory.T.realPlaceKernel_holomorphic_weight_rowHighest : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ) (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (m : ℕ) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), Even n → (∀ j, P j ∈ Harm.rowHighest ℂ c c') → ∀ x₂ ∈ X.dom, DifferentiableOn ℂ (fun x₁ => kern X hr idx P x₁ x₂) X.dom ∧ ∀ x₁ ∈ X.dom, ∀ b ∈ Bor X.Ψ r, kern X hr idx P (rmul x₁ b) x₂ = bchar (wtOf X hr c c' n) b * kern X hr idx P x₁ x₂ := by
  first | exact @GlobalTheory.KernHol.kern_hol_weight | exact GlobalTheory.KernHol.kern_hol_weight | (intros; apply GlobalTheory.KernHol.kern_hol_weight <;> assumption)
