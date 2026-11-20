import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProductMomentBoundDensityMassOne
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MomentHolder.product_moment_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FProductMomentBoundDensityMassOne.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.product_moment_bound_density_mass_one : ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r : ℕ) (len : Fin (r + 1) → Ω → ℝ) (Ph : Ω → ℝ) (A Rr : ℝ), (∀ a, AEMeasurable (len a) ν) → (∀ a, ∀ᵐ x ∂ν, 0 < len a x) → AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) → ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν = 1 → 0 ≤ A → 1 ≤ Rr → (∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal (len 0 x ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (A ^ q)) → (∀ a : Fin r, ∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal ((len a.succ x / len a.castSucc x) ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * q))) → ∫⁻ x, ENNReal.ofReal ((∏ a, len a x ^ 2) * Ph x) ∂ν ≤ ENNReal.ofReal ((A * Rr ^ (2 * r)) ^ (r + 1)) := by
  first | exact @GlobalTheory.MomentHolder.product_moment_le | exact GlobalTheory.MomentHolder.product_moment_le | (intros; apply GlobalTheory.MomentHolder.product_moment_le <;> assumption)
