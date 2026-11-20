import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFormFactorThroughTraceGenerator
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LowFilt.exists_linear_theta_factor` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLinearFormFactorThroughTraceGenerator.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.exists_linearForm_factor_through_traceGenerator : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    (Z' : Submodule (𝓞 E) D.La) (θ : 𝓞 E →+ ℤ) (s : 𝓞 E) (hs : s ≠ 0)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u)) (w : D.La),
    ∃ ℓ : Z' →ₗ[𝓞 E] 𝓞 E, ∀ x : Z', θ (ℓ x) = D.EF x (H.bar s • w) := by
  first | exact @GlobalTheory.LowFilt.exists_linear_theta_factor | exact GlobalTheory.LowFilt.exists_linear_theta_factor | (intros; apply GlobalTheory.LowFilt.exists_linear_theta_factor <;> assumption)
