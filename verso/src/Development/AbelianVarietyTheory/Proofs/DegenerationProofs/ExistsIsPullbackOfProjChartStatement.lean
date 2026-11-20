import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullbackOfProjChart
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ZH.RatModel.exists_isPullback_of_projChart` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FExistsIsPullbackOfProjChart.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.exists_isPullback_of_projChart' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') [IsNoetherianRing o] (N P : RatModel o Ω') (U₀ : M.Z.Opens) (b : N.Z ⟶ U₀.toScheme) (f : P.Z ⟶ M.Z) (J : Type) [Finite J] (t : J → Ω'), M.IsHom N φ (b ≫ U₀.ι) → M.IsHom P φ f → (∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty → M.ProjChart N φ (b ≫ U₀.ι) W t ∧ M.ProjChart P φ f W t) → ∃ a₀ : N.Z ⟶ P.Z, P.IsHom N (AlgHom.id o Ω') a₀ ∧ IsPullback a₀ b f U₀.ι := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isPullback_of_projChart | exact GlobalTheory.ZH.RatModel.exists_isPullback_of_projChart | (intros; apply GlobalTheory.ZH.RatModel.exists_isPullback_of_projChart <;> assumption)
