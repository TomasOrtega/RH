import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineSpaceCoveredSmoothOfRelativeDimensionAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAffineSpaceCoveredSmoothOfRelativeDimensionAdd.lean&line=94#L94)
-/
theorem _root_.GlobalTheory.T.affineSpaceCovered_smoothOfRelativeDimension_add : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r d : ℕ), AffCover M M' φ f r → SmoothOfRelativeDimension d M.s → SmoothOfRelativeDimension (d + r) M'.s := by
  first | exact @GlobalTheory.FlagBundle.affCover_smooth | exact GlobalTheory.FlagBundle.affCover_smooth | (intros; apply GlobalTheory.FlagBundle.affCover_smooth <;> assumption)
