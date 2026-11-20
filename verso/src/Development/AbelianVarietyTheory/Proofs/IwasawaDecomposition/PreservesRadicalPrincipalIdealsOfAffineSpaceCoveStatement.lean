import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreservesRadicalPrincipalIdealsOfAffineSpaceCove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FPreservesRadicalPrincipalIdealsOfAffineSpaceCove.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.preservesRadicalPrincipalIdeals_of_affineSpaceCovered : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r : ℕ), AffCover M M' φ f r → KeepsRad M M' φ f := by
  first | exact @GlobalTheory.FlagBundle.AffRad.keepsRad_of_affCover | exact GlobalTheory.FlagBundle.AffRad.keepsRad_of_affCover | (intros; apply GlobalTheory.FlagBundle.AffRad.keepsRad_of_affCover <;> assumption)
