import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyFlagRefinementBundleOfGoodModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsVarietyFlagRefinementBundleOfGoodModel.lean&line=179#L179)
-/
theorem _root_.GlobalTheory.T.exists_variety_flagRefinementBundle_of_goodModel : ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) (ι : Type) (m k : ι → ℕ) (S : Fr M m k), Good M d → ∃ (Y : GlobalTheory.ProjVar.Var F) (φ : Ω →ₐ[F] Y.Fn) (f : Y.X ⟶ M.Z) (S' : Fr (ratOf Y) m k), Y.dim = d ∧ Refines S S' φ f := by
  first | exact @GlobalTheory.FlagBundle.exists_var_refines | exact GlobalTheory.FlagBundle.exists_var_refines | (intros; apply GlobalTheory.FlagBundle.exists_var_refines <;> assumption)
