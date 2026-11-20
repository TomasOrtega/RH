import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProjectiveBundleOfLatticeIsProjOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsProjectiveBundleOfLatticeIsProjOver.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.exists_projectiveBundleOfLattice_isProjOver : ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (J : Type) [Fintype J] [DecidableEq J] [Nonempty J] (EE : M.Lat J), IsProjOver M.s → ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra F Ω') (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (s : J → Ω'), ProjBundle M EE M' φ f s ∧ IsProjOver M'.s := by
  first | exact @GlobalTheory.FlagBundle.exists_projBundle | exact GlobalTheory.FlagBundle.exists_projBundle | (intros; apply GlobalTheory.FlagBundle.exists_projBundle <;> assumption)
