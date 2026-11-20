import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomSpecOfLeRingOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FExistsHomSpecOfLeRingOn.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.exists_hom_spec_of_le_ringOn' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (R : Subalgebra o Ω), (U₀ : Set M.Z).Nonempty → R ≤ M.ringOn U₀ → ∃ u₀ : U₀.toScheme ⟶ Sp R, ∀ eta : Sp Ω ⟶ U₀.toScheme, eta ≫ U₀.ι = M.pt → eta ≫ u₀ = spMap R.val.toRingHom := by
  first | exact @GlobalTheory.ZH.RatModel.exists_hom_spec_of_le_ringOn | exact GlobalTheory.ZH.RatModel.exists_hom_spec_of_le_ringOn | (intros; apply GlobalTheory.ZH.RatModel.exists_hom_spec_of_le_ringOn <;> assumption)
