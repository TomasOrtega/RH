import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGramMatricesCmUnitaryShimuraObject
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatCM.GramExists.exists_isGram` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsGramMatricesCmUnitaryShimuraObject.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.exists_gramMatrices_cmUnitaryShimuraObject : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q), ∃ gP gQ, IsGram X gP gQ := by
  first | exact @GlobalTheory.FlatCM.GramExists.exists_isGram | exact GlobalTheory.FlatCM.GramExists.exists_isGram | (intros; apply GlobalTheory.FlatCM.GramExists.exists_isGram <;> assumption)
