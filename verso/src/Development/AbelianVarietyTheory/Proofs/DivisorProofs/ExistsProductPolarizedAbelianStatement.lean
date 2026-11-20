import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductPolarizedAbelian
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProd
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField
open Limits MonoidalCategory CartesianMonoidalCategory GlobalTheory.VB
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsProductPolarizedAbelian.lean&line=136#L136)
-/
theorem _root_.GlobalTheory.T.exists_product_polarized_abelian : ∀ (S : Scheme.{0}) (P₁ P₂ : PPAS S), ∃ P : PPAS S, P.IsProd P₁ P₂ := by
  first | exact @GlobalTheory.PPAS.exists_isProd | exact GlobalTheory.PPAS.exists_isProd | (intros; apply GlobalTheory.PPAS.exists_isProd <;> assumption)
