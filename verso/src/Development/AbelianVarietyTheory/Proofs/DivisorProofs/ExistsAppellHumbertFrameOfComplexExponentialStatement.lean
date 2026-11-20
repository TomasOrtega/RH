import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfComplexExponential
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsAppellHumbertFrameOfComplexExponential.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_appellHumbertFrame_of_complexExponential : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (M : LB A.left), M.IsLB → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsExp (𝟙 (Sp ℂ)) e → ∃ (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), (∀ z, u.ex z = e z) ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  first | exact @GlobalTheory.ExpUnifAH.exists_unif_isFactorAH_of_isExp | exact GlobalTheory.ExpUnifAH.exists_unif_isFactorAH_of_isExp | (intros; apply GlobalTheory.ExpUnifAH.exists_unif_isFactorAH_of_isExp <;> assumption)
