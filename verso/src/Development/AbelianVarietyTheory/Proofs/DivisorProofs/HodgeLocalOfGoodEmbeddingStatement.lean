import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLocalOfGoodEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CurvInterp.HodgeGood.hodgeLocal_good` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHodgeLocalOfGoodEmbedding.lean&line=96#L96)
-/
theorem _root_.GlobalTheory.T.hodge_local_of_good_embedding : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ → HodgeLocal x σ := by
  first | exact @GlobalTheory.CurvInterp.HodgeGood.hodgeLocal_good | exact GlobalTheory.CurvInterp.HodgeGood.hodgeLocal_good | (intros; apply GlobalTheory.CurvInterp.HodgeGood.hodgeLocal_good <;> assumption)
