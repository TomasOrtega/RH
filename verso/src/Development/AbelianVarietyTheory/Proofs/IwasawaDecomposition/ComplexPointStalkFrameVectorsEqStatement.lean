import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointStalkFrameVectorsEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfConjEqOne
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LieBase.frameAt_v_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FComplexPointStalkFrameVectorsEq.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.complexPoint_stalkFrame_vectors_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (A₀ A : Mat Dw.mult X.Fn) (y : CxPts X.str (σ.comp e.toRingHom)) (x x' : Sp ℂ ⟶ Z.X) (g : EigFrame Z σ x) (g' : EigFrame Z σ x'), FrameAt e f₀ A₀ A y g → FrameAt e f₀ A₀ A y g' → ∀ τ i, g.v τ i = g'.v τ i := by
  first | exact @GlobalTheory.LieBase.frameAt_v_eq | exact GlobalTheory.LieBase.frameAt_v_eq | (intros; apply GlobalTheory.LieBase.frameAt_v_eq <;> assumption)
