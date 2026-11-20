import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsNonemptyDenseVariety
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FComplexPointsNonemptyDenseVariety.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.complexPoints_nonempty_dense_variety : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ), Nonempty (CxPts Y.str σ) ∧ ∀ W : Y.X.Opens, (W : Set Y.X).Nonempty → Dense (CxPts.ptsIn Y.str σ W) := by
  first | exact @GlobalTheory.CxPtsDense.nonempty_and_dense | exact GlobalTheory.CxPtsDense.nonempty_and_dense | (intros; apply GlobalTheory.CxPtsDense.nonempty_and_dense <;> assumption)
