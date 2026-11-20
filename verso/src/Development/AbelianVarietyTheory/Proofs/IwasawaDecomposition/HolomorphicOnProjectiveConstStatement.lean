import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicOnProjectiveConst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtFJQOver
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ConstFn.holoOn_univ_const` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FHolomorphicOnProjectiveConst.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.holomorphic_on_projective_const : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ) (R : AnRead Y.str σ Y.dim) (q : CxPts Y.str σ → ℂ), R.HoloOn Set.univ q → ∃ b : ℂ, ∀ z, q z = b := by
  first | exact @GlobalTheory.ConstFn.holoOn_univ_const | exact GlobalTheory.ConstFn.holoOn_univ_const | (intros; apply GlobalTheory.ConstFn.holoOn_univ_const <;> assumption)
