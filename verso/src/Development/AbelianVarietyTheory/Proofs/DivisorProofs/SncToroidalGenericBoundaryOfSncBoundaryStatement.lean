import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncToroidalGenericBoundaryOfSncBoundary
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSncToroidalGenericBoundaryOfSncBoundary.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.snc_toroidalGenericBoundary_of_snc_boundary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ReciprocityTheory.AnForm.R.FinalTheorems.Snc (GlobalTheory.LogKS.boundary Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (GlobalTheory.Toroidal.genBdIdeal Y) := by
  first | exact @GlobalTheory.VarFlag.snc_genBdIdeal_of_snc_boundary | exact GlobalTheory.VarFlag.snc_genBdIdeal_of_snc_boundary | (intros; apply GlobalTheory.VarFlag.snc_genBdIdeal_of_snc_boundary <;> assumption)
