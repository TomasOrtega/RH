import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyToroidalBoundaryDataOfSnc
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FNonemptyToroidalBoundaryDataOfSnc.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.nonempty_toroidal_boundary_data_of_snc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)], ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Z) → Nonempty (OddPrimesWithRootsOfUnity Z) := by
  first | exact @GlobalTheory.ShFam.nonempty_toroidal_boundary_data | exact GlobalTheory.ShFam.nonempty_toroidal_boundary_data | (intros; apply GlobalTheory.ShFam.nonempty_toroidal_boundary_data <;> assumption)
