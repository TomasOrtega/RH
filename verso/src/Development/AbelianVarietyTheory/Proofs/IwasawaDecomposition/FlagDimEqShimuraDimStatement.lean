import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDimEqShimuraDim
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ShFam.SigDim.dim_add_sum_choose_eq_dimFl` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFlagDimEqShimuraDim.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.flag_dim_eq_shimura_dim : ∀ {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j), S.Dw.dim + ∑ τ, (S.Dw.mult τ).choose 2 = Formalism.DegreeFormula.dimFl D.what₂.Tau N := by
  first | exact @GlobalTheory.ShFam.SigDim.dim_add_sum_choose_eq_dimFl | exact GlobalTheory.ShFam.SigDim.dim_add_sum_choose_eq_dimFl | (intros; apply GlobalTheory.ShFam.SigDim.dim_add_sum_choose_eq_dimFl <;> assumption)
