import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatAlgebraicTensorChartRing
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomCompEq
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlatAlgebraicTensorChartRing.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.flat_algebraic_tensor_chart_ring : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (N : ℕ) (q : PrimeSpectrum R) (c : PreChart G N q), Module.Flat R (c.C ⊗[R] c.C) ∧ Algebra.IsAlgebraic R (c.C ⊗[R] c.C) := by
  first | exact @GlobalTheory.GroupBplus.Aff.PreChart.tensor_flat_isAlgebraic | exact GlobalTheory.GroupBplus.Aff.PreChart.tensor_flat_isAlgebraic | (intros; apply GlobalTheory.GroupBplus.Aff.PreChart.tensor_flat_isAlgebraic <;> assumption)
