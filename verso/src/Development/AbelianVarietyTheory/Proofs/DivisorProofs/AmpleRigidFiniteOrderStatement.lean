import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidFiniteOrder
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrderSt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AmpleFiniteOrder.finiteOrder_of_const_of_cube` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAmpleRigidFiniteOrder.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.ample_rigid_finite_order : GlobalTheory.AmpleRigid.ConstSt → GlobalTheory.AmpleRigid.CubeSt → GlobalTheory.AmpleRigid.FiniteOrderSt := by
  first | exact @GlobalTheory.AmpleFiniteOrder.finiteOrder_of_const_of_cube | exact GlobalTheory.AmpleFiniteOrder.finiteOrder_of_const_of_cube | (intros; apply GlobalTheory.AmpleFiniteOrder.finiteOrder_of_const_of_cube <;> assumption)
