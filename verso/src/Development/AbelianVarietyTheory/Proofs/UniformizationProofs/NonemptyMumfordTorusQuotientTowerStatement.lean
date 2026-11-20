import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyMumfordTorusQuotientTower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.UU.TowerEx.nonempty_tower | exact GlobalTheory.UU.TowerEx.nonempty_tower | (intros; apply GlobalTheory.UU.TowerEx.nonempty_tower <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.nonempty_mumfordTorusQuotientTower : (AllSet fun s => Nonempty (Tower s)) := by
  first | exact @GlobalTheory.UU.TowerEx.nonempty_tower | exact GlobalTheory.UU.TowerEx.nonempty_tower | (intros; apply GlobalTheory.UU.TowerEx.nonempty_tower <;> assumption)
