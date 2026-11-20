import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTowerAndHeightEqTwoDim
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FrobFieldExists
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsTorsionTowerAndHeightEqTwoDim.lean&line=79#L79)
-/
theorem _root_.GlobalTheory.T.exists_torsionTower_and_height_eq_two_dim : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A : AbVar k), (∃ G : PDivGroup p k, Nonempty (G.TorsionTower A.X)) ∧ ∀ (G : PDivGroup p k) (t : G.TorsionTower A.X), G.height = 2 * A.dim := by
  first | exact @GlobalTheory.AVTower.exists_tower_and_height_eq | exact GlobalTheory.AVTower.exists_tower_and_height_eq | (intros; apply GlobalTheory.AVTower.exists_tower_and_height_eq <;> assumption)
