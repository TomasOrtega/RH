import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataMatrixActionRingHomProperties
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMumfordTensorDataMatrixActionRingHomProperties.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.mumfordTensorData_matrixAction_ringHom_properties : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W), (∀ a, IsMonHom (T.act a)) ∧ T.act 1 = 𝟙 _ ∧ (∀ a b, T.act (a * b) = T.act b ≫ T.act a) ∧ ∀ a b, T.act (a + b) = padd D'.P.A (T.act a) (T.act b) := by
  first | exact @GlobalTheory.Mum.TensAct.act_ring | exact GlobalTheory.Mum.TensAct.act_ring | (intros; apply GlobalTheory.Mum.TensAct.act_ring <;> assumption)
