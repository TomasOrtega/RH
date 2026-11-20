import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemIdentityComponentOfRational
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMulMemIdentityComponentOfRational.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.mul_mem_identityComponent_of_rational' : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] (x y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G), x.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → y.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → (x * y).left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) := by
  first | exact @GlobalTheory.mul_mem_identityComponent_of_rational | exact GlobalTheory.mul_mem_identityComponent_of_rational | (intros; apply GlobalTheory.mul_mem_identityComponent_of_rational <;> assumption)
