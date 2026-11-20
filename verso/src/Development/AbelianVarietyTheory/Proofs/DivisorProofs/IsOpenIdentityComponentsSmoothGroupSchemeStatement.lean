import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIdentityComponentsSmoothGroupScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IdCompOpen.isOpen_identityComponent` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsOpenIdentityComponentsSmoothGroupScheme.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.isOpen_identityComponents_smooth_groupScheme : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → IsOpen {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  first | exact @GlobalTheory.IdCompOpen.isOpen_identityComponent | exact GlobalTheory.IdCompOpen.isOpen_identityComponent | (intros; apply GlobalTheory.IdCompOpen.isOpen_identityComponent <;> assumption)
