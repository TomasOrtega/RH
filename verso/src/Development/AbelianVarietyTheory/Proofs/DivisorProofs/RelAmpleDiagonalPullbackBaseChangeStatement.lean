import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalPullbackBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DiagAmpleBC.relAmple_diag_pull` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRelAmpleDiagonalPullbackBaseChange.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.relAmple_diagonal_pullback_baseChange : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (t : T ⟶ S) (B : Over T) (β : B.left ⟶ A.left) (β₂ : (G2 B).left ⟶ (G2 A).left), IsPullback β B.hom A.hom t → IsSquare β β₂ → RelAmple B ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) := by
  first | exact @GlobalTheory.DiagAmpleBC.relAmple_diag_pull | exact GlobalTheory.DiagAmpleBC.relAmple_diag_pull | (intros; apply GlobalTheory.DiagAmpleBC.relAmple_diag_pull <;> assumption)
