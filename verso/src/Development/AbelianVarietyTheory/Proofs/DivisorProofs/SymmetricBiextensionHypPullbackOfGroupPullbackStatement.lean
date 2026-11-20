import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricBiextensionHypPullbackOfGroupPullback
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSymmetricBiextensionHypPullbackOfGroupPullback.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.symmetricBiextensionHyp_pullback_of_groupPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left) (Q : LB (A ⊗ A).left), IsGrpPullback A' A f φ → IsSquare φ φ₂ → QHyp A Q → QHyp A' (Q.pull φ₂) := by
  first | exact @GlobalTheory.ActFin.qHyp_pull_of_isGrpPullback | exact GlobalTheory.ActFin.qHyp_pull_of_isGrpPullback | (intros; apply GlobalTheory.ActFin.qHyp_pull_of_isGrpPullback <;> assumption)
