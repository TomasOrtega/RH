import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPullbackCancelLeft
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PPAS.hasTheta_pull_cancel` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThetaPullbackCancelLeft.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.theta_pullback_cancel_left : ∀ (S T T' : Scheme.{0}) (P : PPAS S) (P' : PPAS T) (f : T ⟶ S) (φ : P'.A.left ⟶ P.A.left) (g : T' ⟶ T), P'.IsPull P f φ → (∃ (Q : PPAS T') (ψ : Q.A.left ⟶ P.A.left), Q.IsPull P (g ≫ f) ψ ∧ Q.HasTheta) → ∃ (Q : PPAS T') (ψ : Q.A.left ⟶ P'.A.left), Q.IsPull P' g ψ ∧ Q.HasTheta := by
  first | exact @GlobalTheory.PPAS.hasTheta_pull_cancel | exact GlobalTheory.PPAS.hasTheta_pull_cancel | (intros; apply GlobalTheory.PPAS.hasTheta_pull_cancel <;> assumption)
