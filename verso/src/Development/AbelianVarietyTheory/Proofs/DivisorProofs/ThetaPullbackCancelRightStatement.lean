import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPullbackCancelRight
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PPAS.exists_pull_hasTheta_comp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThetaPullbackCancelRight.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.theta_pullback_cancel_right : ∀ (S T T' : Scheme.{0}) (P : PPAS S) (P' : PPAS T) (f : T ⟶ S) (φ : P'.A.left ⟶ P.A.left) (g : T' ⟶ T), P'.IsPull P f φ → (∃ (Q : PPAS T') (ψ : Q.A.left ⟶ P'.A.left), Q.IsPull P' g ψ ∧ Q.HasTheta) → ∃ (Q : PPAS T') (ψ : Q.A.left ⟶ P.A.left), Q.IsPull P (g ≫ f) ψ ∧ Q.HasTheta := by
  first | exact @GlobalTheory.PPAS.exists_pull_hasTheta_comp | exact GlobalTheory.PPAS.exists_pull_hasTheta_comp | (intros; apply GlobalTheory.PPAS.exists_pull_hasTheta_comp <;> assumption)
