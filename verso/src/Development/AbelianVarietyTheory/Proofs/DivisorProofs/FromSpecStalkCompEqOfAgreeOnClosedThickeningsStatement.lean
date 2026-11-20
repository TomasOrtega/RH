import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecStalkCompEqOfAgreeOnClosedThickenings
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThickStalkEq.fromSpecStalk_comp_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFromSpecStalkCompEqOfAgreeOnClosedThickenings.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.fromSpecStalk_comp_eq_of_agree_on_closedThickenings : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Spec (CommRingCat.of R))), LocallyOfFiniteType G.hom → ∀ (b b' : G ⟶ G), (∀ e : ℕ, (Over.pullback (thick R (maximalIdeal R) e)).map b = (Over.pullback (thick R (maximalIdeal R) e)).map b') → ∀ x : G.left, G.hom x = closedPoint R → G.left.fromSpecStalk x ≫ b.left = G.left.fromSpecStalk x ≫ b'.left := by
  first | exact @GlobalTheory.ThickStalkEq.fromSpecStalk_comp_eq | exact GlobalTheory.ThickStalkEq.fromSpecStalk_comp_eq | (intros; apply GlobalTheory.ThickStalkEq.fromSpecStalk_comp_eq <;> assumption)
