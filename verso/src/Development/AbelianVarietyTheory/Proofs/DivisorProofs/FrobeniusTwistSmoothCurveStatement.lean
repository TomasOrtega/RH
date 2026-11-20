import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusTwistSmoothCurve
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrobTwistCurve.exists_twist` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFrobeniusTwistSmoothCurve.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.frobenius_twist_smooth_curve : ∀ (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [PerfectField k] [CharP k q] (C : Scheme.{0}) [a : Algebra k Γ(C, ⊤)], IsSmoothProjCurve k C → ∃ a' : Algebra k Γ(C, ⊤), @IsSmoothProjCurve k _ C a' ∧ frob C q (natCast_eq_zero C q k) ≫ @strHom k _ C a = @strHom k _ C a' := by
  first | exact @GlobalTheory.FrobTwistCurve.exists_twist | exact GlobalTheory.FrobTwistCurve.exists_twist | (intros; apply GlobalTheory.FrobTwistCurve.exists_twist <;> assumption)
