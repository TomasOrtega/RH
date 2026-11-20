import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusFiniteIdentityPoints
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CurveRootGeometry.FrobFin.isFinite_frob` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFrobeniusFiniteIdentityPoints.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.frobenius_finite_identity_points : ∀ (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [PerfectField k] [CharP k q] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], LocallyOfFiniteType (strHom k C) → IsFinite (frob C q (natCast_eq_zero C q k)) ∧ ∀ x : C, frob C q (natCast_eq_zero C q k) x = x := by
  first | exact @GlobalTheory.CurveRootGeometry.FrobFin.isFinite_frob | exact GlobalTheory.CurveRootGeometry.FrobFin.isFinite_frob | (intros; apply GlobalTheory.CurveRootGeometry.FrobFin.isFinite_frob <;> assumption)
