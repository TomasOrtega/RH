import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfIsProperOfIsHomId
import Mathlib
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_lift_of_isProper_of_isHom_id` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLiftOfIsProperOfIsHomId.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_lift_of_isProper_of_isHom_id' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y M : RatModel o Ω) (q : Y.Z ⟶ M.Z), M.IsHom Y (AlgHom.id o Ω) q → IsProper q → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), ∃ y' : Sp (OO p) ⟶ Y.Z, y' ≫ q = y := by
  first | exact @GlobalTheory.exists_lift_of_isProper_of_isHom_id | exact GlobalTheory.exists_lift_of_isProper_of_isHom_id | (intros; apply GlobalTheory.exists_lift_of_isProper_of_isHom_id <;> assumption)
