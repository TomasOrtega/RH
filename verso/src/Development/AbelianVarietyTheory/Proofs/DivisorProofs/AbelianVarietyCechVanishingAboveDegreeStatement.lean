import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyCechVanishingAboveDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Tri
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AmpleGen.not_NV_of_ge` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAbelianVarietyCechVanishingAboveDegree.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.abelianVariety_cech_vanishing_above_degree : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ c : ℕ, ∀ P : LB A.left, P.IsLB → ∀ j : ℕ, c ≤ j → ¬ NV A P j := by
  first | exact @GlobalTheory.AmpleGen.not_NV_of_ge | exact GlobalTheory.AmpleGen.not_NV_of_ge | (intros; apply GlobalTheory.AmpleGen.not_NV_of_ge <;> assumption)
