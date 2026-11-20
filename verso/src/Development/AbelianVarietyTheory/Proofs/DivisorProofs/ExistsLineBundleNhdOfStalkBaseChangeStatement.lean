import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleNhdOfStalkBaseChange
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.StalkLB.exists_lb_nhd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLineBundleNhdOfStalkBaseChange.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.exists_lineBundle_nhd_of_stalk_baseChange : ∀ {S X : Scheme.{0}} [IsLocallyNoetherian S] (h : X ⟶ S) [QuasiCompact h] [QuasiSeparated h] (x : S) (N : LB (pullback h (S.fromSpecStalk x))), N.IsLB → ∃ W : S.Opens, x ∈ W ∧ ∃ N' : LB ↑(h ⁻¹ᵁ W), N'.IsLB ∧ ∀ a : pullback h (S.fromSpecStalk x) ⟶ ↑(h ⁻¹ᵁ W), a ≫ (h ⁻¹ᵁ W).ι = pullback.fst h (S.fromSpecStalk x) → LBIso (N'.pull a) N := by
  first | exact @GlobalTheory.StalkLB.exists_lb_nhd | exact GlobalTheory.StalkLB.exists_lb_nhd | (intros; apply GlobalTheory.StalkLB.exists_lb_nhd <;> assumption)
