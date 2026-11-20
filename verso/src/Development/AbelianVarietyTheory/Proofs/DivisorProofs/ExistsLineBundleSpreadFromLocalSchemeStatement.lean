import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleSpreadFromLocalScheme
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLineBundleSpreadFromLocalScheme.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exists_lineBundle_spread_from_localScheme : ∀ {S Y U YU : Scheme.{0}} [IsLocallyNoetherian S] (f : Y ⟶ S) [QuasiCompact f] [QuasiSeparated f] (j : U ⟶ S) [IsOpenImmersion j] (e : YU ⟶ Y) (fU : YU ⟶ U), IsPullback e fU f j → ∀ (L : LB YU), L.IsLB → ∀ (x : S) (N : LB (pullback f (S.fromSpecStalk x))), N.IsLB → (∀ (T : Scheme.{0}) (a : T ⟶ pullback f (S.fromSpecStalk x)) (b : T ⟶ YU), a ≫ pullback.fst f (S.fromSpecStalk x) = b ≫ e → LBIso (N.pull a) (L.pull b)) → ∃ W : S.Opens, x ∈ W ∧ ∃ N' : LB ↑(f ⁻¹ᵁ W), N'.IsLB ∧ ∀ (T : Scheme.{0}) (a : T ⟶ ↑(f ⁻¹ᵁ W)) (b : T ⟶ YU), a ≫ (f ⁻¹ᵁ W).ι = b ≫ e → LBIso (N'.pull a) (L.pull b) := by
  first | exact @GlobalTheory.SpreadLB.exists_spread | exact GlobalTheory.SpreadLB.exists_spread | (intros; apply GlobalTheory.SpreadLB.exists_spread <;> assumption)
