import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGroupRangeUnionClosedFibres
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Desc.UnionLocal.exists_locGrp_range_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLocalGroupRangeUnionClosedFibres.lean&line=278#L278)
-/
theorem _root_.GlobalTheory.T.exists_localGroup_range_union_closedFibres : ∀ (σ : Setup) (E : Emb σ), σ.Common → ∀ x : Sp σ.R, ∃ g : σ.R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ Set.range h = E.U ∩ E.p ⁻¹' {z : Sp σ.R | g ∉ z.asIdeal} := by
  first | exact @GlobalTheory.Desc.UnionLocal.exists_locGrp_range_eq | exact GlobalTheory.Desc.UnionLocal.exists_locGrp_range_eq | (intros; apply GlobalTheory.Desc.UnionLocal.exists_locGrp_range_eq <;> assumption)
