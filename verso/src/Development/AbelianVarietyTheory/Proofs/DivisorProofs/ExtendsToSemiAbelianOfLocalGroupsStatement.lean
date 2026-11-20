import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsToSemiAbelianOfLocalGroups
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Desc.Emb.hasExt_of_locGrp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExtendsToSemiAbelianOfLocalGroups.lean&line=167#L167)
-/
theorem _root_.GlobalTheory.T.extendsToSemiAbelian_of_local_groups : ∀ (σ : Setup) (E : Emb σ), σ.Common → (∀ x : Sp σ.R, ∃ g : σ.R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ Set.range h = E.U ∩ E.p ⁻¹' {z : Sp σ.R | g ∉ z.asIdeal}) → HasExt (awayMap σ.f) σ.A := by
  first | exact @GlobalTheory.Desc.Emb.hasExt_of_locGrp | exact GlobalTheory.Desc.Emb.hasExt_of_locGrp | (intros; apply GlobalTheory.Desc.Emb.hasExt_of_locGrp <;> assumption)
