import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsToSemiAbelianOfLocallyNormalNoetherian
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExtendsToSemiAbelianOfLocallyNormalNoetherian.lean&line=188#L188)
-/
theorem _root_.GlobalTheory.T.extendsToSemiAbelian_of_locally_normal_noetherian : ∀ (X S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A], IsAbelianScheme A → (∀ s : S, ∃ U : S.Opens, s ∈ U ∧ HasExt (j ∣_ U) ((Over.pullback (j ⁻¹ᵁ U).ι).obj A)) → HasExt j A := by
  first | exact @GlobalTheory.ExtGlue.hasExt_of_locally | exact GlobalTheory.ExtGlue.hasExt_of_locally | (intros; apply GlobalTheory.ExtGlue.hasExt_of_locally <;> assumption)
