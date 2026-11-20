import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusRankEqRankThetaGroupOfPointPerp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTorusRankEqRankThetaGroupOfPointPerp.lean&line=218#L218)
-/
theorem _root_.GlobalTheory.T.torusRank_eq_rank_thetaGroupOfPoint_perp : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Big → S.Over₀ M U₀ → S.IsEE M U₀ EE → ∀ w : M.Z, ∃ r : ℕ, RkAt FinalForm.G w r ∧ Nonempty (S.TT M w ≃+ (Fin r → ZMod (S.r * S.N))) := by
  first | exact @GlobalTheory.ThetaDvr.TorRank.rkAt_tt_equiv | exact GlobalTheory.ThetaDvr.TorRank.rkAt_tt_equiv | (intros; apply GlobalTheory.ThetaDvr.TorRank.rkAt_tt_equiv <;> assumption)
