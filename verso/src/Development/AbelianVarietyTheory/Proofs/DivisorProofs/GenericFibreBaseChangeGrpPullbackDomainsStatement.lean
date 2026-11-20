import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreBaseChangeGrpPullbackDomains
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGenericFibreBaseChangeGrpPullbackDomains.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.genericFibre_baseChange_grpPullback_domains : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (a : FractionRing R →+* FractionRing R'), a.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp ρ → ∀ (G : Over (Sp R)) [GrpObj G], ∃ π₀ : ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).left ⟶ ((Over.pullback (jK R)).obj G).left, IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) ((Over.pullback (jK R)).obj G) (spMap a) π₀ ∧ ∀ L : LB G.left, L.IsLB → LBIso ((L.pull (pullback.fst G.hom (spMap ρ))).pull (pullback.fst (pullback.snd G.hom (spMap ρ)) (jK R'))) ((L.pull (pullback.fst G.hom (jK R))).pull π₀) := by
  first | exact @GlobalTheory.GenFibreBaseChange.genFibre_pull | exact GlobalTheory.GenFibreBaseChange.genFibre_pull | (intros; apply GlobalTheory.GenFibreBaseChange.genFibre_pull <;> assumption)
