import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherian
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RelAmpleQProjNoeth.isQProjOver_of_relAmple_noeth` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsQProjOverOfRelAmpleOverQprojNoetherian.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.isQProjOver_of_relAmple_over_qproj_noetherian : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X : Scheme.{0}) (s : X ⟶ Sp K) (A : Over X) (L : LB A.left), IsQProjOver s → L.IsLB → Out.RelAmple A L → IsQProjOver (A.hom ≫ s) := by
  first | exact @GlobalTheory.RelAmpleQProjNoeth.isQProjOver_of_relAmple_noeth | exact GlobalTheory.RelAmpleQProjNoeth.isQProjOver_of_relAmple_noeth | (intros; apply GlobalTheory.RelAmpleQProjNoeth.isQProjOver_of_relAmple_noeth <;> assumption)
