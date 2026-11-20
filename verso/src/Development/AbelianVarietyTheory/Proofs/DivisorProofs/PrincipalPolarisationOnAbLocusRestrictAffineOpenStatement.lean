import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOnAbLocusRestrictAffineOpen
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPrincipalPolarisationOnAbLocusRestrictAffineOpen.lean&line=135#L135)
-/
theorem _root_.GlobalTheory.T.principalPolarisationOnAbLocus_restrict_affineOpen : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (W : S.Opens) (hW : IsAffineOpen W),
    IsOpen (abLocus G) → PolOnAb G L.L → PolOnAb (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec).L := by
  first | exact @GlobalTheory.KeyVals.PolOpen.polOnAb_affine | exact GlobalTheory.KeyVals.PolOpen.polOnAb_affine | (intros; apply GlobalTheory.KeyVals.PolOpen.polOnAb_affine <;> assumption)
