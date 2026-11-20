import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedAlongAllTraitsRestrictAffineOpen
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUniformisedAlongAllTraitsRestrictAffineOpen.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.uniformisedAlongAllTraits_restrict_affineOpen : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (W : S.Opens) (hW : IsAffineOpen W),
    IsSemiAbelian G → UnifAlong G L.L → UnifAlong (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec).L := by
  first | exact @GlobalTheory.KeyVals.unifAlong_affineOpen | exact GlobalTheory.KeyVals.unifAlong_affineOpen | (intros; apply GlobalTheory.KeyVals.unifAlong_affineOpen <;> assumption)
