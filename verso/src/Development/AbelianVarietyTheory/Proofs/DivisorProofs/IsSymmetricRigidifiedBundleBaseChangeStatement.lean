import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricRigidifiedBundleBaseChange
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsSymmetricRigidifiedBundleBaseChange.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.isSymmetric_rigidifiedBundleBaseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    L.IsSymmetric → (KeyVals.bL L ξ).IsSymmetric := by
  first | exact @GlobalTheory.KeyVals.isSymmetric_bL | exact GlobalTheory.KeyVals.isSymmetric_bL | (intros; apply GlobalTheory.KeyVals.isSymmetric_bL <;> assumption)
