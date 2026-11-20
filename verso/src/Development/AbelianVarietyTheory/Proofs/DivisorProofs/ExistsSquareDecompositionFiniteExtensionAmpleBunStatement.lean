import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareDecompositionFiniteExtensionAmpleBun
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSquareDecompositionFiniteExtensionAmpleBun.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.exists_squareDecomposition_finiteExtension_ampleBundle : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB → RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K'), SqDec ((Over.pullback (spMap (algebraMap K K'))).obj A) (L.pull (pullback.fst A.hom (spMap (algebraMap K K')))) (M.pull (pullback.fst A.hom (spMap (algebraMap K K')))) := by
  first | exact @GlobalTheory.SqDecFinite.sqDec_of_finite_extension | exact GlobalTheory.SqDecFinite.sqDec_of_finite_extension | (intros; apply GlobalTheory.SqDecFinite.sqDec_of_finite_extension <;> assumption)
