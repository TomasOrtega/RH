import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MulAPullbackIsoPowSqSymmetricAbelianVariety
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FMulAPullbackIsoPowSqSymmetricAbelianVariety.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.mulA_pullback_iso_pow_sq_symmetric_abelianVariety : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (k : ℕ), M.IsLB → SymB M → LBIso (M.pull (Out.mulA P.A k).left) (lbPow M (k ^ 2)) := by
  first | exact @GlobalTheory.MulSym.lbIso_mulPull_of_symB | exact GlobalTheory.MulSym.lbIso_mulPull_of_symB | (intros; apply GlobalTheory.MulSym.lbIso_mulPull_of_symB <;> assumption)
