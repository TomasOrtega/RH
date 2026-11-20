import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeparatedSiegelModuliOverIntegers
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDirectFactorOfIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLineBundleEighthPowerIsoPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SepSiegel.isSeparated_toZ` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsSeparatedSiegelModuliOverIntegers.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.isSeparated_siegelModuli_over_integers : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)), IsSeparated (toZ F.X) := by
  first | exact @GlobalTheory.SepSiegel.isSeparated_toZ | exact GlobalTheory.SepSiegel.isSeparated_toZ | (intros; apply GlobalTheory.SepSiegel.isSeparated_toZ <;> assumption)
