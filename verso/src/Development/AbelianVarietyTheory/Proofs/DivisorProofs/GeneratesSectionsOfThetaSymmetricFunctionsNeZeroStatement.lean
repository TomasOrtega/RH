import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratesSectionsOfThetaSymmetricFunctionsNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UMin.GenSym.isGenSec_of_symAt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGeneratesSectionsOfThetaSymmetricFunctionsNeZero.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.generates_sections_of_thetaSymmetricFunctions_ne_zero : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (x : Sp Ω ⟶ S) (θ : SecAt G L x) (e : Fin N → Ω), Odd m → N = m ^ (4 * g) → PolFib G L g x → SymAt G L ρ m x θ e → (∃ j, e j ≠ 0) → IsGenSec G L ((1 : ℕ) : ℤ) θ := by
  first | exact @GlobalTheory.UMin.GenSym.isGenSec_of_symAt | exact GlobalTheory.UMin.GenSym.isGenSec_of_symAt | (intros; apply GlobalTheory.UMin.GenSym.isGenSec_of_symAt <;> assumption)
