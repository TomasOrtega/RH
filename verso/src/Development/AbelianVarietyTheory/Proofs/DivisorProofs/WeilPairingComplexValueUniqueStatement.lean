import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingComplexValueUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWeilPairingComplexValueUnique.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.weilPairing_complex_value_unique : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (y : Sp ℂ ⟶ X) (k : ℤ) (x x' : Over.mk y ⟶ G) (c c' : ℂˣ), Out.WeilIs G L k x x' (unitOn c) → Out.WeilIs G L k x x' (unitOn c') → c = c' := by
  first | exact @GlobalTheory.WeilComplexUnique.weilIs_unitOn_unique_complex | exact GlobalTheory.WeilComplexUnique.weilIs_unitOn_unique_complex | (intros; apply GlobalTheory.WeilComplexUnique.weilIs_unitOn_unique_complex <;> assumption)
