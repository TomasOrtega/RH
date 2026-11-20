import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationConstantOfPowerEq
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ValConstOfPowEq.valConst_of_powEq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FValuationConstantOfPowerEq.lean&line=320#L320)
-/
theorem _root_.GlobalTheory.T.valuation_constant_of_power_eq : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (Z : Scheme.{0}) (f : Z ⟶ Spec (.of O)) (D : LB Z), D.IsLB →
  ∀ sig : (D.pull (genericι f)).Gen, sig.IsGen →
  ∀ (M : ℕ) (n : ℤ) (gen : (lbPow D M).Gen), 1 ≤ M → gen.IsGen → PowEq f ϖ hϖ D sig M n gen →
  ValConst f ϖ D sig M n := by
  first | exact @GlobalTheory.ValConstOfPowEq.valConst_of_powEq | exact GlobalTheory.ValConstOfPowEq.valConst_of_powEq | (intros; apply GlobalTheory.ValConstOfPowEq.valConst_of_powEq <;> assumption)
