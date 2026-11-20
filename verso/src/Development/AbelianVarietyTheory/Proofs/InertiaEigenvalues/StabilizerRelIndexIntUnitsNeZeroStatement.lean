import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StabilizerRelIndexIntUnitsNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FStabilizerRelIndexIntUnitsNeZero.lean&line=126#L126)
-/
theorem _root_.GlobalTheory.T.stabilizer_relIndex_intUnits_ne_zero' : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → ∀ L : stLat O E g, (MulAction.stabilizer Aˣ L).relIndex (intUnits O A) ≠ 0 := by
  first | exact @GlobalTheory.UnitLemma.StabIdx.stabilizer_relIndex_intUnits_ne_zero | exact GlobalTheory.UnitLemma.StabIdx.stabilizer_relIndex_intUnits_ne_zero | (intros; apply GlobalTheory.UnitLemma.StabIdx.stabilizer_relIndex_intUnits_ne_zero <;> assumption)
