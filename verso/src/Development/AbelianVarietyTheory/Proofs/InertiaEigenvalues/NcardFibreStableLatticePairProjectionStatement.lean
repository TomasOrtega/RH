import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NcardFibreStableLatticePairProjection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNcardFibreStableLatticePairProjection.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.ncard_fibre_stableLatticePairProjection : ∀ (O E A₁ A₂ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂), resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0 → ∀ y : LatPair O E g₁ g₂, ((latProj O E g₁ g₂ ⁻¹' {y}).ncard : ℚ) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) := by
  first | exact @GlobalTheory.UnitLemma.ncard_fibre_latProj | exact GlobalTheory.UnitLemma.ncard_fibre_latProj | (intros; apply GlobalTheory.UnitLemma.ncard_fibre_latProj <;> assumption)
