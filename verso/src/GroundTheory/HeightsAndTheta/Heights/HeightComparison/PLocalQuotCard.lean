import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightLocalQuotCard
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PSubringPrimeMaximal
import GroundTheory.HeightsAndTheta.Heights.Intersections.CardLength
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KrullDimQuotientEqOneIffEqBot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField IsLocalRing

/- English proof (translation)
Introduce `L _ _ O hft _ m _ f hf`. Establish `: IsNoetherianRing O` using `Algebra.FiniteType.isNoetherianRing ℤ O`. Establish `hO : Ring.KrullDimLE 1 O` using `Ring.KrullDimLE.mk₁' fun q hq0 hq ↦ SubringPrimeMaximal.proof L O q hq hq0`. Set `R` to `Localization.AtPrime m`. Establish `: Ring.KrullDimLE 1 R`.

Rewrite using `[Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height m R]`. Conclude with `Ideal.height_le_ringKrullDim_of_isPrime.trans (Ring.krullDimLE_iff.mp hO)`. Establish `hf' : algebraMap O R f ≠ 0`. Introduce `h`. Apply `hf` to reduce the goal to its premises.

Conclude with `IsLocalization.injective R m.primeCompl_le_nonZeroDivisors (by simpa using h)`. Establish `hspan : Ideal.span {algebraMap O R f} = LinearMap.range (LinearMap.lsmul R R (algebraMap O R f))`. Use extensionality with `z`. Simplify using `[Ideal.mem_span_singleton', LinearMap.mem_range, mul_comm]`. Establish `hfin : Module.length R (R ⧸ Ideal.span {algebraMap O R f}) ≠ ⊤`.

Rewrite using `[hspan]`. Conclude with `ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top R hf'`. Unfold `localQuotLength`. Rewrite using `[Inter.card_eq_card_residueField_pow_length _ hfin]`. Use `congr 1`.

Conclude with `Nat.card_congr (IsLocalization.AtPrime.equivQuotMaximalIdeal m R).toEquiv.symm`.
-/
theorem LocalQuotCard.proof : LocalQuotCard.Statement := by
  intro L _ _ O hft _ m _ f hf
  have : IsNoetherianRing O := Algebra.FiniteType.isNoetherianRing ℤ O
  have hO : Ring.KrullDimLE 1 O := Ring.KrullDimLE.mk₁' fun q hq0 hq ↦
    SubringPrimeMaximal.proof L O q hq hq0
  let R := Localization.AtPrime m
  have : Ring.KrullDimLE 1 R := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height m R]
    exact Ideal.height_le_ringKrullDim_of_isPrime.trans (Ring.krullDimLE_iff.mp hO)
  have hf' : algebraMap O R f ≠ 0 := by
    intro h
    apply hf
    exact IsLocalization.injective R m.primeCompl_le_nonZeroDivisors (by simpa using h)
  have hspan : Ideal.span {algebraMap O R f} = LinearMap.range (LinearMap.lsmul R R (algebraMap O R f)) := by
    ext z
    simp [Ideal.mem_span_singleton', LinearMap.mem_range, mul_comm]
  have hfin : Module.length R (R ⧸ Ideal.span {algebraMap O R f}) ≠ ⊤ := by
    rw [hspan]
    exact ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top R hf'
  unfold localQuotLength
  rw [Inter.card_eq_card_residueField_pow_length _ hfin]
  congr 1
  exact Nat.card_congr (IsLocalization.AtPrime.equivQuotMaximalIdeal m R).toEquiv.symm

end GroundTheory.Heights₂.Heights
