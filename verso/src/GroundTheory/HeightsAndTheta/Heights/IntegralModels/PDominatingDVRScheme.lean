import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDominatingDVR
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizuki
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizukiQuotientLength
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PTorsionFreeQuotientLength
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PBlowUpChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open AlgebraicGeometry

/- English proof (translation)
The claim follows from `DominatingDVR.proof (KrullAkizuki.proof (KrullAkizukiQuotientLength.proof TorsionFreeQuotientLength.proof)) BlowUpChart.proof`.
-/
theorem DominatingDVR.closed : DominatingDVR.Statement :=
  DominatingDVR.proof
    (KrullAkizuki.proof (KrullAkizukiQuotientLength.proof TorsionFreeQuotientLength.proof))
    BlowUpChart.proof

/- English proof (translation)
Introduce `hF`. Establish `hgen : genericPoint Z ⤳ z` using `(genericPoint_spec Z).specializes trivial`. Establish `hmem : genericPoint Z ∈ Set.range (Z.fromSpecStalk z)`. Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `hgen`.

Take `⟨y, hy⟩` from `hmem`. Establish `hmax : IsLocalRing.maximalIdeal (Z.presheaf.stalk z) = ⊥` using `(IsLocalRing.isField_iff_maximalIdeal_eq.mp hF)`. Establish `hyc : y = IsLocalRing.closedPoint (Z.presheaf.stalk z)`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `IsLocalRing.le_maximalIdeal y.isPrime.ne_top`. Conclude with `hmax.le.trans bot_le`. Apply `hz` to reduce the goal to its premises. Rewrite using `[← hy, hyc, Scheme.fromSpecStalk_closedPoint]`.
-/
theorem not_isField_stalk_of_ne_genericPoint (Z : Scheme.{0}) [IsIntegral Z] (z : Z)
    (hz : z ≠ genericPoint Z) : ¬ IsField (Z.presheaf.stalk z) := by
  intro hF
  have hgen : genericPoint Z ⤳ z := (genericPoint_spec Z).specializes trivial
  have hmem : genericPoint Z ∈ Set.range (Z.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]; exact hgen
  obtain ⟨y, hy⟩ := hmem
  have hmax : IsLocalRing.maximalIdeal (Z.presheaf.stalk z) = ⊥ :=
    (IsLocalRing.isField_iff_maximalIdeal_eq.mp hF)
  have hyc : y = IsLocalRing.closedPoint (Z.presheaf.stalk z) := by
    apply PrimeSpectrum.ext
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal y.isPrime.ne_top
    · exact hmax.le.trans bot_le
  apply hz
  rw [← hy, hyc, Scheme.fromSpecStalk_closedPoint]

/- English proof (translation)
Introduce `Z _ _ z hz`. Conclude with `DominatingDVR.closed (Z.presheaf.stalk z) (not_isField_stalk_of_ne_genericPoint Z z hz) Z.functionField`.
-/
theorem DominatingDVRScheme.proof : DominatingDVRScheme.Statement := by
  intro Z _ _ z hz
  exact DominatingDVR.closed (Z.presheaf.stalk z) (not_isField_stalk_of_ne_genericPoint Z z hz)
    Z.functionField

end GroundTheory.Heights₂.Heights.Model
