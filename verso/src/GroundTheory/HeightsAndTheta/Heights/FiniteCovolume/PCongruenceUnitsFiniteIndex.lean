import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsVectorOrbits

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

/- English proof (translation)
Introduce `N hN`. Establish `hI : Ideal.span {(N : 𝓞 E)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hN.ne'` after adjusting the coercions. Establish `: Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})` using `Ideal.finiteQuotientOfFreeOfNeBot _ hI`.

Establish `: Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ` using `Finite.of_injective _ Units.val_injective`. Establish `: (congruenceUnits E N).FiniteIndex` using `Subgroup.finiteIndex_ker _`. Conclude with `Subgroup.FiniteIndex.index_ne_zero`.
-/
theorem CongruenceUnitsFiniteIndex.proof (E : Type*) [Field E] [NumberField E] :
    CongruenceUnitsFiniteIndex.Statement E := by
  intro N hN
  have hI : Ideal.span {(N : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ :=
    Finite.of_injective _ Units.val_injective
  have : (congruenceUnits E N).FiniteIndex := Subgroup.finiteIndex_ker _
  exact Subgroup.FiniteIndex.index_ne_zero

end GroundTheory.Heights₂.Heights.FiniteCovolume
