import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicProperties
open NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Introduce `D X s P`. Establish `hJ : (GlobalTheory.TwU.seamP s P).asIdeal = P.asIdeal.map (RingOfIntegers.mapRingEquiv s.iE)`. Use extensionality with `y`. Take `⟨x, rfl⟩` from `(RingOfIntegers.mapRingEquiv s.iE).surjective y`. Rewrite using `[GlobalTheory.TwU.mem_seamP, Ideal.mem_map_of_equiv]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨x, h, rfl⟩`. Introduce and unpack `⟨z, hz, hzx⟩`. Use `(RingOfIntegers.mapRingEquiv s.iE).injective hzx` as an intermediate fact.

Substitute `this` using the available equality. Conclude with `hz`. Unfold `Formalism.L2.Col.qOf`. Rewrite using `[Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]`. Conclude with `(Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv s.iE) hJ).toEquiv).symm`.
-/
theorem qOf_seamP : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.Col.Fields) (s : Formalism.L2.Ker.Seam D X) (P : HeightOneSpectrum (𝓞 X.E)), Formalism.L2.Col.qOf (GlobalTheory.TwU.seamP s P) = Formalism.L2.Col.qOf P := by
  intro D X s P
  have hJ : (GlobalTheory.TwU.seamP s P).asIdeal = P.asIdeal.map (RingOfIntegers.mapRingEquiv s.iE) := by
    ext y
    obtain ⟨x, rfl⟩ := (RingOfIntegers.mapRingEquiv s.iE).surjective y
    rw [GlobalTheory.TwU.mem_seamP, Ideal.mem_map_of_equiv]
    constructor
    · intro h; exact ⟨x, h, rfl⟩
    · rintro ⟨z, hz, hzx⟩
      have := (RingOfIntegers.mapRingEquiv s.iE).injective hzx
      subst this; exact hz
  unfold Formalism.L2.Col.qOf
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv s.iE) hJ).toEquiv).symm

end GlobalTheory
