import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open GlobalTheory.EtC

namespace GlobalTheory

/- English proof (translation)
Introduce `k B _ _ _ _ _ hB`. Use `letI : Field B := hB.toField`. Use `haveI : Module.Finite k B := finite_of_finite_type_of_isJacobsonRing k B`. Establish `hbk : Function.Bijective (algebraMap k B)` using `IsAlgClosed.algebraMap_bijective_of_isIntegral`. Use `haveI : IsAlgClosed B := IsAlgClosed.of_ringEquiv k B (RingEquiv.ofBijective (algebraMap k B) hbk)`.

Use `⟨Field.henselian B, ?_⟩` and prove the remaining obligations. Establish `hbij : Function.Bijective (IsLocalRing.residue B)` using `⟨(IsLocalRing.residue B).injective, Ideal.Quotient.mk_surjective⟩`. Use `haveI : IsAlgClosed (IsLocalRing.ResidueField B) := IsAlgClosed.of_ringEquiv B _ (RingEquiv.ofBijective _ hbij)`. Conclude with `IsSepClosed.of_isAlgClosed _`.
-/
theorem field_finiteType_algClosed_SH : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B], IsField B → SH B := by
  intro k B _ _ _ _ _ hB
  letI : Field B := hB.toField
  haveI : Module.Finite k B := finite_of_finite_type_of_isJacobsonRing k B
  have hbk : Function.Bijective (algebraMap k B) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  haveI : IsAlgClosed B := IsAlgClosed.of_ringEquiv k B
    (RingEquiv.ofBijective (algebraMap k B) hbk)
  refine ⟨Field.henselian B, ?_⟩
  have hbij : Function.Bijective (IsLocalRing.residue B) :=
    ⟨(IsLocalRing.residue B).injective, Ideal.Quotient.mk_surjective⟩
  haveI : IsAlgClosed (IsLocalRing.ResidueField B) :=
    IsAlgClosed.of_ringEquiv B _ (RingEquiv.ofBijective _ hbij)
  exact IsSepClosed.of_isAlgClosed _

end GlobalTheory
