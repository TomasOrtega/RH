import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalRingOfIsIntegralOfHenselian
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.NormalLocal

/- English proof (translation)
Set `B` to `A ⧸ 𝔭`. Set `K` to `FractionRing B`. Set `S` to `integralClosure B K`. Establish `: IsFractionRing S K` using `inferInstance`. Establish `hic : IsIntegrallyClosed S` using `(isIntegrallyClosed_iff_isIntegrallyClosedIn K).mpr inferInstance`.

Use `letI : Algebra A S := ((algebraMap B S).comp (Ideal.Quotient.mk 𝔭)).toAlgebra`. Establish `h1 : (Ideal.Quotient.mk 𝔭).IsIntegral` using `RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective`. Establish `h2 : (algebraMap B S).IsIntegral` using `fun x => Algebra.IsIntegral.isIntegral (R := B) x`. Establish `hint : (algebraMap A S).IsIntegral` using `RingHom.IsIntegral.trans _ _ h1 h2`. Use `haveI : Algebra.IsIntegral A S := ⟨fun x => hint x⟩`.

Establish `hloc : IsLocalRing S` using `GlobalTheory.IntClLocal.isLocalRing_of_isIntegral_of_henselian A S`. Establish `hinjK : Function.Injective (algebraMap B K)` using `IsFractionRing.injective B K`. Establish `hinj : Function.Injective (algebraMap B S)`. Introduce `x y h`. Conclude with `hinjK (congrArg Subtype.val h)`.

Use `⟨S, inferInstance, inferInstance, hic, hloc, algebraMap A S, hint, ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Rewrite using `[RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]`. Express the relevant statement in the definitionally equal form `(algebraMap B S) (Ideal.Quotient.mk 𝔭 a) = 0 ↔ _`. Rewrite using `[← map_zero (algebraMap B S), hinj.eq_iff]`.
-/
theorem exists_normal_local (A : Type) [CommRing A] [HenselianLocalRing A] (𝔭 : Ideal A) [𝔭.IsPrime] :
    ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : IsIntegrallyClosed S) (_ : IsLocalRing S) (f : A →+* S),
      f.IsIntegral ∧ RingHom.ker f = 𝔭 := by
  let B := A ⧸ 𝔭
  let K := FractionRing B
  let S := integralClosure B K
  have : IsFractionRing S K := inferInstance
  have hic : IsIntegrallyClosed S := (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mpr inferInstance
  letI : Algebra A S := ((algebraMap B S).comp (Ideal.Quotient.mk 𝔭)).toAlgebra
  have h1 : (Ideal.Quotient.mk 𝔭).IsIntegral := RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective
  have h2 : (algebraMap B S).IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := B) x
  have hint : (algebraMap A S).IsIntegral := RingHom.IsIntegral.trans _ _ h1 h2
  haveI : Algebra.IsIntegral A S := ⟨fun x => hint x⟩
  have hloc : IsLocalRing S := GlobalTheory.IntClLocal.isLocalRing_of_isIntegral_of_henselian A S
  have hinjK : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
  have hinj : Function.Injective (algebraMap B S) := by
    intro x y h
    exact hinjK (congrArg Subtype.val h)
  refine ⟨S, inferInstance, inferInstance, hic, hloc, algebraMap A S, hint, ?_⟩
  ext a
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
  change (algebraMap B S) (Ideal.Quotient.mk 𝔭 a) = 0 ↔ _
  rw [← map_zero (algebraMap B S), hinj.eq_iff]

end GlobalTheory.NormalLocal
