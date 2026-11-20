import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Use `haveI hp : (RingHom.ker h).IsPrime := RingHom.ker_isPrime h`. Take `⟨Q, -, hQ, hQc⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker h) (⊥ : Ideal C) (by simpa [← RingHom.ker_eq_comap_bot] using hk)`. Use `haveI : Q.LiesOver (RingHom.ker h) := (Ideal.liesOver_iff _ _).mpr hQc.symm`. Use `letI : Algebra (A ⧸ RingHom.ker h) K := (RingHom.kerLift h).toAlgebra`. Use `haveI : FaithfulSMul (A ⧸ RingHom.ker h) K := (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective h)`.

Use `haveI : FaithfulSMul (A ⧸ RingHom.ker h) (C ⧸ Q) := inferInstance`. Use `haveI : Nontrivial (A ⧸ RingHom.ker h) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top`. Use `haveI : Algebra.IsIntegral (A ⧸ RingHom.ker h) (C ⧸ Q) := Ideal.Quotient.algebra_isIntegral_of_liesOver (A := A) (p := RingHom.ker h) (P := Q)`. Use `haveI : Algebra.IsAlgebraic (A ⧸ RingHom.ker h) (C ⧸ Q) := Algebra.IsIntegral.isAlgebraic`. Use `haveI : Module.IsTorsionFree (A ⧸ RingHom.ker h) (C ⧸ Q) := Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective _ _)`.

Use `haveI : Module.IsTorsionFree (A ⧸ RingHom.ker h) K := Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective h)`. Set `φ : (C ⧸ Q) →ₐ[A ⧸ RingHom.ker h] K` to `IsAlgClosed.lift`. Use `⟨φ.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Establish `e1 : (Ideal.Quotient.mk Q) (algebraMap A C a) = algebraMap (A ⧸ RingHom.ker h) (C ⧸ Q) (Ideal.Quotient.mk _ a)` using `rfl`.

Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Rewrite using `[e1, φ.commutes]`. Both sides reduce to the same expression.
-/
theorem ringHom_extend_of_isIntegral_isAlgClosed (A C K : Type) [CommRing A] [CommRing C]
    [Algebra A C] [Algebra.IsIntegral A C] [Field K] [IsAlgClosed K] (h : A →+* K)
    (hk : RingHom.ker (algebraMap A C) ≤ RingHom.ker h) :
    ∃ ψ : C →+* K, ψ.comp (algebraMap A C) = h := by
  classical
  haveI hp : (RingHom.ker h).IsPrime := RingHom.ker_isPrime h
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker h) (⊥ : Ideal C)
    (by simpa [← RingHom.ker_eq_comap_bot] using hk)
  haveI : Q.LiesOver (RingHom.ker h) := (Ideal.liesOver_iff _ _).mpr hQc.symm
  letI : Algebra (A ⧸ RingHom.ker h) K := (RingHom.kerLift h).toAlgebra
  haveI : FaithfulSMul (A ⧸ RingHom.ker h) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective h)
  haveI : FaithfulSMul (A ⧸ RingHom.ker h) (C ⧸ Q) := inferInstance
  haveI : Nontrivial (A ⧸ RingHom.ker h) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
  haveI : Algebra.IsIntegral (A ⧸ RingHom.ker h) (C ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver (A := A) (p := RingHom.ker h) (P := Q)
  haveI : Algebra.IsAlgebraic (A ⧸ RingHom.ker h) (C ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker h) (C ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective _ _)
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker h) K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective h)
  let φ : (C ⧸ Q) →ₐ[A ⧸ RingHom.ker h] K := IsAlgClosed.lift
  refine ⟨φ.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  ext a
  have e1 : (Ideal.Quotient.mk Q) (algebraMap A C a) =
      algebraMap (A ⧸ RingHom.ker h) (C ⧸ Q) (Ideal.Quotient.mk _ a) := rfl
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [e1, φ.commutes]
  rfl

end GlobalTheory
