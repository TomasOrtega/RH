import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIffEtaleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorExistsPointFiniteSeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeIsDomainIsIntegrallyClos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedOfFormallyEtale
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth

/- English proof (translation)
Use `letI iRD : Algebra R D := (baseHom A R D).toAlgebra`. Use `haveI : IsScalarTower R (GlobalTheory.LocAcyc.GenFib A R) D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Set `M` to `Algebra.algebraMapSubmonoid R (nonZeroDivisors A)`. Use `haveI : Module.Flat R (GlobalTheory.LocAcyc.GenFib A R) := IsLocalization.flat _ M`. Use `haveI : Module.Flat R D := Module.Flat.trans R (GlobalTheory.LocAcyc.GenFib A R) D`.

Use `haveI : Algebra.FormallyEtale R (GlobalTheory.LocAcyc.GenFib A R) := Algebra.FormallyEtale.of_isLocalization M`. Use `haveI : Algebra.FormallyEtale R D := Algebra.FormallyEtale.comp R (GlobalTheory.LocAcyc.GenFib A R) D`. Use `haveI : Algebra.EssFiniteType R (GlobalTheory.LocAcyc.GenFib A R) := Algebra.EssFiniteType.of_isLocalization _ M`. Use `haveI : Algebra.EssFiniteType R D := Algebra.EssFiniteType.comp R (GlobalTheory.LocAcyc.GenFib A R) D`. Establish `h1 : Module.Finite R (integralClosure R (R ⊗[R] D))` using `GlobalTheory.RootFibre.finite_integralClosure R D R`.

Establish `e` using `AlgEquiv.mapIntegralClosure (Algebra.TensorProduct.lid R D)`. Establish `h2 : Module.Finite R (integralClosure R D)` using `Module.Finite.equiv e.toLinearEquiv`. Use `letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D`. Set `f : integralClosure R D ≃ₗ[R] GlobalTheory.KeyOriginNoeth.closure A R D` to `{ toFun := fun x => ⟨x.1, x.2⟩ invFun := fun x => ⟨x.1, x.2⟩ map_add' := fun _ _ => rfl map_smul' := fun r x => by`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show r • x.1 = (baseHom A R D r) * x.1`. Both sides reduce to the same expression. Use `left_inv := fun _ => rfl`. Use `right_inv := fun _ => rfl }`. Conclude with `Module.Finite.equiv f`.
-/
theorem finite_closure (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [Algebra A R] [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D] :
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    Module.Finite R (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  letI iRD : Algebra R D := (baseHom A R D).toAlgebra
  haveI : IsScalarTower R (GlobalTheory.LocAcyc.GenFib A R) D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let M := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)
  haveI : Module.Flat R (GlobalTheory.LocAcyc.GenFib A R) := IsLocalization.flat _ M
  haveI : Module.Flat R D := Module.Flat.trans R (GlobalTheory.LocAcyc.GenFib A R) D
  haveI : Algebra.FormallyEtale R (GlobalTheory.LocAcyc.GenFib A R) := Algebra.FormallyEtale.of_isLocalization M
  haveI : Algebra.FormallyEtale R D := Algebra.FormallyEtale.comp R (GlobalTheory.LocAcyc.GenFib A R) D
  haveI : Algebra.EssFiniteType R (GlobalTheory.LocAcyc.GenFib A R) := Algebra.EssFiniteType.of_isLocalization _ M
  haveI : Algebra.EssFiniteType R D := Algebra.EssFiniteType.comp R (GlobalTheory.LocAcyc.GenFib A R) D
  have h1 : Module.Finite R (integralClosure R (R ⊗[R] D)) :=
    GlobalTheory.RootFibre.finite_integralClosure R D R
  have e := AlgEquiv.mapIntegralClosure (Algebra.TensorProduct.lid R D)
  have h2 : Module.Finite R (integralClosure R D) := Module.Finite.equiv e.toLinearEquiv
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  let f : integralClosure R D ≃ₗ[R] GlobalTheory.KeyOriginNoeth.closure A R D :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        apply Subtype.ext
        show r • x.1 = (baseHom A R D r) * x.1
        rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Module.Finite.equiv f

end GlobalTheory.KeyOriginNoeth
