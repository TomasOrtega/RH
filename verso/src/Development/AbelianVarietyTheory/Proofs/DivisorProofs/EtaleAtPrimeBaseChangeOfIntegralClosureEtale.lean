import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
open IsLocalRing Polynomial
open scoped TensorProduct
open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth GlobalTheory.KeyOriginBC

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

/- English proof (translation)
Introduce `A R R₁ DA _ _ _ _ _ _ κ P₁ _ h`. Use `letI := closureAlg A R DA`. Use `letI iRS : Algebra R (Localization.AtPrime P₁) := ((algebraMap R₁ (Localization.AtPrime P₁)).comp κ).toAlgebra`. Establish `hunit : ∀ y : (P₁.comap κ).primeCompl, IsUnit (algebraMap R (Localization.AtPrime P₁) y)`. Introduce `y`.

Conclude with `IsLocalization.map_units (Localization.AtPrime P₁) (⟨κ y, y.2⟩ : P₁.primeCompl)`. Use `letI : Algebra (Localization.AtPrime (P₁.comap κ)) (Localization.AtPrime P₁) := (IsLocalization.lift (M := (P₁.comap κ).primeCompl) hunit).toAlgebra`. Use `haveI : IsScalarTower R (Localization.AtPrime (P₁.comap κ)) (Localization.AtPrime P₁) := IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq (M := (P₁.comap κ).primeCompl) hunit x).symm)`. Use `haveI : Algebra.Etale (Localization.AtPrime (P₁.comap κ)) (Localization.AtPrime (P₁.comap κ) ⊗[R] closure A R DA) := h`. Use `haveI : Algebra.Etale (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[Localization.AtPrime (P₁.comap κ)] (Localization.AtPrime (P₁.comap κ) ⊗[R] closure A R DA)) := Algebra.Etale.baseChange _ _ _`.

Conclude with `Algebra.Etale.of_equiv (Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime (P₁.comap κ)) (Localization.AtPrime P₁) (Localization.AtPrime P₁) (closure A R DA))`.
-/
theorem closureEtaleAt_comap_baseChange_atPrime : ∀ (A R R₁ DA : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing R₁]
    [CommRing DA] [Algebra (GenFib A R) DA] (κ : R →+* R₁) (P₁ : Ideal R₁) [P₁.IsPrime],
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A R DA (P₁.comap κ) →
    letI := closureAlg A R DA
    letI : Algebra R (Localization.AtPrime P₁) :=
      ((algebraMap R₁ (Localization.AtPrime P₁)).comp κ).toAlgebra
    Algebra.Etale (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R] closure A R DA) := by
  intro A R R₁ DA _ _ _ _ _ _ κ P₁ _ h
  letI := closureAlg A R DA
  letI iRS : Algebra R (Localization.AtPrime P₁) :=
    ((algebraMap R₁ (Localization.AtPrime P₁)).comp κ).toAlgebra
  have hunit : ∀ y : (P₁.comap κ).primeCompl,
      IsUnit (algebraMap R (Localization.AtPrime P₁) y) := by
    intro y
    exact IsLocalization.map_units (Localization.AtPrime P₁)
      (⟨κ y, y.2⟩ : P₁.primeCompl)
  letI : Algebra (Localization.AtPrime (P₁.comap κ)) (Localization.AtPrime P₁) :=
    (IsLocalization.lift (M := (P₁.comap κ).primeCompl) hunit).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime (P₁.comap κ)) (Localization.AtPrime P₁) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (IsLocalization.lift_eq (M := (P₁.comap κ).primeCompl) hunit x).symm)
  haveI : Algebra.Etale (Localization.AtPrime (P₁.comap κ))
      (Localization.AtPrime (P₁.comap κ) ⊗[R] closure A R DA) := h
  haveI : Algebra.Etale (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[Localization.AtPrime (P₁.comap κ)]
      (Localization.AtPrime (P₁.comap κ) ⊗[R] closure A R DA)) :=
    Algebra.Etale.baseChange _ _ _
  exact Algebra.Etale.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime (P₁.comap κ))
      (Localization.AtPrime P₁) (Localization.AtPrime P₁) (closure A R DA))

end GlobalTheory.KeyOriginEnlarge
