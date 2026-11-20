import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

/- English proof (translation)
Use `letI : Algebra A B := φ.toAlgebra`. Use `haveI : Algebra.IsIntegral A B := ⟨hφ⟩`. Use `haveI : P.LiesOver (IsLocalRing.maximalIdeal A) := ⟨hP.symm⟩`. Use `letI : Algebra (IsLocalRing.ResidueField A) (B ⧸ P) := Ideal.Quotient.algebraOfLiesOver P (IsLocalRing.maximalIdeal A)`. Use `haveI : IsScalarTower A (IsLocalRing.ResidueField A) (B ⧸ P) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`.

Use `haveI : Algebra.IsIntegral A (B ⧸ P) := inferInstance`. Use `haveI : Algebra.IsIntegral (IsLocalRing.ResidueField A) (B ⧸ P) := Algebra.IsIntegral.tower_top (R := A)`. Set `l : (B ⧸ P) →ₐ[IsLocalRing.ResidueField A] AlgebraicClosure (IsLocalRing.ResidueField A)` to `IsAlgClosed.lift`. Use `⟨l.toRingHom.comp (Ideal.Quotient.mk P), ?_⟩` and prove the remaining obligations. Use extensionality with `a`.

Establish `h` using `l.commutes (algebraMap A (IsLocalRing.ResidueField A) a)`. Rewrite `h` using `[← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`. Conclude with `h`.
-/
theorem exists_ringHom_algClosure_residueField_of_isIntegral (A B : Type) [CommRing A]
    [IsLocalRing A] [CommRing B] (φ : A →+* B) (hφ : φ.IsIntegral) (P : Ideal B) [P.IsPrime]
    (hP : P.comap φ = IsLocalRing.maximalIdeal A) :
    ∃ ψ : B →+* AlgebraicClosure (IsLocalRing.ResidueField A),
      ψ.comp φ = algebraMap A (AlgebraicClosure (IsLocalRing.ResidueField A)) := by
  letI : Algebra A B := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hφ⟩
  haveI : P.LiesOver (IsLocalRing.maximalIdeal A) := ⟨hP.symm⟩
  letI : Algebra (IsLocalRing.ResidueField A) (B ⧸ P) :=
    Ideal.Quotient.algebraOfLiesOver P (IsLocalRing.maximalIdeal A)
  haveI : IsScalarTower A (IsLocalRing.ResidueField A) (B ⧸ P) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral A (B ⧸ P) := inferInstance
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField A) (B ⧸ P) :=
    Algebra.IsIntegral.tower_top (R := A)
  let l : (B ⧸ P) →ₐ[IsLocalRing.ResidueField A] AlgebraicClosure (IsLocalRing.ResidueField A) :=
    IsAlgClosed.lift
  refine ⟨l.toRingHom.comp (Ideal.Quotient.mk P), ?_⟩
  ext a
  have h := l.commutes (algebraMap A (IsLocalRing.ResidueField A) a)
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
  exact h

/- English proof (translation)
Introduce `A _ _ Y g hi hs`. Use `haveI : IsAffine Y := isAffine_of_isAffineHom g`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (Y.isoSpec.inv ≫ g)`. Establish `h1 : IsIntegralHom (Spec.map φ)` using `by rw [hφ]; infer_instance`. Establish `h2 : Surjective (Spec.map φ)` using `by rw [hφ]; infer_instance`.

Establish `h3 : φ.hom.IsIntegral` using `IsIntegralHom.SpecMap_iff.mp h1`. Take `⟨P, hP⟩` from `h2.surj (IsLocalRing.closedPoint A)`. Establish `hP' : (PrimeSpectrum.asIdeal P).comap φ.hom = IsLocalRing.maximalIdeal A` using `congrArg PrimeSpectrum.asIdeal hP`. Use `haveI := PrimeSpectrum.isPrime P`. Take `⟨ψ, hψ⟩` from `exists_ringHom_algClosure_residueField_of_isIntegral A Γ(Y, ⊤) φ.hom h3 (PrimeSpectrum.asIdeal P) hP'`.

Use `⟨Spec.map (CommRingCat.ofHom ψ) ≫ Y.isoSpec.inv, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hφ, ← Spec.map_comp, ← hψ]`. Both sides reduce to the same expression.
-/
theorem exists_point_algClosure_residueField_of_isIntegralHom :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of A)),
    IsIntegralHom g → Surjective g → ∃ s : Spec (CommRingCat.of (AlgebraicClosure (IsLocalRing.ResidueField A))) ⟶ Y,
    s ≫ g = Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure (IsLocalRing.ResidueField A)))) := by
  intro A _ _ Y g hi hs
  haveI : IsAffine Y := isAffine_of_isAffineHom g
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Y.isoSpec.inv ≫ g)
  have h1 : IsIntegralHom (Spec.map φ) := by rw [hφ]; infer_instance
  have h2 : Surjective (Spec.map φ) := by rw [hφ]; infer_instance
  have h3 : φ.hom.IsIntegral := IsIntegralHom.SpecMap_iff.mp h1
  obtain ⟨P, hP⟩ := h2.surj (IsLocalRing.closedPoint A)
  have hP' : (PrimeSpectrum.asIdeal P).comap φ.hom = IsLocalRing.maximalIdeal A :=
    congrArg PrimeSpectrum.asIdeal hP
  haveI := PrimeSpectrum.isPrime P
  obtain ⟨ψ, hψ⟩ := exists_ringHom_algClosure_residueField_of_isIntegral A Γ(Y, ⊤) φ.hom h3
    (PrimeSpectrum.asIdeal P) hP'
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ Y.isoSpec.inv, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp, ← hψ]
  rfl

end GlobalTheory
