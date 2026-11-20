import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendAdicCompletionLocalizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularFibreOfLiftedPartialDerivationsStatement
open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `Λ _ _ _ _ n P _ K _ _ _ hinj`. Set `S₀` to `MvPolynomial (Fin n) Λ`. Set `R` to `Localization.AtPrime P`. Set `B` to `AdicCompletion (maximalIdeal R) R`. Use `haveI : IsRegularLocalRing R := inferInstance`.

Use `haveI : IsRegularLocalRing B := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion R`. Use `haveI : IsRegularRing B := GlobalTheory.isRegularRing_of_isRegularLocalRing B`. Use `letI : Algebra S₀ K := ((algebraMap R K).comp (algebraMap S₀ R)).toAlgebra`. Use `haveI : IsScalarTower S₀ R K := .of_algebraMap_eq fun _ => rfl`. Use `haveI : Algebra.EssFiniteType S₀ R := Algebra.EssFiniteType.of_isLocalization R P.primeCompl`.

Use `haveI : Algebra.EssFiniteType S₀ K := Algebra.EssFiniteType.comp S₀ R K`. Establish `hC : ∀ a : Λ, algebraMap S₀ K (MvPolynomial.C a) = 0 → a = 0`. Introduce `a ha`. Apply `hinj a` to reduce the goal to its premises. Rewrite using `[IsScalarTower.algebraMap_apply Λ S₀ R a]`.

Conclude with `ha`. Establish `hD : ∀ s : Fin n, ∃ D : Derivation ℤ B B, ∀ x, D (algebraMap S₀ B x) = algebraMap S₀ B (MvPolynomial.pderiv s x)` using `fun s => GlobalTheory.T.exists_derivation_extend_adicCompletion_localization S₀ P ((MvPolynomial.pderiv s).restrictScalars ℤ)`. Establish `hD' : ∀ s : Fin n, ∃ D : @Derivation ℤ B B _ _ _ (Ring.toIntAlgebra B) _ _, ∀ x, D (algebraMap S₀ B x) = algebraMap S₀ B (MvPolynomial.pderiv s x)`. Introduce `s`. Take `⟨D, hD⟩` from `hD s`.

Conclude with `⟨@Derivation.mk ℤ B B _ _ _ (Ring.toIntAlgebra B) _ _ D.toLinearMap D.map_one_eq_zero' D.leibniz', hD⟩`. Establish `h` using `GlobalTheory.T.regular_fibre_of_lifted_partialDerivations Λ (Fin n) B K hC hD'`. Set `e : B ⊗[R] K ≃ₐ[R] B ⊗[S₀] K` to `IsLocalization.algebraTensorEquiv P.primeCompl R B K`. Conclude with `IsRegularRing.of_ringEquiv e.symm.toRingEquiv`.
-/
theorem isRegularRing_adicCompletion_tensor_of_mvPolynomial :
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (n : ℕ)
      (P : Ideal (MvPolynomial (Fin n) Λ)) [P.IsPrime] (K : Type) [Field K]
      [Algebra (Localization.AtPrime P) K] [Algebra.EssFiniteType (Localization.AtPrime P) K],
      (∀ a : Λ, algebraMap (Localization.AtPrime P) K
        (algebraMap Λ (Localization.AtPrime P) a) = 0 → a = 0) →
      IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime P))
        (Localization.AtPrime P) ⊗[Localization.AtPrime P] K) := by
  intro Λ _ _ _ _ n P _ K _ _ _ hinj
  let S₀ := MvPolynomial (Fin n) Λ
  let R := Localization.AtPrime P
  let B := AdicCompletion (maximalIdeal R) R
  haveI : IsRegularLocalRing R := inferInstance
  haveI : IsRegularLocalRing B := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion R
  haveI : IsRegularRing B := GlobalTheory.isRegularRing_of_isRegularLocalRing B
  letI : Algebra S₀ K := ((algebraMap R K).comp (algebraMap S₀ R)).toAlgebra
  haveI : IsScalarTower S₀ R K := .of_algebraMap_eq fun _ => rfl
  haveI : Algebra.EssFiniteType S₀ R := Algebra.EssFiniteType.of_isLocalization R P.primeCompl
  haveI : Algebra.EssFiniteType S₀ K := Algebra.EssFiniteType.comp S₀ R K
  have hC : ∀ a : Λ, algebraMap S₀ K (MvPolynomial.C a) = 0 → a = 0 := by
    intro a ha
    apply hinj a
    rw [IsScalarTower.algebraMap_apply Λ S₀ R a]
    exact ha
  have hD : ∀ s : Fin n, ∃ D : Derivation ℤ B B, ∀ x,
      D (algebraMap S₀ B x) = algebraMap S₀ B (MvPolynomial.pderiv s x) := fun s =>
    GlobalTheory.T.exists_derivation_extend_adicCompletion_localization S₀ P ((MvPolynomial.pderiv s).restrictScalars ℤ)
  have hD' : ∀ s : Fin n, ∃ D : @Derivation ℤ B B _ _ _ (Ring.toIntAlgebra B) _ _, ∀ x,
      D (algebraMap S₀ B x) = algebraMap S₀ B (MvPolynomial.pderiv s x) := by
    intro s
    obtain ⟨D, hD⟩ := hD s
    exact ⟨@Derivation.mk ℤ B B _ _ _ (Ring.toIntAlgebra B) _ _ D.toLinearMap
      D.map_one_eq_zero' D.leibniz', hD⟩
  have h := GlobalTheory.T.regular_fibre_of_lifted_partialDerivations Λ (Fin n) B K hC hD'
  let e : B ⊗[R] K ≃ₐ[R] B ⊗[S₀] K := IsLocalization.algebraTensorEquiv P.primeCompl R B K
  exact IsRegularRing.of_ringEquiv e.symm.toRingEquiv

end GlobalTheory
