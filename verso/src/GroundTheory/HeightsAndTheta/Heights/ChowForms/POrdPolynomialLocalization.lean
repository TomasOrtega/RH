import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial IsLocalRing

/- English proof (translation)
Use extensionality with `r`. Rewrite using `[Ideal.mem_comap, MvPolynomial.mem_map_C_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Simplify using `using h 0`.

Introduce `h m`. Rewrite using `[coeff_C]`. Use `split_ifs`. Conclude with `h`. Conclude with `p.zero_mem`.
-/
theorem OrdPolynomialLocalization.comap_C_map_C {R : Type*} [CommRing R] (σ : Type*) (p : Ideal R) :
    Ideal.comap (C : R →+* MvPolynomial σ R) (Ideal.map (C : R →+* MvPolynomial σ R) p) = p := by
  classical
  ext r
  rw [Ideal.mem_comap, MvPolynomial.mem_map_C_iff]
  constructor
  · intro h
    simpa using h 0
  · intro h m
    rw [coeff_C]
    split_ifs
    · exact h
    · exact p.zero_mem

/- English proof (translation)
Introduce `R _ σ p _ _ x`. Use `set P := Ideal.map (C : R →+* MvPolynomial σ R) p with hPdef`. Establish `: P.LiesOver p` using `⟨by`. Rewrite using `[Ideal.under, MvPolynomial.algebraMap_eq, hPdef]`. Conclude with `(OrdPolynomialLocalization.comap_C_map_C σ p).symm⟩`.

Set `` to `Localization.AtPrime.algebraOfLiesOver p P`. Use `set A := Localization.AtPrime p`. Use `set B := Localization.AtPrime P`. Establish `: IsLocalHom (algebraMap A B)` using `inferInstanceAs (IsLocalHom (Localization.localRingHom p P (algebraMap R (MvPolynomial σ R)) Ideal.LiesOver.over))`. Establish `hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B`.

Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R (MvPolynomial σ R) B, ← Ideal.map_map, MvPolynomial.algebraMap_eq, ← hPdef, Localization.AtPrime.map_eq_maximalIdeal]`. Establish `h1 : Module.length B (B ⧸ maximalIdeal B) = 1`. Establish `: IsSimpleModule B (B ⧸ maximalIdeal B)` using `isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal B, ⟨LinearEquiv.refl _ _⟩⟩`. Conclude with `Module.length_eq_one _ _`. Establish `key` using `IsLocalRing.length_baseChange A B (A ⧸ Ideal.span {algebraMap R A x})`.

Rewrite `key` using `[hm, h1, mul_one, ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (Ideal.span {algebraMap R A x})).toLinearEquiv.length_eq, Ideal.map_span, Set.image_singleton, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R (MvPolynomial σ R) B, MvPolynomial.algebraMap …`. Conclude with `key`.
-/
theorem OrdPolynomialLocalization.proof : OrdPolynomialLocalization.Statement := by
  intro R _ σ p _ _ x
  set P := Ideal.map (C : R →+* MvPolynomial σ R) p with hPdef
  have : P.LiesOver p := ⟨by
    rw [Ideal.under, MvPolynomial.algebraMap_eq, hPdef]
    exact (OrdPolynomialLocalization.comap_C_map_C σ p).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p P
  set A := Localization.AtPrime p
  set B := Localization.AtPrime P
  have : IsLocalHom (algebraMap A B) :=
    inferInstanceAs (IsLocalHom (Localization.localRingHom p P (algebraMap R (MvPolynomial σ R))
      Ideal.LiesOver.over))
  have hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq R (MvPolynomial σ R) B, ← Ideal.map_map, MvPolynomial.algebraMap_eq,
      ← hPdef, Localization.AtPrime.map_eq_maximalIdeal]
  have h1 : Module.length B (B ⧸ maximalIdeal B) = 1 := by
    have : IsSimpleModule B (B ⧸ maximalIdeal B) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal B, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _
  have key := IsLocalRing.length_baseChange A B (A ⧸ Ideal.span {algebraMap R A x})
  rw [hm, h1, mul_one, ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
    (Ideal.span {algebraMap R A x})).toLinearEquiv.length_eq, Ideal.map_span,
    Set.image_singleton, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply R (MvPolynomial σ R) B, MvPolynomial.algebraMap_eq] at key
  exact key

end GroundTheory.Heights₂.Heights
