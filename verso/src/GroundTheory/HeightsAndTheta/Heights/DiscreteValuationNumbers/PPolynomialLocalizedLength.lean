import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpHorizontalMult
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open IsLocalRing

universe u

/- English proof (translation)
Set `g` to `Submodule.toLocalizedQuotient' (Localization.AtPrime W) W.primeCompl (Algebra.linearMap A (Localization.AtPrime W)) K`. Set `e` to `(IsLocalizedModule.linearEquiv W.primeCompl g (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ K))).restrictScalars (Localization.AtPrime W)`. Establish `hK : Submodule.localized' (Localization.AtPrime W) W.primeCompl (Algebra.linearMap A (Localization.AtPrime W)) K = K.map (algebraMap A (Localization.AtPrime W))`. Rewrite using `[Submodule.localized'_eq_span]`. Both sides reduce to the same expression.

Rewrite using `[← e.length_eq]`. Conclude with `(Submodule.quotEquivOfEq _ _ hK).length_eq`.
-/
theorem length_localizedModule_quotient_eq {A : Type*} [CommRing A] (K W : Ideal A) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ K)) =
      Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W))) := by
  let g := Submodule.toLocalizedQuotient' (Localization.AtPrime W) W.primeCompl
    (Algebra.linearMap A (Localization.AtPrime W)) K
  let e := (IsLocalizedModule.linearEquiv W.primeCompl g
    (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ K))).restrictScalars (Localization.AtPrime W)
  have hK : Submodule.localized' (Localization.AtPrime W) W.primeCompl
      (Algebra.linearMap A (Localization.AtPrime W)) K = K.map (algebraMap A (Localization.AtPrime W)) := by
    rw [Submodule.localized'_eq_span]
    rfl
  rw [← e.length_eq]
  exact (Submodule.quotEquivOfEq _ _ hK).length_eq

/- English proof (translation)
Use extensionality with `r`. Rewrite using `[Ideal.mem_comap, Ideal.mem_map_C_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Simplify using `using h 0`.

Introduce `h n`. Rewrite using `[Polynomial.coeff_C]`. Use `split_ifs`. Conclude with `h`. Conclude with `p.zero_mem`.
-/
theorem comap_C_map_C_polynomial {R : Type*} [CommRing R] (p : Ideal R) :
    (p.map (Polynomial.C : R →+* Polynomial R)).comap (Polynomial.C : R →+* Polynomial R) = p := by
  ext r
  rw [Ideal.mem_comap, Ideal.mem_map_C_iff]
  constructor
  · intro h
    simpa using h 0
  · intro h n
    rw [Polynomial.coeff_C]
    split_ifs
    · exact h
    · exact p.zero_mem

/- English proof (translation)
Introduce `R _ q _ I`. Use `set Q := q.map (Polynomial.C : R →+* Polynomial R) with hQdef`. Establish `: Q.LiesOver q` using `⟨by`. Rewrite using `[Ideal.under, Polynomial.algebraMap_eq, hQdef]`. Conclude with `(comap_C_map_C_polynomial q).symm⟩`.

Set `` to `Localization.AtPrime.algebraOfLiesOver q Q`. Use `set A := Localization.AtPrime q`. Use `set B := Localization.AtPrime Q`. Establish `: IsLocalHom (algebraMap A B)` using `inferInstanceAs (IsLocalHom (Localization.localRingHom q Q (algebraMap R (Polynomial R)) Ideal.LiesOver.over))`. Establish `hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B`.

Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R (Polynomial R) B, ← Ideal.map_map, Polynomial.algebraMap_eq, ← hQdef, Localization.AtPrime.map_eq_maximalIdeal]`. Establish `h1 : Module.length B (B ⧸ maximalIdeal B) = 1`. Establish `: IsSimpleModule B (B ⧸ maximalIdeal B)` using `isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal B, ⟨LinearEquiv.refl _ _⟩⟩`. Conclude with `Module.length_eq_one _ _`. Establish `key` using `IsLocalRing.length_baseChange A B (A ⧸ I.map (algebraMap R A))`.

Rewrite `key` using `[hm, h1, mul_one, ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (I.map (algebraMap R A))).toLinearEquiv.length_eq, Ideal.map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R (Polynomial R) B, ← Ideal.map_map, Polynomial.algebraMap_eq]`. Rewrite using `[length_localizedModule_quotient_eq, length_localizedModule_quotient_eq]`. Conclude with `key`.
-/
theorem PolynomialLocalizedLength.full : PolynomialLocalizedLength.Statement.{u} := by
  intro R _ q _ I
  set Q := q.map (Polynomial.C : R →+* Polynomial R) with hQdef
  have : Q.LiesOver q := ⟨by
    rw [Ideal.under, Polynomial.algebraMap_eq, hQdef]
    exact (comap_C_map_C_polynomial q).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver q Q
  set A := Localization.AtPrime q
  set B := Localization.AtPrime Q
  have : IsLocalHom (algebraMap A B) :=
    inferInstanceAs (IsLocalHom (Localization.localRingHom q Q (algebraMap R (Polynomial R))
      Ideal.LiesOver.over))
  have hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq R (Polynomial R) B, ← Ideal.map_map, Polynomial.algebraMap_eq,
      ← hQdef, Localization.AtPrime.map_eq_maximalIdeal]
  have h1 : Module.length B (B ⧸ maximalIdeal B) = 1 := by
    have : IsSimpleModule B (B ⧸ maximalIdeal B) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal B, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _
  have key := IsLocalRing.length_baseChange A B (A ⧸ I.map (algebraMap R A))
  rw [hm, h1, mul_one, ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
    (I.map (algebraMap R A))).toLinearEquiv.length_eq, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
    IsScalarTower.algebraMap_eq R (Polynomial R) B, ← Ideal.map_map, Polynomial.algebraMap_eq] at key
  rw [length_localizedModule_quotient_eq, length_localizedModule_quotient_eq]
  exact key

end GroundTheory.Heights₂.Heights.NumbersDVR
