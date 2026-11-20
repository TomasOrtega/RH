import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ThetaQuasiPeriods.Change

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

/- English proof (translation)
Use `letI : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra`. Use `haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Set `L` to `FractionRing B`. Use `haveI : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq fun r => by`. Rewrite using `[IsScalarTower.algebraMap_apply R B L, IsScalarTower.algebraMap_apply A B L]`.

Both sides reduce to the same expression. Establish `hAB : Function.Injective (algebraMap A B)` using `FaithfulSMul.algebraMap_injective A B`. Establish `hBL : Function.Injective (algebraMap B L)` using `IsFractionRing.injective B L`. Establish `hAL : Function.Injective (algebraMap A L)`. Rewrite using `[IsScalarTower.algebraMap_eq A B L]`.

Conclude with `hBL.comp hAB`. Use `haveI : IsFractionRing A L := by`. Use `⟨⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `y`. Conclude with `IsUnit.mk0 _ ((map_ne_zero_iff _ hAL).mpr (nonZeroDivisors.ne_zero y.2))`.

Introduce `z`. Take `⟨⟨x, y⟩, hz⟩` from `IsLocalization.surj (nonZeroDivisors B) z`. Take `⟨a₁, c₁, hc₁, h₁⟩` from `hb x`. Take `⟨a₂, c₂, hc₂, h₂⟩` from `hb (y : B)`. Establish `hy : (y : B) ≠ 0` using `nonZeroDivisors.ne_zero y.2`.

Establish `ha₂ : a₂ ≠ 0`. Introduce `h0`. Rewrite `h₂` using `[h0, map_zero]`. Conclude with `mul_ne_zero ((map_ne_zero_iff _ hAB).mpr hc₂) hy h₂`. Use `⟨⟨a₁ * c₂, ⟨c₁ * a₂, mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hc₁ ha₂)⟩⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [IsScalarTower.algebraMap_apply A B L, map_mul, ← h₁, ← h₂]`. Simplify using `only [map_mul] at hz ⊢`. Rewrite using `[← hz]`. Expand and normalize the polynomial expressions, which then agree. Introduce `x y hxy`.

Conclude with `⟨1, by rw [hAL hxy]⟩`. Use `haveI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr (by`. Rewrite using `[IsScalarTower.algebraMap_eq R A L]`. Conclude with `hAL.comp (FaithfulSMul.algebraMap_injective R A))`. Set `K` to `FractionRing R`.

Use `letI : Algebra K L := FractionRing.liftAlgebra R L`. Use `haveI : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L`. Use `haveI : Module.Finite K L := Module.Finite.of_isLocalization R A (nonZeroDivisors R)`. Use `haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)`. Use `haveI : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField`.

Use `haveI : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L _`. Use `haveI : Algebra.IsIntegral R B := Algebra.IsIntegral.trans A`. Set `f : B →ₐ[R] integralClosure R L` to `(IsScalarTower.toAlgHom R B L).codRestrict (integralClosure R L) (fun b => (Algebra.IsIntegral.isIntegral (R := R) b).map (IsScalarTower.toAlgHom R B L))`. Establish `hf : Function.Injective f.toLinearMap` using `fun x y h => hBL (congrArg Subtype.val h)`. Use `haveI : IsNoetherian R (integralClosure R L) := isNoetherian_of_isNoetherianRing_of_finite _ _`.

Use `haveI : IsNoetherian R B := isNoetherian_of_injective f.toLinearMap hf`. Use `haveI : Module.Finite R B := Module.IsNoetherian.finite R B`. Conclude with `Module.Finite.of_restrictScalars_finite R A B`.
-/
theorem finite_of_isIntegral_of_birational_of_finite_over_normal
    (R A B : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    [CharZero R] [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra R A] [FaithfulSMul R A] [Module.Finite R A]
    [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (hb : ∀ b : B, ∃ a a' : A, a' ≠ 0 ∧ algebraMap A B a' * b = algebraMap A B a) :
    Module.Finite A B := by
  letI : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let L := FractionRing B
  haveI : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R B L, IsScalarTower.algebraMap_apply A B L]; rfl
  have hAB : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hBL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A B L]; exact hBL.comp hAB

  haveI : IsFractionRing A L := by
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · intro y
      exact IsUnit.mk0 _ ((map_ne_zero_iff _ hAL).mpr (nonZeroDivisors.ne_zero y.2))
    · intro z
      obtain ⟨⟨x, y⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors B) z
      obtain ⟨a₁, c₁, hc₁, h₁⟩ := hb x
      obtain ⟨a₂, c₂, hc₂, h₂⟩ := hb (y : B)
      have hy : (y : B) ≠ 0 := nonZeroDivisors.ne_zero y.2
      have ha₂ : a₂ ≠ 0 := by
        intro h0
        rw [h0, map_zero] at h₂
        exact mul_ne_zero ((map_ne_zero_iff _ hAB).mpr hc₂) hy h₂
      refine ⟨⟨a₁ * c₂, ⟨c₁ * a₂, mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hc₁ ha₂)⟩⟩, ?_⟩
      simp only [IsScalarTower.algebraMap_apply A B L, map_mul, ← h₁, ← h₂]
      simp only [map_mul] at hz ⊢
      rw [← hz]; ring
    · intro x y hxy
      exact ⟨1, by rw [hAL hxy]⟩
  haveI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr (by
    rw [IsScalarTower.algebraMap_eq R A L]
    exact hAL.comp (FaithfulSMul.algebraMap_injective R A))
  let K := FractionRing R
  letI : Algebra K L := FractionRing.liftAlgebra R L
  haveI : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  haveI : Module.Finite K L := Module.Finite.of_isLocalization R A (nonZeroDivisors R)
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  haveI : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L _
  haveI : Algebra.IsIntegral R B := Algebra.IsIntegral.trans A
  let f : B →ₐ[R] integralClosure R L :=
    (IsScalarTower.toAlgHom R B L).codRestrict (integralClosure R L)
      (fun b => (Algebra.IsIntegral.isIntegral (R := R) b).map (IsScalarTower.toAlgHom R B L))
  have hf : Function.Injective f.toLinearMap := fun x y h =>
    hBL (congrArg Subtype.val h)
  haveI : IsNoetherian R (integralClosure R L) := isNoetherian_of_isNoetherianRing_of_finite _ _
  haveI : IsNoetherian R B := isNoetherian_of_injective f.toLinearMap hf
  haveI : Module.Finite R B := Module.IsNoetherian.finite R B
  exact Module.Finite.of_restrictScalars_finite R A B

/- English proof (translation)
Take `⟨d, g, hg, hfin⟩` from `exists_finite_inj_algHom_of_fg ℂ A`. Use `letI : Algebra (MvPolynomial (Fin d) ℂ) A := g.toRingHom.toAlgebra`. Use `haveI : FaithfulSMul (MvPolynomial (Fin d) ℂ) A := (faithfulSMul_iff_algebraMap_injective _ A).mpr hg`. Use `haveI : Module.Finite (MvPolynomial (Fin d) ℂ) A := hfin`. Conclude with `finite_of_isIntegral_of_birational_of_finite_over_normal (MvPolynomial (Fin d) ℂ) A B hb`.
-/
theorem finite_of_isIntegral_of_birational_complex
    (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (hb : ∀ b : B, ∃ a a' : A, a' ≠ 0 ∧ algebraMap A B a' * b = algebraMap A B a) :
    Module.Finite A B := by
  obtain ⟨d, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ A
  letI : Algebra (MvPolynomial (Fin d) ℂ) A := g.toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial (Fin d) ℂ) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hg
  haveI : Module.Finite (MvPolynomial (Fin d) ℂ) A := hfin
  exact finite_of_isIntegral_of_birational_of_finite_over_normal (MvPolynomial (Fin d) ℂ) A B hb

/- English proof (translation)
Introduce `_ A B _ _ _ _ _ _ _ _ _ hb`. Conclude with `finite_of_isIntegral_of_birational_complex A B hb`.
-/
theorem finite_of_isIntegral_of_birational_of_presentation :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p, p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a) → (∀ (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra ℂ A] [Algebra.FiniteType ℂ A] [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B], (∀ b : B, ∃ a a' : A, a' ≠ 0 ∧ algebraMap A B a' * b = algebraMap A B a) → Module.Finite A B) := by
  intro _ A B _ _ _ _ _ _ _ _ _ hb
  exact finite_of_isIntegral_of_birational_complex A B hb

end GlobalTheory
