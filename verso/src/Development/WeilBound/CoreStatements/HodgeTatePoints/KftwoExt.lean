import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.CompletionDVR

noncomputable section

open IsLocalRing Formalism.L2.Pj

namespace PositivityTheory.HtPt.Kftwo

/- English proof (translation)
Take `⟨⟨hdom, hdvr⟩, hcpl, hinj, hloc, -⟩` from `ReciprocityTheory.CA.Pt.completionDVR W`. Use `haveI : CharZero (AdicCompletion (maximalIdeal W) W) := charZero_of_injective_algebraMap hinj`. Conclude with `⟨CDVR.mk (AdicCompletion (maximalIdeal W) W), algebraMap W (AdicCompletion (maximalIdeal W) W), hloc, hinj⟩`.
-/
theorem exists_completion (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W] :
    ∃ (T : CDVR) (g : W →+* T.V), IsLocalHom g ∧ Function.Injective g := by
  obtain ⟨⟨hdom, hdvr⟩, hcpl, hinj, hloc, -⟩ := ReciprocityTheory.CA.Pt.completionDVR W
  haveI : CharZero (AdicCompletion (maximalIdeal W) W) := charZero_of_injective_algebraMap hinj
  exact ⟨CDVR.mk (AdicCompletion (maximalIdeal W) W),
    algebraMap W (AdicCompletion (maximalIdeal W) W), hloc, hinj⟩

/- English proof (translation)
Establish `hker : RingHom.ker (algebraMap V A) ≤ maximalIdeal V`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).mp hinj]`. Conclude with `bot_le`. Take `⟨P, hPmax, hPc⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (maximalIdeal V) hker`. Use `haveI : P.IsPrime := hPmax.isPrime`.

Establish `hP0 : P ≠ ⊥`. Introduce and unpack `rfl`. Apply `IsDiscreteValuationRing.not_a_field V` to reduce the goal to its premises. Rewrite using `[← hPc, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj]`. Use `haveI : IsDomain (Localization.AtPrime P) := IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors P)`.

Use `haveI : IsDiscreteValuationRing (Localization.AtPrime P) := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP0 (Localization.AtPrime P)`. Establish `hAinj : Function.Injective (algebraMap A (Localization.AtPrime P))` using `IsLocalization.injective (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P)`. Use `haveI : CharZero (Localization.AtPrime P) := charZero_of_injective_algebraMap hAinj`. Take `⟨T, g0, hg0, hg0inj⟩` from `exists_completion (Localization.AtPrime P)`. Use `⟨T, g0.comp (algebraMap A (Localization.AtPrime P)), ⟨fun x hx => ?_⟩, hg0inj.comp hAinj⟩` and prove the remaining obligations.

Simplify using `only [RingHom.comp_apply] at hx`. Establish `h1 : IsUnit (algebraMap A (Localization.AtPrime P) (algebraMap V A x))` using `isUnit_of_map_unit g0 _ hx`. Rewrite `h1` using `[IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P]`. Assume the negation of the conclusion as `hxu`. Establish `hx' : x ∈ maximalIdeal V` using `hxu`.

Rewrite `hx'` using `[← hPc]`. Conclude with `h1 (Ideal.mem_comap.mp hx')`.
-/
theorem exists_cdvr_of_isIntegral {V A : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing A]
    [IsDedekindDomain A] [CharZero A] [Algebra V A] [Algebra.IsIntegral V A] (hinj : Function.Injective (algebraMap V A)) :
    ∃ (T : CDVR) (g : A →+* T.V), IsLocalHom (g.comp (algebraMap V A)) ∧ Function.Injective g := by
  have hker : RingHom.ker (algebraMap V A) ≤ maximalIdeal V := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  obtain ⟨P, hPmax, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (maximalIdeal V) hker
  haveI : P.IsPrime := hPmax.isPrime
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    apply IsDiscreteValuationRing.not_a_field V
    rw [← hPc, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj]
  haveI : IsDomain (Localization.AtPrime P) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors P)
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP0 (Localization.AtPrime P)
  have hAinj : Function.Injective (algebraMap A (Localization.AtPrime P)) :=
    IsLocalization.injective (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P)
  haveI : CharZero (Localization.AtPrime P) := charZero_of_injective_algebraMap hAinj
  obtain ⟨T, g0, hg0, hg0inj⟩ := exists_completion (Localization.AtPrime P)
  refine ⟨T, g0.comp (algebraMap A (Localization.AtPrime P)), ⟨fun x hx => ?_⟩, hg0inj.comp hAinj⟩
  simp only [RingHom.comp_apply] at hx
  have h1 : IsUnit (algebraMap A (Localization.AtPrime P) (algebraMap V A x)) := isUnit_of_map_unit g0 _ hx
  rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P] at h1
  by_contra hxu
  have hx' : x ∈ maximalIdeal V := hxu
  rw [← hPc] at hx'
  exact h1 (Ideal.mem_comap.mp hx')

/- English proof (translation)
Use `letI : Algebra V K' := ((algebraMap K K').comp (algebraMap V K)).toAlgebra`. Use `haveI : IsScalarTower V K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Use `haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective`. Use `haveI : IsDedekindDomain (integralClosure V K') := integralClosure.isDedekindDomain V K K'`. Use `haveI : IsFractionRing (integralClosure V K') K' := integralClosure.isFractionRing_of_finite_extension K K'`.

Use `haveI : CharZero (integralClosure V K') := ⟨fun m n h => Nat.cast_injective (R := K') (by simpa using congrArg (algebraMap (integralClosure V K') K') h)⟩`. Establish `hVK' : Function.Injective (algebraMap V K')` using `(algebraMap K K').injective.comp (IsFractionRing.injective V K)`. Establish `hinj : Function.Injective (algebraMap V (integralClosure V K'))`. Use `Function.Injective.of_comp (f := algebraMap (integralClosure V K') K') ?_` and prove the remaining obligations. Rewrite using `[← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]`.

Conclude with `hVK'`. Take `⟨T, g, hg, hginj⟩` from `exists_cdvr_of_isIntegral hinj`. Establish `hjinj : Function.Injective ((algebraMap T.V T.Fr).comp g)` using `(IsFractionRing.injective T.V T.Fr).comp hginj`. Use `⟨T, g.comp (algebraMap V (integralClosure V K')), IsFractionRing.lift (K := K') hjinj, hg, ?_⟩` and prove the remaining obligations. Use extensionality with `x`.

Simplify using `only [RingHom.comp_apply]`. Rewrite using `[← IsScalarTower.algebraMap_apply V K K', IsScalarTower.algebraMap_apply V (integralClosure V K') K', IsFractionRing.lift_algebraMap]`. Both sides reduce to the same expression.
-/
theorem exists_cdvr {V K K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [CharZero K]
    [Algebra V K] [IsFractionRing V K] [Field K'] [Algebra K K'] [FiniteDimensional K K'] :
    ∃ (T : CDVR) (g : V →+* T.V) (j : K' →+* T.Fr), IsLocalHom g ∧
      (algebraMap T.V T.Fr).comp g = (j.comp (algebraMap K K')).comp (algebraMap V K) := by
  letI : Algebra V K' := ((algebraMap K K').comp (algebraMap V K)).toAlgebra
  haveI : IsScalarTower V K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  haveI : IsDedekindDomain (integralClosure V K') := integralClosure.isDedekindDomain V K K'
  haveI : IsFractionRing (integralClosure V K') K' :=
    integralClosure.isFractionRing_of_finite_extension K K'
  haveI : CharZero (integralClosure V K') :=
    ⟨fun m n h => Nat.cast_injective (R := K')
      (by simpa using congrArg (algebraMap (integralClosure V K') K') h)⟩
  have hVK' : Function.Injective (algebraMap V K') :=
    (algebraMap K K').injective.comp (IsFractionRing.injective V K)
  have hinj : Function.Injective (algebraMap V (integralClosure V K')) := by
    refine Function.Injective.of_comp (f := algebraMap (integralClosure V K') K') ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact hVK'
  obtain ⟨T, g, hg, hginj⟩ := exists_cdvr_of_isIntegral hinj
  have hjinj : Function.Injective ((algebraMap T.V T.Fr).comp g) :=
    (IsFractionRing.injective T.V T.Fr).comp hginj
  refine ⟨T, g.comp (algebraMap V (integralClosure V K')),
    IsFractionRing.lift (K := K') hjinj, hg, ?_⟩
  ext x
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply V K K',
    IsScalarTower.algebraMap_apply V (integralClosure V K') K', IsFractionRing.lift_algebraMap]
  rfl

end PositivityTheory.HtPt.Kftwo
