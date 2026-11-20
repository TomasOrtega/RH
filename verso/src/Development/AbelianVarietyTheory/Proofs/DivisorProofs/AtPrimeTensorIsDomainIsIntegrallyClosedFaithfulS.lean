import Mathlib
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Introduce `R A _ _ _ _ _ _ _ p _`. Use `set Rp := Localization.AtPrime p`. Use `set B := TensorProduct R Rp A`. Use `letI : Algebra A B := Algebra.TensorProduct.rightAlgebra`. Establish `hpush : Algebra.IsPushout R A Rp B` using `TensorProduct.isPushout'`.

Use `haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid A p.primeCompl) B := (Algebra.isLocalization_iff_isPushout p.primeCompl Rp).mpr hpush`. Establish `hinj : Function.Injective (algebraMap R A)` using `FaithfulSMul.algebraMap_injective R A`. Establish `hle : Algebra.algebraMapSubmonoid A p.primeCompl ≤ nonZeroDivisors A`. Introduce and unpack `_ ⟨r, hr, rfl⟩`. Use `mem_nonZeroDivisors_of_ne_zero ?_` and prove the remaining obligations.

Introduce `h0`. Apply `hr` to reduce the goal to its premises. Establish `: r = 0` using `hinj (by simpa using h0)`. Rewrite using `[this]`. Conclude with `p.zero_mem`.

Use `haveI hdom : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hle`. Use `⟨hdom, isIntegrallyClosed_of_isLocalization B _ hle, ?_⟩` and prove the remaining obligations. Establish `hAB : Function.Injective (algebraMap A B)` using `IsLocalization.injective B hle`. Use `(faithfulSMul_iff_algebraMap_injective Rp B).mpr ?_` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `x hx`. Take `⟨⟨r, s⟩, rfl⟩` from `IsLocalization.mk'_surjective p.primeCompl x`. Establish `hcomp : ∀ r : R, algebraMap Rp B (algebraMap R Rp r) = algebraMap A B (algebraMap R A r)`. Introduce `r`. Rewrite using `[← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`.

Establish `h1 : algebraMap Rp B (algebraMap R Rp r) = 0`. Use `congrArg (algebraMap Rp B) (IsLocalization.mk'_spec Rp r s)` as an intermediate fact. Rewrite `this` using `[map_mul, hx, zero_mul]`. Conclude with `this.symm`. Rewrite `h1` using `[hcomp]`.

Establish `hr : r = 0` using `hinj ((hAB (h1.trans (map_zero _).symm)).trans (map_zero _).symm)`. Simplify using `[hr]`.
-/
theorem atPrime_tensor_isDomain_isIntegrallyClosed_faithfulSMul : ∀ (R A : Type) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [FaithfulSMul R A] (p : Ideal R) [p.IsPrime], IsDomain (TensorProduct R (Localization.AtPrime p) A) ∧ IsIntegrallyClosed (TensorProduct R (Localization.AtPrime p) A) ∧ FaithfulSMul (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A) := by
  intro R A _ _ _ _ _ _ _ p _
  set Rp := Localization.AtPrime p
  set B := TensorProduct R Rp A
  letI : Algebra A B := Algebra.TensorProduct.rightAlgebra
  have hpush : Algebra.IsPushout R A Rp B := TensorProduct.isPushout'
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid A p.primeCompl) B :=
    (Algebra.isLocalization_iff_isPushout p.primeCompl Rp).mpr hpush
  have hinj : Function.Injective (algebraMap R A) := FaithfulSMul.algebraMap_injective R A
  have hle : Algebra.algebraMapSubmonoid A p.primeCompl ≤ nonZeroDivisors A := by
    rintro _ ⟨r, hr, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    apply hr
    have : r = 0 := hinj (by simpa using h0)
    rw [this]; exact p.zero_mem
  haveI hdom : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hle
  refine ⟨hdom, isIntegrallyClosed_of_isLocalization B _ hle, ?_⟩
  have hAB : Function.Injective (algebraMap A B) := IsLocalization.injective B hle
  refine (faithfulSMul_iff_algebraMap_injective Rp B).mpr ?_
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
  have hcomp : ∀ r : R, algebraMap Rp B (algebraMap R Rp r) = algebraMap A B (algebraMap R A r) := by
    intro r
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have h1 : algebraMap Rp B (algebraMap R Rp r) = 0 := by
    have := congrArg (algebraMap Rp B) (IsLocalization.mk'_spec Rp r s)
    rw [map_mul, hx, zero_mul] at this
    exact this.symm
  rw [hcomp] at h1
  have hr : r = 0 := hinj ((hAB (h1.trans (map_zero _).symm)).trans (map_zero _).symm)
  simp [hr]

end GlobalTheory
