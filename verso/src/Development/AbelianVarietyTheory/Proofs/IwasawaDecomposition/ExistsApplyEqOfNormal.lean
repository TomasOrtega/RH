import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.RayMono

/- English proof (translation)
Set `_` to `j.toRingHom.toAlgebra`. Establish `: IsScalarTower K A Ω` using `IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm`. Conclude with `⟨i.restrictNormal A x, i.restrictNormal_commutes A x⟩`.
-/
theorem exists_apply_eq_of_normal {K A Ω : Type} [Field K] [Field A] [Field Ω] [Algebra K A] [Algebra K Ω]
    [Normal K A] (i j : A →ₐ[K] Ω) (x : A) : ∃ y, j y = i x := by
  let _ := j.toRingHom.toAlgebra
  have : IsScalarTower K A Ω := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  exact ⟨i.restrictNormal A x, i.restrictNormal_commutes A x⟩

/- English proof (translation)
Introduce and unpack `E _ _ φ 𝔪 𝔪' M M' hn hd ⟨h, _, hM⟩ ⟨h', _, hM'⟩ z hz`. Set `_` to `algOf φ M h`. Set `_` to `algOf φ M' h'`. Set `_` to `φ.toAlgebra`. Use `hM.1` as an intermediate fact.

Use `hM'.1` as an intermediate fact. Take `⟨f⟩` from `nonempty_algHom_of_isRay_of_dvd hn hd hM'.2 hM.2`. Set `i : M →ₐ[E] ℂ` to `{ M.val.toRingHom with commutes' := fun _ => rfl }`. Set `i' : M' →ₐ[E] ℂ` to `{ M'.val.toRingHom with commutes' := fun _ => rfl }`. Take `⟨y, hy⟩` from `exists_apply_eq_of_normal i (i'.comp f) ⟨z, hz⟩`.

Establish `hy' : ((f y : M') : ℂ) = z` using `hy`. Conclude with `hy' ▸ (f y).2`.
-/
theorem le_of_isRayFieldIn_of_dvd : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (𝔪 𝔪' : Ideal (𝓞 E))
    (M M' : IntermediateField ℚ ℂ), 𝔪' ≠ ⊥ → 𝔪 ∣ 𝔪' → IsRayFieldIn φ 𝔪 M → IsRayFieldIn φ 𝔪' M' → M ≤ M' := by
  rintro E _ _ φ 𝔪 𝔪' M M' hn hd ⟨h, _, hM⟩ ⟨h', _, hM'⟩ z hz
  let _ := algOf φ M h
  let _ := algOf φ M' h'
  let _ := φ.toAlgebra
  have := hM.1
  have := hM'.1
  obtain ⟨f⟩ := nonempty_algHom_of_isRay_of_dvd hn hd hM'.2 hM.2
  let i : M →ₐ[E] ℂ := { M.val.toRingHom with commutes' := fun _ => rfl }
  let i' : M' →ₐ[E] ℂ := { M'.val.toRingHom with commutes' := fun _ => rfl }
  obtain ⟨y, hy⟩ := exists_apply_eq_of_normal i (i'.comp f) ⟨z, hz⟩
  have hy' : ((f y : M') : ℂ) = z := hy
  exact hy' ▸ (f y).2

end GlobalTheory.Mem.RayMono
