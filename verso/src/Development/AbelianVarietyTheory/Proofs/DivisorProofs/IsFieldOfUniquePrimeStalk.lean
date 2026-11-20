import Mathlib
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory

/- English proof (translation)
Introduce `R q huniq hfield`. Use `letI : Algebra R ((Spec R).presheaf.stalk q) := StructureSheaf.stalkAlgebra R q`. Use `haveI : q.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := R) q`. Use `haveI hloc : IsLocalization.AtPrime ((Spec R).presheaf.stalk q) q.asIdeal := StructureSheaf.IsLocalization.to_stalk R q`. Establish `hunit : ∀ x : R, x ∉ q.asIdeal → IsUnit x`.

Introduce `x hx`. Assume the negation of the conclusion as `hxu`. Take `⟨m, hm, hxm⟩` from `exists_max_ideal_of_mem_nonunits hxu`. Establish `h1 : ((⟨m, hm.isPrime⟩ : PrimeSpectrum R) : Spec R) = q` using `huniq _`. Establish `hmq : m = q.asIdeal`.

Rewrite using `[← h1]`. Conclude with `hx (hmq ▸ hxm)`. Set `e : R ≃ₐ[R] ((Spec R).presheaf.stalk q)` to `IsLocalization.atUnits R q.asIdeal.primeCompl (S := (Spec R).presheaf.stalk q) (fun y hy => (IsUnit.mem_submonoid_iff y).2 (hunit y hy))`. Conclude with `MulEquiv.isField hfield e.toMulEquiv`.
-/
theorem isField_of_spec_singleton_stalk_isField :
    ∀ (R : CommRingCat.{0}) (q : Spec R), (∀ q' : Spec R, q' = q) →
      IsField ((Spec R).presheaf.stalk q) → IsField R := by
  intro R q huniq hfield
  letI : Algebra R ((Spec R).presheaf.stalk q) := StructureSheaf.stalkAlgebra R q
  haveI : q.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := R) q
  haveI hloc : IsLocalization.AtPrime ((Spec R).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R q
  have hunit : ∀ x : R, x ∉ q.asIdeal → IsUnit x := by
    intro x hx
    by_contra hxu
    obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits hxu
    have h1 : ((⟨m, hm.isPrime⟩ : PrimeSpectrum R) : Spec R) = q := huniq _
    have hmq : m = q.asIdeal := by
      rw [← h1]
    exact hx (hmq ▸ hxm)
  let e : R ≃ₐ[R] ((Spec R).presheaf.stalk q) :=
    IsLocalization.atUnits R q.asIdeal.primeCompl (S := (Spec R).presheaf.stalk q)
      (fun y hy => (IsUnit.mem_submonoid_iff y).2 (hunit y hy))
  exact MulEquiv.isField hfield e.toMulEquiv

end GlobalTheory
