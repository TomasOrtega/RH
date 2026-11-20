import Mathlib
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Introduce `R A _ _ _ _ _ p _ H q _ hq`. Use `set P : Ideal R := q.comap (algebraMap R (Localization.AtPrime p)) with hPdef`. Use `haveI : P.IsPrime := Ideal.comap_isPrime _ _`. Establish `hP : P.height = 1`. Rewrite using `[← hq, ← IsLocalization.height_comap p.primeCompl q]`.

Use `haveI := H P hP`. Use `haveI : IsLocalization.AtPrime (Localization.AtPrime q) P := IsLocalization.isLocalization_atPrime_localization_atPrime p.primeCompl q`. Set `e : Localization.AtPrime P ≃ₐ[R] Localization.AtPrime q` to `IsLocalization.algEquiv P.primeCompl _ _`. Use `letI : Algebra (Localization.AtPrime P) (Localization.AtPrime q) := e.toRingHom.toAlgebra`. Use `haveI : IsScalarTower R (Localization.AtPrime P) (Localization.AtPrime q) := IsScalarTower.of_algebraMap_eq (fun r => (e.commutes r).symm)`.

Use `haveI : Algebra.Etale (Localization.AtPrime q) (TensorProduct (Localization.AtPrime P) (Localization.AtPrime q) (TensorProduct R (Localization.AtPrime P) A)) := Algebra.Etale.baseChange _ _ _`. Set `e1` to `Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime P) (Localization.AtPrime q) (Localization.AtPrime q) A`. Set `e2` to `Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime p) (Localization.AtPrime q) (Localization.AtPrime q) A`. Conclude with `Algebra.Etale.of_equiv (e1.trans e2.symm)`.
-/
theorem etale_localization_atPrime_of_height_one :
    ∀ (R A : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [Algebra R A]
      (p : Ideal R) [p.IsPrime],
      (∀ (P : Ideal R) [P.IsPrime], P.height = 1 →
        Algebra.Etale (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) A)) →
      ∀ (q : Ideal (Localization.AtPrime p)) [q.IsPrime], q.height = 1 →
        Algebra.Etale (Localization.AtPrime q)
          (TensorProduct (Localization.AtPrime p) (Localization.AtPrime q)
            (TensorProduct R (Localization.AtPrime p) A)) := by
  intro R A _ _ _ _ _ p _ H q _ hq
  set P : Ideal R := q.comap (algebraMap R (Localization.AtPrime p)) with hPdef
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hP : P.height = 1 := by
    rw [← hq, ← IsLocalization.height_comap p.primeCompl q]
  haveI := H P hP
  haveI : IsLocalization.AtPrime (Localization.AtPrime q) P :=
    IsLocalization.isLocalization_atPrime_localization_atPrime p.primeCompl q
  let e : Localization.AtPrime P ≃ₐ[R] Localization.AtPrime q :=
    IsLocalization.algEquiv P.primeCompl _ _
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime q) := e.toRingHom.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime P) (Localization.AtPrime q) :=
    IsScalarTower.of_algebraMap_eq (fun r => (e.commutes r).symm)
  haveI : Algebra.Etale (Localization.AtPrime q)
      (TensorProduct (Localization.AtPrime P) (Localization.AtPrime q)
        (TensorProduct R (Localization.AtPrime P) A)) :=
    Algebra.Etale.baseChange _ _ _
  let e1 := Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime P)
    (Localization.AtPrime q) (Localization.AtPrime q) A
  let e2 := Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime p)
    (Localization.AtPrime q) (Localization.AtPrime q) A
  exact Algebra.Etale.of_equiv (e1.trans e2.symm)

end GlobalTheory
