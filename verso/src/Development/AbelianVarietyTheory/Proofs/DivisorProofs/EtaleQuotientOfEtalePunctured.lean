import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFree
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Introduce `R A _ _ _ _ f _ H P _ hP`. Use `set S := R ⧸ Ideal.span {f}`. Use `set T := Localization.AtPrime P`. Use `set p : Ideal R := P.comap (algebraMap R S) with hpdef`. Use `haveI : p.IsPrime := Ideal.comap_isPrime _ _`.

Establish `hp : p ≠ maximalIdeal R`. Introduce `h`. Apply `hP` to reduce the goal to its premises. Use `le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) ?_` and prove the remaining obligations. Introduce `x hx`.

Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Establish `hr : r ∈ maximalIdeal R`. Rewrite using `[mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Conclude with `(mem_maximalIdeal _).1 hx (hu.map _)`.

Rewrite `hr` using `[← h]`. Conclude with `hr`. Use `haveI := H p hp`. Set `φ : Localization.AtPrime p →+* T` to `Localization.localRingHom p P (algebraMap R S) rfl`. Use `letI : Algebra (Localization.AtPrime p) T := φ.toAlgebra`.

Use `haveI : IsScalarTower R (Localization.AtPrime p) T := IsScalarTower.of_algebraMap_eq (fun r => by show algebraMap R T r = φ (algebraMap R _ r)`. Rewrite using `[Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply R S T])`. Use `haveI : Algebra.Etale T (TensorProduct (Localization.AtPrime p) T (TensorProduct R (Localization.AtPrime p) A)) := Algebra.Etale.baseChange _ _ _`. Set `e1` to `Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime p) T T A`. Set `e2` to `Algebra.TensorProduct.cancelBaseChange R S T T A`.

Set `e3 : (A ⧸ (Ideal.span {f}).map (algebraMap R A)) ≃ₐ[S] TensorProduct R S A` to `AlgEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective (((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (Ideal.span {f})).restrictScalars R).trans (Algebra.TensorProduct.comm R A S))`. Set `e4 : TensorProduct S T (A ⧸ (Ideal.span {f}).map (algebraMap R A)) ≃ₐ[T] TensorProduct S T (TensorProduct R S A)` to `Algebra.TensorProduct.congr AlgEquiv.refl e3`. Conclude with `Algebra.Etale.of_equiv (e1.trans (e4.trans e2).symm)`.
-/
theorem etale_quotient_of_etale_punctured :
    ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A] (f : R)
      [IsLocalRing (R ⧸ Ideal.span {f})],
      (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
        Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) →
      ∀ (P : Ideal (R ⧸ Ideal.span {f})) [P.IsPrime], P ≠ maximalIdeal (R ⧸ Ideal.span {f}) →
        Algebra.Etale (Localization.AtPrime P)
          (TensorProduct (R ⧸ Ideal.span {f}) (Localization.AtPrime P)
            (A ⧸ (Ideal.span {f}).map (algebraMap R A))) := by
  intro R A _ _ _ _ f _ H P _ hP
  set S := R ⧸ Ideal.span {f}
  set T := Localization.AtPrime P
  set p : Ideal R := P.comap (algebraMap R S) with hpdef
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  have hp : p ≠ maximalIdeal R := by
    intro h
    apply hP
    refine le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) ?_
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hr : r ∈ maximalIdeal R := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (mem_maximalIdeal _).1 hx (hu.map _)
    rw [← h] at hr
    exact hr
  haveI := H p hp
  let φ : Localization.AtPrime p →+* T := Localization.localRingHom p P (algebraMap R S) rfl
  letI : Algebra (Localization.AtPrime p) T := φ.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime p) T :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      show algebraMap R T r = φ (algebraMap R _ r)
      rw [Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply R S T])
  haveI : Algebra.Etale T (TensorProduct (Localization.AtPrime p) T
      (TensorProduct R (Localization.AtPrime p) A)) :=
    Algebra.Etale.baseChange _ _ _
  let e1 := Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime p) T T A
  let e2 := Algebra.TensorProduct.cancelBaseChange R S T T A
  let e3 : (A ⧸ (Ideal.span {f}).map (algebraMap R A)) ≃ₐ[S] TensorProduct R S A :=
    AlgEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      (((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (Ideal.span {f})).restrictScalars R).trans
        (Algebra.TensorProduct.comm R A S))
  let e4 : TensorProduct S T (A ⧸ (Ideal.span {f}).map (algebraMap R A)) ≃ₐ[T]
      TensorProduct S T (TensorProduct R S A) :=
    Algebra.TensorProduct.congr AlgEquiv.refl e3
  exact Algebra.Etale.of_equiv (e1.trans (e4.trans e2).symm)

end GlobalTheory
