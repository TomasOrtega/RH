import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Establish `hJ : IsJacobsonRing T` using `isJacobsonRing_of_finiteType (A := ℂ)`. Establish `h1 : x ∈ Ideal.jacobson (⊥ : Ideal T)`. Rewrite using `[Ideal.jacobson, Ideal.mem_sInf]`. Introduce and unpack `m ⟨-, hm⟩`. Set `` to `Ideal.Quotient.field m`.

Establish `hfin : Module.Finite ℂ (T ⧸ m)` using `finite_of_finite_type_of_isJacobsonRing ℂ (T ⧸ m)`. Establish `hb : Function.Bijective (algebraMap ℂ (T ⧸ m))` using `IsAlgClosed.algebraMap_bijective_of_isIntegral`. Set `e : ℂ ≃ₐ[ℂ] (T ⧸ m)` to `AlgEquiv.ofBijective (Algebra.ofId ℂ (T ⧸ m)) hb`. Use `h ((e.symm : (T ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m))` as an intermediate fact. Establish `h0 : e.symm (Ideal.Quotient.mk m x) = 0` using `this`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp ((map_eq_zero_iff _ e.symm.injective).mp h0)`. Establish `h2 : x ∈ Ideal.radical (⊥ : Ideal T)`. Use `IsJacobsonRing.out hJ (Ideal.radical_isRadical (⊥ : Ideal T))` as an intermediate fact. Rewrite using `[← this]`. Conclude with `Ideal.jacobson_mono Ideal.le_radical h1`.

Conclude with `h2`.
-/
theorem isNilpotent_of_forall_algHom_eq_zero (T : Type) [CommRing T] [Algebra ℂ T]
    [Algebra.FiniteType ℂ T] (x : T) (h : ∀ ω : T →ₐ[ℂ] ℂ, ω x = 0) : IsNilpotent x := by
  have hJ : IsJacobsonRing T := isJacobsonRing_of_finiteType (A := ℂ)
  have h1 : x ∈ Ideal.jacobson (⊥ : Ideal T) := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    let := Ideal.Quotient.field m
    have hfin : Module.Finite ℂ (T ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (T ⧸ m)
    have hb : Function.Bijective (algebraMap ℂ (T ⧸ m)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e : ℂ ≃ₐ[ℂ] (T ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId ℂ (T ⧸ m)) hb
    have := h ((e.symm : (T ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m))
    have h0 : e.symm (Ideal.Quotient.mk m x) = 0 := this
    exact Ideal.Quotient.eq_zero_iff_mem.mp ((map_eq_zero_iff _ e.symm.injective).mp h0)
  have h2 : x ∈ Ideal.radical (⊥ : Ideal T) := by
    have := IsJacobsonRing.out hJ (Ideal.radical_isRadical (⊥ : Ideal T))
    rw [← this]
    exact Ideal.jacobson_mono Ideal.le_radical h1
  exact h2

/- English proof (translation)
Introduce `B A _ _ _ _ _ _ _ f h`. Establish `: Algebra.FiniteType B A` using `Algebra.FiniteType.of_restrictScalars_finiteType ℂ B A`. Establish `: Algebra.FiniteType A (A ⊗[B] A)` using `inferInstance`. Establish `: Algebra.FiniteType ℂ (A ⊗[B] A)` using `Algebra.FiniteType.trans (S := A) inferInstance inferInstance`. Apply `isNilpotent_of_forall_algHom_eq_zero` to reduce the goal to its premises.

Introduce `ω`. Set `l : A →ₐ[ℂ] A ⊗[B] A` to `Algebra.TensorProduct.includeLeft`. Set `r : A →ₐ[ℂ] A ⊗[B] A` to `(Algebra.TensorProduct.includeRight : A →ₐ[B] A ⊗[B] A).restrictScalars ℂ`. Use `h (ω.comp l) (ω.comp r) (fun b => by` as an intermediate fact. Simplify using `only [AlgHom.comp_apply, l, r, Algebra.TensorProduct.includeLeft_apply, AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply]`.

Use `congr 1`. Rewrite using `[Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul])`. Rewrite using `[map_sub, sub_eq_zero]`. Conclude with `this`.
-/
theorem isNilpotent_tmul_sub_tmul_of_const_on_fibres :
    ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra ℂ B] [Algebra ℂ A] [Algebra B A] [IsScalarTower ℂ B A] [Algebra.FiniteType ℂ A] (f : A), (∀ χ χ' : A →ₐ[ℂ] ℂ, (∀ b : B, χ (algebraMap B A b) = χ' (algebraMap B A b)) → χ f = χ' f) → IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f) := by
  intro B A _ _ _ _ _ _ _ f h
  have : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType ℂ B A
  have : Algebra.FiniteType A (A ⊗[B] A) := inferInstance
  have : Algebra.FiniteType ℂ (A ⊗[B] A) := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  apply isNilpotent_of_forall_algHom_eq_zero
  intro ω
  let l : A →ₐ[ℂ] A ⊗[B] A := Algebra.TensorProduct.includeLeft
  let r : A →ₐ[ℂ] A ⊗[B] A :=
    (Algebra.TensorProduct.includeRight : A →ₐ[B] A ⊗[B] A).restrictScalars ℂ
  have := h (ω.comp l) (ω.comp r) (fun b => by
    simp only [AlgHom.comp_apply, l, r, Algebra.TensorProduct.includeLeft_apply,
      AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul])
  rw [map_sub, sub_eq_zero]
  exact this

end GlobalTheory.ClassFin
