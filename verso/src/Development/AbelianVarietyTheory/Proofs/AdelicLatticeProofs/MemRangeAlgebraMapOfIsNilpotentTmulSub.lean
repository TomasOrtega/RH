import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Use `letI : Field (A ⧸ m) := Ideal.Quotient.field m`. Use `haveI : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)`. Set `ι : (A ⧸ m) →ₐ[K] AlgebraicClosure K` to `IsAlgClosed.lift`. Use `⟨ι.comp (Ideal.Quotient.mkₐ K m), fun x hx => ?_⟩` and prove the remaining obligations. Establish `h : ι (Ideal.Quotient.mk m x) = 0` using `hx`.

Establish `h2 : Ideal.Quotient.mk m x = 0` using `ι.toRingHom.injective (by simpa using h)`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp h2`.
-/
theorem exists_algHom_algebraicClosure_ker_le (K A : Type) [Field K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] :
    ∃ φ : A →ₐ[K] AlgebraicClosure K, ∀ x, φ x = 0 → x ∈ m := by
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  let ι : (A ⧸ m) →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  refine ⟨ι.comp (Ideal.Quotient.mkₐ K m), fun x hx => ?_⟩
  have h : ι (Ideal.Quotient.mk m x) = 0 := hx
  have h2 : Ideal.Quotient.mk m x = 0 := ι.toRingHom.injective (by simpa using h)
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

/- English proof (translation)
Break down `subsingleton_or_nontrivial A with hA | hA` into its components or cases. Conclude with `⟨0, Subsingleton.elim _ _⟩`. Establish `h1 : ∀ φ ψ : A →ₐ[K] AlgebraicClosure K, φ f = ψ f`. Introduce `φ ψ`. Establish `h` using `(hf.map (Algebra.TensorProduct.productMap φ ψ)).eq_zero`.

Simplify `h` using `[sub_eq_zero]`. Take `⟨m₀, hm₀⟩` from `Ideal.exists_maximal A`. Take `⟨φ₀, -⟩` from `exists_algHom_algebraicClosure_ker_le K A m₀`. Establish `h2 : φ₀ f ∈ Set.range (algebraMap K (AlgebraicClosure K))`. Rewrite using `[InfiniteGalois.mem_range_algebraMap_iff_fixed]`.

Introduce `σ`. Conclude with `h1 (σ.toAlgHom.comp φ₀) φ₀`. Take `⟨c, hc⟩` from `h2`. Use `haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Establish `h3 : f - algebraMap K A c ∈ (⊥ : Ideal A).jacobson`. Rewrite using `[Ideal.jacobson, Submodule.mem_sInf]`. Introduce and unpack `m ⟨-, hm⟩`. Take `⟨φ, hφ⟩` from `exists_algHom_algebraicClosure_ker_le K A m`. Apply `hφ` to reduce the goal to its premises.

Rewrite using `[map_sub, AlgHom.commutes, hc, h1 φ φ₀, sub_self]`. Establish `h4 : (⊥ : Ideal A).jacobson = ⊥` using `IsJacobsonRing.out inferInstance (Ideal.isRadical_bot)`. Rewrite `h3` using `[h4, Ideal.mem_bot, sub_eq_zero]`. Conclude with `h3.symm`.
-/
theorem mem_range_algebraMap_of_isNilpotent_tmul_sub (K A : Type) [Field K] [CharZero K]
    [CommRing A] [Algebra K A] [Algebra.FiniteType K A] [IsReduced A] (f : A)
    (hf : IsNilpotent (f ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] f)) : f ∈ (algebraMap K A).range := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, Subsingleton.elim _ _⟩
  have h1 : ∀ φ ψ : A →ₐ[K] AlgebraicClosure K, φ f = ψ f := by
    intro φ ψ
    have h := (hf.map (Algebra.TensorProduct.productMap φ ψ)).eq_zero
    simpa [sub_eq_zero] using h
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal A
  obtain ⟨φ₀, -⟩ := exists_algHom_algebraicClosure_ker_le K A m₀
  have h2 : φ₀ f ∈ Set.range (algebraMap K (AlgebraicClosure K)) := by
    rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
    intro σ
    exact h1 (σ.toAlgHom.comp φ₀) φ₀
  obtain ⟨c, hc⟩ := h2
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  refine ⟨c, ?_⟩
  have h3 : f - algebraMap K A c ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro m ⟨-, hm⟩
    obtain ⟨φ, hφ⟩ := exists_algHom_algebraicClosure_ker_le K A m
    apply hφ
    rw [map_sub, AlgHom.commutes, hc, h1 φ φ₀, sub_self]
  have h4 : (⊥ : Ideal A).jacobson = ⊥ :=
    IsJacobsonRing.out inferInstance (Ideal.isRadical_bot)
  rw [h4, Ideal.mem_bot, sub_eq_zero] at h3
  exact h3.symm

end GlobalTheory.ClassFin
