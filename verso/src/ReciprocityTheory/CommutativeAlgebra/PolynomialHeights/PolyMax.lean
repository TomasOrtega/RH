import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim

namespace ReciprocityTheory.CA

open Polynomial IsLocalRing

variable {P : Type*} [CommRing P] [IsLocalRing P]

/- English proof (translation)
Use `letI : Field (P ⧸ maximalIdeal P) := Ideal.Quotient.field _`. Use `letI : Field (S ⧸ 𝔑) := Ideal.Quotient.field _`. Use `letI : Algebra (P ⧸ maximalIdeal P) (S ⧸ 𝔑) := (Ideal.quotientMap 𝔑 (algebraMap P S) h.ge).toAlgebra`. Use `haveI : IsScalarTower P (P ⧸ maximalIdeal P) (S ⧸ 𝔑) := by first`. Consider the case `exact IsScalarTower.of_algebraMap_eq (fun p => rfl)`.

Consider the case `exact IsScalarTower.of_algebraMap_eq (fun p => by simp [Ideal.quotientMap_mk])`. Use `haveI : Algebra.FiniteType P (S ⧸ 𝔑) := by first`. Consider the case `infer_instance`. Consider the case `exact Algebra.FiniteType.of_surjective inferInstance (Ideal.Quotient.mkₐ P 𝔑) (Ideal.Quotient.mkₐ_surjective P 𝔑)`. Use `haveI : Algebra.FiniteType (P ⧸ maximalIdeal P) (S ⧸ 𝔑) := Algebra.FiniteType.of_restrictScalars_finiteType P _ _`.

Use `haveI : Module.Finite (P ⧸ maximalIdeal P) (S ⧸ 𝔑) := finite_of_finite_type_of_isJacobsonRing _ _`. Use `haveI : Algebra.IsIntegral P (P ⧸ maximalIdeal P) := by first`. Consider the case `infer_instance`. Consider the case `exact Algebra.IsIntegral.of_surjective (Ideal.Quotient.mkₐ P (maximalIdeal P)) (Ideal.Quotient.mkₐ_surjective P _)`. Conclude with `Algebra.IsIntegral.trans (P ⧸ maximalIdeal P)`.
-/
theorem isIntegral_quotient_of_isMaximal_of_comap_eq {S : Type*} [CommRing S] [Algebra P S]
    [Algebra.FiniteType P S] (𝔑 : Ideal S) [𝔑.IsMaximal]
    (h : 𝔑.comap (algebraMap P S) = maximalIdeal P) : Algebra.IsIntegral P (S ⧸ 𝔑) := by
  classical
  letI : Field (P ⧸ maximalIdeal P) := Ideal.Quotient.field _
  letI : Field (S ⧸ 𝔑) := Ideal.Quotient.field _
  letI : Algebra (P ⧸ maximalIdeal P) (S ⧸ 𝔑) :=
    (Ideal.quotientMap 𝔑 (algebraMap P S) h.ge).toAlgebra
  haveI : IsScalarTower P (P ⧸ maximalIdeal P) (S ⧸ 𝔑) := by
    first
    | exact IsScalarTower.of_algebraMap_eq (fun p => rfl)
    | exact IsScalarTower.of_algebraMap_eq (fun p => by simp [Ideal.quotientMap_mk])
  haveI : Algebra.FiniteType P (S ⧸ 𝔑) := by
    first
    | infer_instance
    | exact Algebra.FiniteType.of_surjective inferInstance (Ideal.Quotient.mkₐ P 𝔑)
        (Ideal.Quotient.mkₐ_surjective P 𝔑)
  haveI : Algebra.FiniteType (P ⧸ maximalIdeal P) (S ⧸ 𝔑) :=
    Algebra.FiniteType.of_restrictScalars_finiteType P _ _
  haveI : Module.Finite (P ⧸ maximalIdeal P) (S ⧸ 𝔑) :=
    finite_of_finite_type_of_isJacobsonRing _ _
  haveI : Algebra.IsIntegral P (P ⧸ maximalIdeal P) := by
    first
    | infer_instance
    | exact Algebra.IsIntegral.of_surjective (Ideal.Quotient.mkₐ P (maximalIdeal P))
        (Ideal.Quotient.mkₐ_surjective P _)
  exact Algebra.IsIntegral.trans (P ⧸ maximalIdeal P)

/- English proof (translation)
Use `haveI := isIntegral_quotient_of_isMaximal_of_comap_eq 𝔑 h`. Use `haveI : Algebra.IsIntegral S' (S ⧸ 𝔑) := by first`. Consider the case `exact Algebra.IsIntegral.tower_top P`. Consider the case `exact Algebra.IsIntegral.tower_top (R := P)`. Use `letI : Field (S ⧸ 𝔑) := Ideal.Quotient.field _`.

Establish `hbot` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := S') (⊥ : Ideal (S ⧸ 𝔑))`. Establish `heq : (⊥ : Ideal (S ⧸ 𝔑)).comap (algebraMap S' (S ⧸ 𝔑)) = 𝔑.comap (algebraMap S' S)`. Use extensionality with `y`. Rewrite using `[Ideal.mem_comap, Ideal.mem_bot, Ideal.mem_comap]`. Use `first`.

Consider the case `exact Ideal.Quotient.eq_zero_iff_mem`. Consider the case `(rw [IsScalarTower.algebraMap_apply S' S (S ⧸ 𝔑), Ideal.Quotient.algebraMap_eq]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem)`. Rewrite using `[← heq]`. Conclude with `hbot`.
-/
theorem isMaximal_comap_of_isMaximal_of_comap_eq {S' S : Type*} [CommRing S'] [CommRing S]
    [Algebra P S'] [Algebra P S] [Algebra S' S] [IsScalarTower P S' S] [Algebra.FiniteType P S]
    (𝔑 : Ideal S) [𝔑.IsMaximal] (h : 𝔑.comap (algebraMap P S) = maximalIdeal P) :
    (𝔑.comap (algebraMap S' S)).IsMaximal := by
  haveI := isIntegral_quotient_of_isMaximal_of_comap_eq 𝔑 h
  haveI : Algebra.IsIntegral S' (S ⧸ 𝔑) := by
    first
    | exact Algebra.IsIntegral.tower_top P
    | exact Algebra.IsIntegral.tower_top (R := P)
  letI : Field (S ⧸ 𝔑) := Ideal.Quotient.field _
  have hbot := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := S') (⊥ : Ideal (S ⧸ 𝔑))
  have heq : (⊥ : Ideal (S ⧸ 𝔑)).comap (algebraMap S' (S ⧸ 𝔑)) = 𝔑.comap (algebraMap S' S) := by
    ext y
    rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.mem_comap]
    first
    | exact Ideal.Quotient.eq_zero_iff_mem
    | (rw [IsScalarTower.algebraMap_apply S' S (S ⧸ 𝔑), Ideal.Quotient.algebraMap_eq]
       exact Ideal.Quotient.eq_zero_iff_mem)
  rw [← heq]
  exact hbot

/- English proof (translation)
Use `haveI := isIntegral_quotient_of_isMaximal_of_comap_eq 𝔑 h`. Take `⟨g, hg, hgx⟩` from `Algebra.IsIntegral.isIntegral (R := P) (Ideal.Quotient.mk 𝔑 x)`. Use `⟨g, hg, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Establish `key : Ideal.Quotient.mk 𝔑 (aeval x g) = aeval (Ideal.Quotient.mk 𝔑 x) g` using `by first`.

Consider the case `exact (Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ P 𝔑) x g).symm`. Consider the case `simpa using (Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ P 𝔑) x g).symm`. Rewrite using `[key, Polynomial.aeval_def]`. Conclude with `hgx`.
-/
theorem exists_monic_aeval_mem_of_isMaximal {S : Type*} [CommRing S] [Algebra P S]
    [Algebra.FiniteType P S] (𝔑 : Ideal S) [𝔑.IsMaximal]
    (h : 𝔑.comap (algebraMap P S) = maximalIdeal P) (x : S) :
    ∃ g : P[X], g.Monic ∧ aeval x g ∈ 𝔑 := by
  haveI := isIntegral_quotient_of_isMaximal_of_comap_eq 𝔑 h
  obtain ⟨g, hg, hgx⟩ := Algebra.IsIntegral.isIntegral (R := P) (Ideal.Quotient.mk 𝔑 x)
  refine ⟨g, hg, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have key : Ideal.Quotient.mk 𝔑 (aeval x g) = aeval (Ideal.Quotient.mk 𝔑 x) g := by
    first
    | exact (Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ P 𝔑) x g).symm
    | simpa using (Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ P 𝔑) x g).symm
  rw [key, Polynomial.aeval_def]
  exact hgx

end ReciprocityTheory.CA
