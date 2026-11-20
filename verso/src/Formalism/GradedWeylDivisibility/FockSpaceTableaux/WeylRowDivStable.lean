import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowdivLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Unfold `rowDiv`. Rewrite using `[map_add, Polynomial.coeff_add]`.
-/
private theorem rowDiv_add_fock_space_tableaux (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f g : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (f + g) = rowDiv R a b k f + rowDiv R a b k g := by
  unfold rowDiv
  rw [map_add, Polynomial.coeff_add]

/- English proof (translation)
Unfold `rowDiv`. Rewrite using `[map_smul, Polynomial.coeff_smul]`.
-/
private theorem rowDiv_smul_fock_space_tableaux (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (c : R) (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (c • f) = c • rowDiv R a b k f := by
  unfold rowDiv
  rw [map_smul, Polynomial.coeff_smul]

/- English proof (translation)
Unfold `WeylRowDivStable`. Introduce `R _ r n hn ν a b k f hf`. Set `L : MvPolynomial (Fin r × Fin n) R →ₗ[R] MvPolynomial (Fin r × Fin n) R` to `{ toFun := rowDiv R a b k map_add' := rowDiv_add_fock_space_tableaux R a b k map_smul' := rowDiv_smul_fock_space_tableaux R a b k }`. Establish `key : weyl R r n hn ν ≤ (weyl R r n hn ν).comap L`. Unfold `weyl`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap]`. Conclude with `Submodule.subset_span ⟨(a, b, k) :: w, rfl⟩`. Conclude with `key hf`.
-/
theorem weylModuleRowDividedPowerStable : WeylRowDivStable := by
  unfold WeylRowDivStable
  intro R _ r n hn ν a b k f hf
  let L : MvPolynomial (Fin r × Fin n) R →ₗ[R] MvPolynomial (Fin r × Fin n) R :=
    { toFun := rowDiv R a b k
      map_add' := rowDiv_add_fock_space_tableaux R a b k
      map_smul' := rowDiv_smul_fock_space_tableaux R a b k }
  have key : weyl R r n hn ν ≤ (weyl R r n hn ν).comap L := by
    unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    exact Submodule.subset_span ⟨(a, b, k) :: w, rfl⟩
  exact key hf

end Formalism.GradedWeylDivisibility
