import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerBasisOfCharpolySeparable

namespace GlobalTheory.UnitLemma

open Polynomial

/- English proof (translation)
Introduce `K B h`. Take `⟨e, he⟩` from `exists_basis_pow_of_separable K B h`. Establish `h2 : minpoly K.E (LinearMap.mulLeft K.E B.g) = minpoly K.E B.g` using `minpoly.algHom_eq (Algebra.lmul K.E B.A) (Algebra.lmul_injective) B.g`. Establish `hms : (minpoly K.E B.g).Separable` using `h.of_dvd (h2 ▸ LinearMap.minpoly_dvd_charpoly (LinearMap.mulLeft K.E B.g))`. Establish `hsurj : ∀ a : B.A, ∃ q : K.E[X], aeval B.g q = a`.

Introduce `a`. Establish `hle : Submodule.span K.E (Set.range e) ≤ Subalgebra.toSubmodule (Algebra.adjoin K.E ({B.g} : Set B.A))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[he]`.

Conclude with `Subalgebra.pow_mem (Algebra.adjoin K.E ({B.g} : Set B.A)) (Algebra.subset_adjoin (Set.mem_singleton B.g)) _`. Establish `ha : a ∈ Algebra.adjoin K.E ({B.g} : Set B.A)` using `hle (e.span_eq ▸ Submodule.mem_top)`. Rewrite `ha` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨q, hq⟩` from `ha`. Conclude with `⟨q, hq⟩`.

Use `⟨fun n hn => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `hn`. Take `⟨q, rfl⟩` from `hsurj n`. Break down `Nat.eq_zero_or_pos k with h0 | h0` into its components or cases. Substitute `h0` using the available equality.

Rewrite `hk` using `[pow_zero]`. Use `haveI := subsingleton_of_zero_eq_one hk.symm`. Conclude with `Subsingleton.elim _ _`. Establish `hdk : minpoly K.E B.g ∣ q ^ k` using `minpoly.dvd _ _ (by rw [map_pow, hk])`. Take `⟨r, hr⟩` from `(hms.squarefree.dvd_pow_iff_dvd h0.ne').1 hdk`.

Rewrite using `[hr, map_mul, minpoly.aeval, zero_mul]`.
-/
theorem InvAlg.isReduced_of_separable_P : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsReduced B.A := by
  intro K B h
  obtain ⟨e, he⟩ := exists_basis_pow_of_separable K B h
  have h2 : minpoly K.E (LinearMap.mulLeft K.E B.g) = minpoly K.E B.g :=
    minpoly.algHom_eq (Algebra.lmul K.E B.A) (Algebra.lmul_injective) B.g
  have hms : (minpoly K.E B.g).Separable :=
    h.of_dvd (h2 ▸ LinearMap.minpoly_dvd_charpoly (LinearMap.mulLeft K.E B.g))
  have hsurj : ∀ a : B.A, ∃ q : K.E[X], aeval B.g q = a := by
    intro a
    have hle : Submodule.span K.E (Set.range e) ≤
        Subalgebra.toSubmodule (Algebra.adjoin K.E ({B.g} : Set B.A)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [he]
      exact Subalgebra.pow_mem (Algebra.adjoin K.E ({B.g} : Set B.A))
        (Algebra.subset_adjoin (Set.mem_singleton B.g)) _
    have ha : a ∈ Algebra.adjoin K.E ({B.g} : Set B.A) := hle (e.span_eq ▸ Submodule.mem_top)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨q, hq⟩ := ha
    exact ⟨q, hq⟩
  refine ⟨fun n hn => ?_⟩
  obtain ⟨k, hk⟩ := hn
  obtain ⟨q, rfl⟩ := hsurj n
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0
    rw [pow_zero] at hk
    haveI := subsingleton_of_zero_eq_one hk.symm
    exact Subsingleton.elim _ _
  have hdk : minpoly K.E B.g ∣ q ^ k := minpoly.dvd _ _ (by rw [map_pow, hk])
  obtain ⟨r, hr⟩ := (hms.squarefree.dvd_pow_iff_dvd h0.ne').1 hdk
  rw [hr, map_mul, minpoly.aeval, zero_mul]

end GlobalTheory.UnitLemma
