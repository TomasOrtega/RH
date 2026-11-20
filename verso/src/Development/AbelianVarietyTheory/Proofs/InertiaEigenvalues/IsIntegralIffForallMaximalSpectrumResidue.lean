import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

/- English proof (translation)
Use `haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A`. Prove the components needed by the constructor for the conclusion. Introduce `h m`. Use `h.map (Ideal.Quotient.mkₐ K.O m.asIdeal)` as an intermediate fact. Simplify `this` using `[Ideal.Quotient.mkₐ_eq_mk]`.

Introduce `h`. Use `letI : Fintype (MaximalSpectrum B.A) := Fintype.ofFinite _`. Use `choose p hpm hp using fun m : MaximalSpectrum B.A => h m`. Use `⟨∏ m, p m, monic_prod_of_monic _ _ (fun m _ => hpm m), ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ m : MaximalSpectrum B.A, eval₂ (algebraMap K.O B.A) x (∏ m, p m) ∈ m.asIdeal`.

Introduce `m`. Rewrite using `[eval₂_finset_prod]`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]`. Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`.

Establish `h1` using `hp m`. Establish `h2` using `Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ K.O m.asIdeal) x (p m)`. Rewrite `h2` using `[Ideal.Quotient.mkₐ_eq_mk, aeval_def, h1]`. Rewrite using `[← aeval_def]`. Conclude with `h2.symm`.

Use `set z := eval₂ (algebraMap K.O B.A) x (∏ m, p m)`. Establish `hj : z ∈ Ideal.jacobson (⊥ : Ideal B.A)`. Rewrite using `[Ideal.jacobson, Submodule.mem_sInf]`. Introduce and unpack `J ⟨-, hJ⟩`. Conclude with `hmem ⟨J, hJ⟩`.

Take `⟨k, hk⟩` from `IsArtinianRing.isNilpotent_jacobson_bot (R := B.A)`. Establish `hz : z ^ k = 0`. Use `Ideal.pow_mem_pow hj k` as an intermediate fact. Rewrite `this` using `[hk]`. Simplify using `using this`.

Conclude with `IsReduced.eq_zero z ⟨k, hz⟩`.
-/
theorem isIntegral_iff_forall_maximalSpectrum (K : UQ) (B : InvAlg K) (hred : IsReduced B.A) (x : B.A) :
    IsIntegral K.O x ↔ ∀ m : MaximalSpectrum B.A, IsIntegral K.O (Ideal.Quotient.mk m.asIdeal x) := by
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  constructor
  · intro h m
    have := h.map (Ideal.Quotient.mkₐ K.O m.asIdeal)
    simpa [Ideal.Quotient.mkₐ_eq_mk] using this
  · intro h
    letI : Fintype (MaximalSpectrum B.A) := Fintype.ofFinite _
    choose p hpm hp using fun m : MaximalSpectrum B.A => h m
    refine ⟨∏ m, p m, monic_prod_of_monic _ _ (fun m _ => hpm m), ?_⟩
    have hmem : ∀ m : MaximalSpectrum B.A, eval₂ (algebraMap K.O B.A) x (∏ m, p m) ∈ m.asIdeal := by
      intro m
      rw [eval₂_finset_prod]
      classical
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
      apply Ideal.mul_mem_right
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have h1 := hp m
      have h2 := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ K.O m.asIdeal) x (p m)
      rw [Ideal.Quotient.mkₐ_eq_mk, aeval_def, h1] at h2
      rw [← aeval_def]
      exact h2.symm
    set z := eval₂ (algebraMap K.O B.A) x (∏ m, p m)
    have hj : z ∈ Ideal.jacobson (⊥ : Ideal B.A) := by
      rw [Ideal.jacobson, Submodule.mem_sInf]
      rintro J ⟨-, hJ⟩
      exact hmem ⟨J, hJ⟩
    obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B.A)
    have hz : z ^ k = 0 := by
      have := Ideal.pow_mem_pow hj k
      rw [hk] at this
      simpa using this
    exact IsReduced.eq_zero z ⟨k, hz⟩

end GlobalTheory.UnitLemma
