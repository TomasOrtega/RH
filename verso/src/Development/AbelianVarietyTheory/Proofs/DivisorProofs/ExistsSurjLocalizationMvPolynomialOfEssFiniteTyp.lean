import Mathlib
open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `Λ R _ _ _ _ h`. Take `⟨σ, hσ⟩` from `(Algebra.essFiniteType_iff Λ R).mp h`. Set `y : Fin σ.card → R` to `fun i => (σ.equivFin.symm i : R)`. Set `φ₀ : MvPolynomial (Fin σ.card) Λ →ₐ[Λ] R` to `MvPolynomial.aeval y`. Establish `hrange : Algebra.adjoin Λ (σ : Set R) = φ₀.range`.

Rewrite using `[← Algebra.adjoin_range_eq_range_aeval]`. Use `congr 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Conclude with `⟨σ.equivFin ⟨x, hx⟩, by simp [y]⟩`. Introduce and unpack `⟨i, rfl⟩`. Conclude with `(σ.equivFin.symm i).2`. Set `P : Ideal (MvPolynomial (Fin σ.card) Λ)` to `(maximalIdeal R).comap φ₀`. Establish `hunit : ∀ b : P.primeCompl, IsUnit (φ₀ b)`.

Introduce `b`. Assume the negation of the conclusion as `hb`. Conclude with `b.2 ((mem_maximalIdeal _).mpr hb)`. Use `⟨σ.card, P, inferInstance, IsLocalization.liftAlgHom (M := P.primeCompl) (f := φ₀) hunit, ?_⟩` and prove the remaining obligations. Introduce `r`.

Take `⟨t, ht, htu, hrt⟩` from `hσ r`. Rewrite `ht`, `hrt` using `[hrange]`. Take `⟨b, rfl⟩` from `ht`. Take `⟨a, ha⟩` from `hrt`. Establish `hb : b ∈ P.primeCompl` using `fun hbP => (mem_maximalIdeal _).mp hbP htu`.

Use `⟨IsLocalization.mk' (Localization.AtPrime P) a ⟨b, hb⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocalization.liftAlgHom_apply, IsLocalization.lift_mk'_spec]`. Express the relevant statement in the definitionally equal form `φ₀ a = φ₀ b * r`. Conclude with `ha.trans (mul_comm _ _)`.
-/
theorem exists_surj_localization_mvPolynomial_of_essFiniteType :
    ∀ (Λ R : Type) [CommRing Λ] [CommRing R] [IsLocalRing R] [Algebra Λ R]
      [Algebra.EssFiniteType Λ R], ∃ (n : ℕ) (P : Ideal (MvPolynomial (Fin n) Λ)) (_ : P.IsPrime)
      (φ : Localization.AtPrime P →ₐ[Λ] R), Function.Surjective φ := by
  intro Λ R _ _ _ _ h
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff Λ R).mp h
  let y : Fin σ.card → R := fun i => (σ.equivFin.symm i : R)
  let φ₀ : MvPolynomial (Fin σ.card) Λ →ₐ[Λ] R := MvPolynomial.aeval y
  have hrange : Algebra.adjoin Λ (σ : Set R) = φ₀.range := by
    rw [← Algebra.adjoin_range_eq_range_aeval]
    congr 1
    ext x
    constructor
    · intro hx
      exact ⟨σ.equivFin ⟨x, hx⟩, by simp [y]⟩
    · rintro ⟨i, rfl⟩
      exact (σ.equivFin.symm i).2
  let P : Ideal (MvPolynomial (Fin σ.card) Λ) := (maximalIdeal R).comap φ₀
  have hunit : ∀ b : P.primeCompl, IsUnit (φ₀ b) := by
    intro b
    by_contra hb
    exact b.2 ((mem_maximalIdeal _).mpr hb)
  refine ⟨σ.card, P, inferInstance, IsLocalization.liftAlgHom (M := P.primeCompl) (f := φ₀) hunit, ?_⟩
  intro r
  obtain ⟨t, ht, htu, hrt⟩ := hσ r
  rw [hrange] at ht hrt
  obtain ⟨b, rfl⟩ := ht
  obtain ⟨a, ha⟩ := hrt
  have hb : b ∈ P.primeCompl := fun hbP => (mem_maximalIdeal _).mp hbP htu
  refine ⟨IsLocalization.mk' (Localization.AtPrime P) a ⟨b, hb⟩, ?_⟩
  rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_mk'_spec]
  change φ₀ a = φ₀ b * r
  exact ha.trans (mul_comm _ _)

end GlobalTheory
