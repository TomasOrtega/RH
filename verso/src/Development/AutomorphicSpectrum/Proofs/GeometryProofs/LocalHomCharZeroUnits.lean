import Mathlib
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ggeo

/- English proof (translation)
Rewrite using `[Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, RingHom.ext_int (f.comp (algebraMap ℤ A)) (algebraMap ℤ B)]`.
-/
private theorem map_aeval_int' {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : A)
    (q : Polynomial ℤ) : f (Polynomial.aeval a q) = Polynomial.aeval (f a) q := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂,
    RingHom.ext_int (f.comp (algebraMap ℤ A)) (algebraMap ℤ B)]

/- English proof (translation)
Introduce `O F L K _ _ _ _ _ _ β θ ρ hρ hker b hb`. Establish `halg : IsAlgebraic ℤ (β b)` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic (β b))`. Take `⟨q, hq0, hq⟩` from `halg.exists_nonzero_coeff_and_aeval_eq_zero (mem_nonZeroDivisors_of_ne_zero hb)`. Establish `h1 : β (Polynomial.aeval b q) = 0` using `by rw [map_aeval_int', hq]`. Establish `h2 : ρ (θ (Polynomial.aeval b q)) = 0` using `by rw [hker _ h1, map_zero]`.

Rewrite `h2` using `[map_aeval_int', map_aeval_int']`. Establish `h3 : ρ (θ b) ≠ 0`. Introduce `h0`. Rewrite `h2` using `[h0, ← Polynomial.coeff_zero_eq_aeval_zero']`. Conclude with `hq0 (by simpa using h2)`.

Conclude with `hρ.map_nonunit _ (isUnit_iff_ne_zero.mpr h3)`.
-/
theorem unit_of_local_hom_charZero_nf : ∀ (O F L K : Type) [CommRing O] [Field F] [NumberField F] [CommRing L] [Field K] [CharZero K] (β : O →+* F) (θ : O →+* L) (ρ : L →+* K), IsLocalHom ρ → (∀ a, β a = 0 → θ a = 0) → ∀ b, β b ≠ 0 → IsUnit (θ b) := by
  intro O F L K _ _ _ _ _ _ β θ ρ hρ hker b hb
  have halg : IsAlgebraic ℤ (β b) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic (β b))
  obtain ⟨q, hq0, hq⟩ :=
    halg.exists_nonzero_coeff_and_aeval_eq_zero (mem_nonZeroDivisors_of_ne_zero hb)
  have h1 : β (Polynomial.aeval b q) = 0 := by rw [map_aeval_int', hq]
  have h2 : ρ (θ (Polynomial.aeval b q)) = 0 := by rw [hker _ h1, map_zero]
  rw [map_aeval_int', map_aeval_int'] at h2
  have h3 : ρ (θ b) ≠ 0 := by
    intro h0
    rw [h0, ← Polynomial.coeff_zero_eq_aeval_zero'] at h2
    exact hq0 (by simpa using h2)
  exact hρ.map_nonunit _ (isUnit_iff_ne_zero.mpr h3)

end GlobalTheory.CompanionTheory.Ggeo
