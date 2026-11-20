import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.SurjPass

/- English proof (translation)
Introduce `P hP hdeg`. Break down `subsingleton_or_nontrivial T with hT | hT` into its components or cases. Conclude with `⟨0, Subsingleton.elim _ _⟩`. Take `⟨Q, hQ, hQdeg, hQm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic ((Polynomial.lifts_iff_coeff_lifts P).mpr fun n => hφ (P.coeff n)) hP`. Take `⟨x, hx⟩` from `h Q hQm (hQdeg ▸ hdeg)`.

Use `⟨φ x, ?_⟩` and prove the remaining obligations. Rewrite using `[← hQ, Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_hom, hx.eq_zero, map_zero]`.
-/
theorem aic_of_surjective {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T)
    (hφ : Function.Surjective φ) (h : Aic S) : Aic T := by
  intro P hP hdeg
  rcases subsingleton_or_nontrivial T with hT | hT
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨Q, hQ, hQdeg, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.lifts_iff_coeff_lifts P).mpr fun n => hφ (P.coeff n)) hP
  obtain ⟨x, hx⟩ := h Q hQm (hQdeg ▸ hdeg)
  refine ⟨φ x, ?_⟩
  rw [← hQ, Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_hom, hx.eq_zero, map_zero]

/- English proof (translation)
Introduce `f g`. Take `⟨f', rfl⟩` from `hφ f`. Take `⟨g', rfl⟩` from `hφ g`. Take `⟨e, he, h1, h2⟩` from `h f' g'`. Use `⟨φ e, ?_, ?_, ?_⟩` and prove the remaining obligations.

Unfold `IsIdempotentElem`. Rewrite using `[← map_mul, he.eq]`. Rewrite `h1`, the goal using `[Ideal.mem_span_singleton]`. Rewrite using `[← map_mul]`. Conclude with `map_dvd φ h1`.

Rewrite `h2`, the goal using `[Ideal.mem_span_singleton]`. Rewrite using `[← map_one φ, ← map_sub, ← map_mul]`. Conclude with `map_dvd φ h2`.
-/
theorem comparable_of_surjective {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T)
    (hφ : Function.Surjective φ) (h : Val0 S) : Val0 T := by
  intro f g
  obtain ⟨f', rfl⟩ := hφ f
  obtain ⟨g', rfl⟩ := hφ g
  obtain ⟨e, he, h1, h2⟩ := h f' g'
  refine ⟨φ e, ?_, ?_, ?_⟩
  · unfold IsIdempotentElem
    rw [← map_mul, he.eq]
  · rw [Ideal.mem_span_singleton] at h1 ⊢
    rw [← map_mul]
    exact map_dvd φ h1
  · rw [Ideal.mem_span_singleton] at h2 ⊢
    rw [← map_one φ, ← map_sub, ← map_mul]
    exact map_dvd φ h2

/- English proof (translation)
Introduce `S _ T _ φ hφ`. Conclude with `⟨aic_of_surjective φ hφ, comparable_of_surjective φ hφ⟩`.
-/
theorem absolutely_closed_comparable_surjective : ∀ {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T),
    Function.Surjective φ → (Aic S → Aic T) ∧ (Val0 S → Val0 T) := by
  intro S _ T _ φ hφ
  exact ⟨aic_of_surjective φ hφ, comparable_of_surjective φ hφ⟩

end GlobalTheory.CompanionTheory.SurjPass
