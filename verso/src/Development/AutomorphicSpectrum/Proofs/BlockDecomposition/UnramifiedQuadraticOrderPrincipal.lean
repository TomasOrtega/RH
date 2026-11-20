import Mathlib

namespace GlobalTheory.CompanionTheory.QuadraticUnit

open Polynomial IsLocalRing

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.

A detailed English derivation is pending.
-/
theorem norm_isUnit {R : Type} [CommRing R] [HenselianLocalRing R] (D : R) (hD : IsUnit D)
    (h2 : IsUnit (2 : R)) (hns : ¬ ∃ e : R, D = e * e) (a b : R)
    (hab : IsUnit a ∨ IsUnit b) : IsUnit (a * a - D * (b * b)) := by
  have hmax : ∀ x : R, x ∈ maximalIdeal R ↔ ¬ IsUnit x := fun x => by
    rw [mem_maximalIdeal, mem_nonunits_iff]
  by_contra hnu
  have hm : a * a - D * (b * b) ∈ maximalIdeal R := (hmax _).2 hnu
  have hb : IsUnit b := by
    rcases hab with ha | hb
    · by_contra hb
      have hbm : b ∈ maximalIdeal R := (hmax b).2 hb
      have haa : a * a ∈ maximalIdeal R := by
        have he : a * a = (a * a - D * (b * b)) + D * (b * b) := by ring
        rw [he]
        exact add_mem hm (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hbm))
      exact (hmax _).1 haa (ha.mul ha)
    · exact hb
  obtain ⟨w, hw⟩ : ∃ w : R, b * w = 1 := ⟨_, hb.mul_val_inv⟩
  set c := a * w with hc
  have hcD : c * c - D ∈ maximalIdeal R := by
    have he : c * c - D = (a * a - D * (b * b)) * (w * w) := by
      have hw2 : D = D * ((b * w) * (b * w)) := by rw [hw]; ring
      rw [hc]
      nth_rewrite 1 [hw2]
      ring
    rw [he]
    exact Ideal.mul_mem_right _ _ hm
  have hcc : IsUnit (c * c) := by
    by_contra hcc
    have hDm : D ∈ maximalIdeal R := by
      have he : D = c * c - (c * c - D) := by ring
      rw [he]
      exact sub_mem ((hmax _).2 hcc) hcD
    exact (hmax _).1 hDm hD
  have hcu : IsUnit c := isUnit_of_mul_isUnit_left hcc
  obtain ⟨e, he, -⟩ := HenselianLocalRing.is_henselian (X ^ 2 - C D) (monic_X_pow_sub_C D two_ne_zero) c
    (by simpa [sq] using hcD) (by simpa [derivative_X_pow, one_add_one_eq_two] using h2.mul hcu)
  apply hns
  refine ⟨e, ?_⟩
  have := he.eq_zero
  simp only [eval_sub, eval_pow, eval_X, eval_C] at this
  linear_combination -this

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem isUnit_add_mul {R O : Type} [CommRing R] [HenselianLocalRing R] [CommRing O]
    (ι : R →+* O) (δ : O) (D : R) (hδ : δ * δ = ι D) (hD : IsUnit D)
    (h2 : IsUnit (2 : R)) (hns : ¬ ∃ e : R, D = e * e) (a b : R)
    (hab : IsUnit a ∨ IsUnit b) : IsUnit (ι a + ι b * δ) := by
  have hn := (norm_isUnit D hD h2 hns a b hab).map ι
  have he : (ι a + ι b * δ) * (ι a - ι b * δ) = ι (a * a - D * (b * b)) := by
    rw [map_sub, map_mul, map_mul, map_mul, ← hδ]
    ring
  rw [← he] at hn
  exact isUnit_of_mul_isUnit_left hn

/- English proof (translation)
Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations.

Simplify to obtain the desired conclusion from the available facts.
-/
theorem exists_eq_mul_isUnit {R O : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [CommRing O] (ι : R →+* O) (δ : O) (D : R) (hδ : δ * δ = ι D)
    (hspan : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ) (hD : IsUnit D)
    (h2 : IsUnit (2 : R)) (hns : ¬ ∃ e : R, D = e * e) (y : O) :
    ∃ (g : R) (u : O), IsUnit u ∧ y = ι g * u := by
  obtain ⟨p, q, rfl⟩ := hspan y
  rcases ValuationRing.dvd_total p q with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · refine ⟨p, 1 + ι r * δ, ?_, by rw [map_mul]; ring⟩
    simpa using isUnit_add_mul ι δ D hδ hD h2 hns 1 r (Or.inl isUnit_one)
  · refine ⟨q, ι r + δ, ?_, by rw [map_mul]; ring⟩
    simpa using isUnit_add_mul ι δ D hδ hD h2 hns r 1 (Or.inr isUnit_one)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem isPrincipalIdealRing_of_nonsquare_unit :
    ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
      [CommRing O] (ι : R →+* O) (δ : O) (D : R), δ * δ = ι D →
      (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) → (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) →
      IsUnit D → IsUnit (2 : R) → (¬ ∃ e : R, D = e * e) → IsPrincipalIdealRing O := by
  intro R O _ _ _ _ _ ι δ D hδ hspan _ hD h2 hns
  refine ⟨fun I => ⟨?_⟩⟩
  obtain ⟨g₀, hg₀⟩ := (IsPrincipalIdealRing.principal (Ideal.comap ι I)).principal
  have hg₀I : ι g₀ ∈ I := by
    have hmem : g₀ ∈ Ideal.comap ι I := by
      rw [hg₀]
      exact Submodule.mem_span_singleton_self g₀
    exact Ideal.mem_comap.1 hmem
  refine ⟨ι g₀, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem I).2 hg₀I)⟩
  intro y hy
  obtain ⟨g, u, hu, rfl⟩ := exists_eq_mul_isUnit ι δ D hδ hspan hD h2 hns y
  have hg : g ∈ Ideal.comap ι I := by
    rw [Ideal.mem_comap]
    have he : ι g = ι g * u * ↑hu.unit⁻¹ := by rw [mul_assoc, hu.mul_val_inv, mul_one]
    rw [he]
    exact I.mul_mem_right _ hy
  rw [hg₀] at hg
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hg
  refine Ideal.mem_span_singleton.2 ⟨ι r * u, ?_⟩
  rw [← hr, smul_eq_mul, map_mul]
  ring

end GlobalTheory.CompanionTheory.QuadraticUnit
