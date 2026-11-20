import Mathlib

open Polynomial

/- English proof (translation)
Establish `hint : IsIntegral ℚ_[l] x` using `(Algebra.IsAlgebraic.isAlgebraic x).isIntegral`. Establish `hm` using `minpoly.monic hint`. Establish `hc : ∀ n, ‖(minpoly ℚ_[l] x).coeff n‖ ≤ 1` using `(spectralValue_le_one_iff hm).1 hx`. Establish `hl : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l])`. Rewrite using `[lifts_iff_coeff_lifts]`.

Introduce `n`. Conclude with `⟨⟨_, hc n⟩, rfl⟩`. Take `⟨q, hq, -, hqm⟩` from `lifts_and_degree_eq_and_monic hl hm`. Use `⟨q, hqm, ?_⟩` and prove the remaining obligations. Establish `h0` using `minpoly.aeval ℚ_[l] x`.

Rewrite `h0` using `[← hq, aeval_def, eval₂_map]`. Rewrite using `[IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l)]`. Conclude with `h0`.
-/
private lemma integral_of_norm {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) (hx : ‖x‖ ≤ 1) :
    IsIntegral ℤ_[l] x := by
  have hint : IsIntegral ℚ_[l] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hm := minpoly.monic hint
  have hc : ∀ n, ‖(minpoly ℚ_[l] x).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hm).1 hx
  have hl : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl hm
  refine ⟨q, hqm, ?_⟩
  have h0 := minpoly.aeval ℚ_[l] x
  rw [← hq, aeval_def, eval₂_map] at h0
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  exact h0

/- English proof (translation)
Establish `hc : spectralValue (minpoly ℚ_[l] x) ≤ 1`. Rewrite using `[spectralValue_le_one_iff (minpoly.monic h.tower_top)]`. Introduce `n`. Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]`. Conclude with `PadicInt.norm_le_one _`.

Conclude with `hc`.
-/
private lemma norm_of_integral {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l)
    (h : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hc : spectralValue (minpoly ℚ_[l] x) ≤ 1 := by
    rw [spectralValue_le_one_iff (minpoly.monic h.tower_top)]
    intro n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  exact hc

/- English proof (translation)
Take `⟨p, hp, he⟩` from `h`. Use `letI := invertibleOfNonzero (inv_ne_zero ha)`. Establish `h1` using `eval₂_reverse_mul_pow (algebraMap R K) ((algebraMap R K a)⁻¹) p`. Rewrite `h1` using `[he, invOf_eq_inv, inv_inv]`. Establish `h2 : eval₂ (algebraMap R K) (algebraMap R K a) p.reverse = 0`.

Simplify `h1` using `[ha]`. Establish `h3 : eval a p.reverse = 0`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero, ← h2, eval₂_at_apply]`. Establish `h5 : p.reverse.coeff 0 = 1`.

Simplify using `[coeff_zero_reverse, hp.leadingCoeff]`. Establish `h4` using `divX_mul_X_add p.reverse`. Rewrite `h3` using `[← h4, h5]`. Simplify using `only [eval_add, eval_mul, eval_X, eval_C] at h3`. Conclude with `isUnit_iff_exists_inv.2 ⟨-(eval a p.reverse.divX), by linear_combination -h3⟩`.
-/
private lemma isUnit_of_inv_integral {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) (a : R) (ha : algebraMap R K a ≠ 0)
    (h : IsIntegral R (algebraMap R K a)⁻¹) : IsUnit a := by
  obtain ⟨p, hp, he⟩ := h
  letI := invertibleOfNonzero (inv_ne_zero ha)
  have h1 := eval₂_reverse_mul_pow (algebraMap R K) ((algebraMap R K a)⁻¹) p
  rw [he, invOf_eq_inv, inv_inv] at h1
  have h2 : eval₂ (algebraMap R K) (algebraMap R K a) p.reverse = 0 := by
    simpa [ha] using h1
  have h3 : eval a p.reverse = 0 := by
    apply hinj
    rw [map_zero, ← h2, eval₂_at_apply]
  have h5 : p.reverse.coeff 0 = 1 := by
    simp [coeff_zero_reverse, hp.leadingCoeff]
  have h4 := divX_mul_X_add p.reverse
  rw [← h4, h5] at h3
  simp only [eval_add, eval_mul, eval_X, eval_C] at h3
  exact isUnit_iff_exists_inv.2 ⟨-(eval a p.reverse.divX), by linear_combination -h3⟩

/- English proof (translation)
Introduce `l _ O _ _`. Establish `hfin : ∀ a : O, IsIntegral ℤ_[l] (a : PadicAlgCl l)` using `fun a => (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map O.val`. Use `⟨fun x hx => (integral_of_norm x hx).tower_top, fun a => norm_of_integral _ (hfin a), fun a ha => lt_of_le_of_ne (norm_of_integral _ (hfin a)) fun h1 => ha ?_⟩` and prove the remaining obligations. Establish `ha0 : (a : PadicAlgCl l) ≠ 0`. Introduce `h`.

Simplify using `[h] at h1`. Establish `hinv : IsIntegral O (a : PadicAlgCl l)⁻¹` using `(integral_of_norm _ (by rw [norm_inv, h1, inv_one])).tower_top`. Conclude with `isUnit_of_inv_integral (K := PadicAlgCl l) Subtype.val_injective a ha0 hinv`.
-/
theorem UpperTheory.integral_dvr_norm :
    ∀ (l : ℕ) [Fact l.Prime] (O : Subalgebra ℤ_[l] (PadicAlgCl l)) [IsDiscreteValuationRing O]
        [Module.Finite ℤ_[l] O],
        (∀ x : PadicAlgCl l, ‖x‖ ≤ 1 → IsIntegral O x) ∧ (∀ a : O, ‖(a : PadicAlgCl l)‖ ≤ 1) ∧
          ∀ a : O, ¬ IsUnit a → ‖(a : PadicAlgCl l)‖ < 1 := by
  intro l _ O _ _
  have hfin : ∀ a : O, IsIntegral ℤ_[l] (a : PadicAlgCl l) := fun a =>
    (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map O.val
  refine ⟨fun x hx => (integral_of_norm x hx).tower_top, fun a => norm_of_integral _ (hfin a),
    fun a ha => lt_of_le_of_ne (norm_of_integral _ (hfin a)) fun h1 => ha ?_⟩
  have ha0 : (a : PadicAlgCl l) ≠ 0 := by
    intro h
    simp [h] at h1
  have hinv : IsIntegral O (a : PadicAlgCl l)⁻¹ :=
    (integral_of_norm _ (by rw [norm_inv, h1, inv_one])).tower_top
  exact isUnit_of_inv_integral (K := PadicAlgCl l) Subtype.val_injective a ha0 hinv
