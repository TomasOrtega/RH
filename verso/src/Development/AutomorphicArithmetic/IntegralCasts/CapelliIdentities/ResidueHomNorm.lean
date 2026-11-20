import Mathlib

/- English proof (translation)
Introduce `O R Ω _ _ _ _ _ _ _ hres hO hint y`. Establish `hm : ∀ a ∈ IsLocalRing.maximalIdeal R, ‖y a‖ < 1`. Introduce `m hmem`. Assume the negation of the conclusion as `hge`. Establish `hge' : 1 ≤ ‖y m‖` using `not_lt.mp hge`.

Establish `hne : y m ≠ 0`. Introduce `h0`. Rewrite `hge'` using `[h0, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hu : ‖(y m)⁻¹‖ ≤ 1`.

Rewrite using `[norm_inv]`. Conclude with `inv_le_one_of_one_le₀ hge'`. Take `⟨p, hp, hev⟩` from `hint _ hu`. Establish `hrev : Polynomial.eval₂ (algebraMap O Ω) (y m) p.reverse = 0` using `by haveI : Invertible (y m)⁻¹ := invertibleOfNonzero (inv_ne_zero hne)`. Establish `h` using `Polynomial.eval₂_reverse_mul_pow (algebraMap O Ω) (y m)⁻¹ p`.

Rewrite `h` using `[invOf_eq_inv, inv_inv, hev]`. Conclude with `(mul_eq_zero.mp h).resolve_right (pow_ne_zero _ (inv_ne_zero hne))`. Establish `hq : y (Polynomial.aeval m p.reverse) = 0`. Rewrite using `[Polynomial.aeval_algHom_apply y m p.reverse |>.symm]`. Simplify `hrev` using `[Polynomial.aeval_def]`.

Establish `hdvd : m ∣ Polynomial.aeval m p.reverse - 1`. Establish `h` using `Polynomial.sub_dvd_eval_sub m 0 (p.reverse.map (algebraMap O R))`. Establish `h0 : (p.reverse.map (algebraMap O R)).eval 0 = 1`. Rewrite using `[← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map, Polynomial.coeff_zero_reverse, hp.leadingCoeff, map_one]`. Rewrite `h` using `[h0, sub_zero, Polynomial.eval_map_algebraMap]`.

Conclude with `h`. Establish `hunit : IsUnit (Polynomial.aeval m p.reverse : R)`. Assume the negation of the conclusion as `hnu`. Establish `h1 : (Polynomial.aeval m p.reverse : R) ∈ IsLocalRing.maximalIdeal R` using `(IsLocalRing.mem_maximalIdeal _).mpr hnu`. Establish `h2 : Polynomial.aeval m p.reverse - 1 ∈ IsLocalRing.maximalIdeal R` using `Ideal.mem_of_dvd _ hdvd hmem`.

Establish `h3 : (1 : R) ∈ IsLocalRing.maximalIdeal R`. Use `Ideal.sub_mem _ h1 h2` as an intermediate fact. Simplify using `using this`. Conclude with `(Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top h3`. Use `hunit.map y` as an intermediate fact.

Rewrite `this` using `[hq]`. Conclude with `not_isUnit_zero this`. Use `⟨fun x => ?_, hm⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `hres x`. Establish `hx : y x = algebraMap O Ω a + y (x - algebraMap O R a)`.

Rewrite using `[map_sub, AlgHom.commutes]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hx]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hO a) (hm _ ha).le)`.
-/
theorem UpperTheory.residue_hom_norm :
    ∀ {O R Ω : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [NormedField Ω]
        [IsUltrametricDist Ω] [Algebra O Ω]
        (hres : ∀ x : R, ∃ a : O, x - algebraMap O R a ∈ IsLocalRing.maximalIdeal R)
        (hO : ∀ a : O, ‖algebraMap O Ω a‖ ≤ 1) (hint : ∀ x : Ω, ‖x‖ ≤ 1 → IsIntegral O x)
        (y : R →ₐ[O] Ω),
        (∀ a, ‖y a‖ ≤ 1) ∧ ∀ a ∈ IsLocalRing.maximalIdeal R, ‖y a‖ < 1 := by
  intro O R Ω _ _ _ _ _ _ _ hres hO hint y
  have hm : ∀ a ∈ IsLocalRing.maximalIdeal R, ‖y a‖ < 1 := by
    intro m hmem
    by_contra hge
    have hge' : 1 ≤ ‖y m‖ := not_lt.mp hge
    have hne : y m ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hge'
      linarith
    have hu : ‖(y m)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hge'
    obtain ⟨p, hp, hev⟩ := hint _ hu
    have hrev : Polynomial.eval₂ (algebraMap O Ω) (y m) p.reverse = 0 := by
      haveI : Invertible (y m)⁻¹ := invertibleOfNonzero (inv_ne_zero hne)
      have h := Polynomial.eval₂_reverse_mul_pow (algebraMap O Ω) (y m)⁻¹ p
      rw [invOf_eq_inv, inv_inv, hev] at h
      exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ (inv_ne_zero hne))
    have hq : y (Polynomial.aeval m p.reverse) = 0 := by
      rw [Polynomial.aeval_algHom_apply y m p.reverse |>.symm]
      simpa [Polynomial.aeval_def] using hrev
    have hdvd : m ∣ Polynomial.aeval m p.reverse - 1 := by
      have h := Polynomial.sub_dvd_eval_sub m 0 (p.reverse.map (algebraMap O R))
      have h0 : (p.reverse.map (algebraMap O R)).eval 0 = 1 := by
        rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map,
          Polynomial.coeff_zero_reverse, hp.leadingCoeff, map_one]
      rw [h0, sub_zero, Polynomial.eval_map_algebraMap] at h
      exact h
    have hunit : IsUnit (Polynomial.aeval m p.reverse : R) := by
      by_contra hnu
      have h1 : (Polynomial.aeval m p.reverse : R) ∈ IsLocalRing.maximalIdeal R :=
        (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have h2 : Polynomial.aeval m p.reverse - 1 ∈ IsLocalRing.maximalIdeal R :=
        Ideal.mem_of_dvd _ hdvd hmem
      have h3 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
        have := Ideal.sub_mem _ h1 h2
        simpa using this
      exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top h3
    have := hunit.map y
    rw [hq] at this
    exact not_isUnit_zero this
  refine ⟨fun x => ?_, hm⟩
  obtain ⟨a, ha⟩ := hres x
  have hx : y x = algebraMap O Ω a + y (x - algebraMap O R a) := by
    rw [map_sub, AlgHom.commutes]
    ring
  rw [hx]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (hO a) (hm _ ha).le)
