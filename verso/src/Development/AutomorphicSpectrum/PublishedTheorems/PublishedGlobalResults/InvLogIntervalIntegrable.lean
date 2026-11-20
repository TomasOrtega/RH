import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.PrimesInProgressionsRelative
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PrimesInProgressionsRelativeOfTzRat

noncomputable section

namespace GlobalTheory.CompanionTheory.PrimesAP

/- English proof (translation)
Establish `hL : 0 < Real.log X` using `Real.log_pos (by linarith)`. Break down `h with rfl | ⟨h1, h2, h3⟩` into its components or cases. Rewrite using `[zero_mul, sub_zero]`. Conclude with `lt_of_lt_of_le (div_pos (by linarith) hL) (le_integral_inv_log le_rfl (by linarith))`. Establish `hY : 2 ≤ X ^ β`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num`. Use `_ ≤ X ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hX (by norm_num)`. Use `_ ≤ X ^ β := Real.rpow_le_rpow_of_exponent_le (by linarith) h2`. Establish `hYX : X ^ β < X`.

Use `Real.rpow_lt_rpow_of_exponent_lt (x := X) (by linarith) h3` as an intermediate fact. Rewrite `this` using `[Real.rpow_one]`. Then use the resulting hypothesis. Establish `h5 : 0 < ∫ t in X ^ β..X, 1 / Real.log t` using `lt_of_lt_of_le (div_pos (by linarith) hL) (le_integral_inv_log hY hYX.le)`. Establish `h6` using `intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_inv_log le_rfl hY) (intervalIntegrable_inv_log hY (X := X) (by linarith))`. Establish `h7 : 0 ≤ ∫ t in (2 : ℝ)..X ^ β, 1 / Real.log t`.

Use `le_trans ?_ (le_integral_inv_log le_rfl hY)` and prove the remaining obligations. Conclude with `div_nonneg (by linarith) (Real.log_nonneg (by linarith))`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem mainTerm_pos_model {θ β X : ℝ} (hX : 4 ≤ X) (h : θ = 0 ∨ (θ ≤ 1 ∧ 1 / 2 ≤ β ∧ β < 1)) :
    0 < (∫ t in (2 : ℝ)..X, 1 / Real.log t) - θ * ∫ t in (2 : ℝ)..X ^ β, 1 / Real.log t := by
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  rcases h with rfl | ⟨h1, h2, h3⟩
  · rw [zero_mul, sub_zero]
    exact lt_of_lt_of_le (div_pos (by linarith) hL) (le_integral_inv_log le_rfl (by linarith))
  · have hY : 2 ≤ X ^ β := by
      calc (2 : ℝ) = 4 ^ (1 / 2 : ℝ) := by
            rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ X ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hX (by norm_num)
        _ ≤ X ^ β := Real.rpow_le_rpow_of_exponent_le (by linarith) h2
    have hYX : X ^ β < X := by
      have := Real.rpow_lt_rpow_of_exponent_lt (x := X) (by linarith) h3
      rwa [Real.rpow_one] at this
    have h5 : 0 < ∫ t in X ^ β..X, 1 / Real.log t :=
      lt_of_lt_of_le (div_pos (by linarith) hL) (le_integral_inv_log hY hYX.le)
    have h6 := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_inv_log le_rfl hY) (intervalIntegrable_inv_log hY (X := X) (by linarith))
    have h7 : 0 ≤ ∫ t in (2 : ℝ)..X ^ β, 1 / Real.log t := by
      refine le_trans ?_ (le_integral_inv_log le_rfl hY)
      exact div_nonneg (by linarith) (Real.log_nonneg (by linarith))
    nlinarith

/- English proof (translation)
Take `⟨C₀, C, c, cQ, c₁, h0, hC, hc, -, -, H⟩` from `h`. Use `set T : ℝ := 2 * C / c + 1 with hT`. Establish `hT1 : 1 ≤ T` using `by have : 0 ≤ 2 * C / c := by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcT : c * T = 2 * C + c` using `by rw [hT]; field_simp`.

Establish `hexp : ∀ t : ℝ, T ≤ t → C * Real.exp (-(c * t)) < 1 / 2` using `fun t ht => by`. Establish `h1 : 2 * C < Real.exp (c * t)`. Use `Real.add_one_le_exp (c * t)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set L : ℝ := max C₀ (T ^ 2) with hL`. Establish `hLT : T ^ 2 ≤ L` using `le_max_right _ _`. Establish `hL1 : 1 ≤ L` using `by nlinarith`. Use `⟨L, by linarith, fun N _ a ha => ?_⟩` and prove the remaining obligations.

Take `⟨β, θ, hθ, hb⟩` from `H N`. Establish `hN : (1 : ℝ) ≤ N` using `by exact_mod_cast NeZero.pos N`. Establish `hB : (4 : ℝ) ≤ 4 * N` using `by linarith`. Use `set X : ℝ := (4 * N : ℝ) ^ L with hX`. Establish `hX4 : 4 ≤ X`.

Use `Real.rpow_le_rpow_of_exponent_le (x := 4 * (N : ℝ)) (by linarith) hL1` as an intermediate fact. Rewrite `this` using `[Real.rpow_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlog : 1 ≤ Real.log (4 * N)`. Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`.

Combine the linear relations using `[Real.exp_one_lt_d9]`. Establish `hlX : Real.log X = L * Real.log (4 * N)` using `Real.log_rpow (by linarith) _`. Establish `hb'` using `hb a ha X (Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _))`. Establish `e1 : C * Real.exp (-(c * Real.log X / Real.log (4 * N))) < 1 / 2`. Establish `: c * Real.log X / Real.log (4 * N) = c * L`.

Rewrite using `[hlX]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]; exact hexp L (by nlinarith)`. Establish `e2 : C * Real.exp (-(c * Real.sqrt (Real.log X))) < 1 / 2` using `hexp _ (Real.le_sqrt_of_sq_le (by rw [hlX]; nlinarith))`. Establish `hm : 0 < ((∫ t in (2 : ℝ)..X, 1 / Real.log t) - θ a * ∫ t in (2 : ℝ)..X ^ β, 1 / Real.log t) / (Nat.totient N : ℝ)`.

Use `div_pos (mainTerm_pos_model hX4 ?_) (by exact_mod_cast Nat.totient_pos.2 (NeZero.pos N))` and prove the remaining obligations. Break down `hθ with ⟨h1, -⟩ | ⟨χ, h1, h2, h3, -⟩` into its components or cases. Conclude with `Or.inl (h1 a)`. Use `Or.inr ⟨?_, h2, h3⟩` and prove the remaining obligations. Use `χ.norm_le_one a` as an intermediate fact.

Rewrite `this` using `[h1 a, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `(abs_le.1 this).2`. Establish `hpos : (0 : ℝ) < (((Finset.Icc 1 ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ (p : ZMod N) = a)).card : ℝ)`. Use `(abs_le.1 hb').1` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Take `⟨p, hp⟩` from `Finset.card_pos.1 (Nat.cast_pos.1 hpos)`. Rewrite `hp` using `[Finset.mem_filter, Finset.mem_Icc]`. Conclude with `⟨p, hp.2.1, hp.2.2, (Nat.le_floor_iff (by linarith)).1 hp.1.2⟩`.
-/
theorem linnik_of_relative_model (h : PrimesInProgressionsRelative) :
    ∃ L : ℝ, 0 < L ∧ ∀ (N : ℕ) [NeZero N] (a : ZMod N), IsUnit a →
      ∃ p : ℕ, p.Prime ∧ (p : ZMod N) = a ∧ (p : ℝ) ≤ (4 * N : ℝ) ^ L := by
  classical
  obtain ⟨C₀, C, c, cQ, c₁, h0, hC, hc, -, -, H⟩ := h
  set T : ℝ := 2 * C / c + 1 with hT
  have hT1 : 1 ≤ T := by have : 0 ≤ 2 * C / c := by positivity
                         linarith
  have hcT : c * T = 2 * C + c := by rw [hT]; field_simp
  have hexp : ∀ t : ℝ, T ≤ t → C * Real.exp (-(c * t)) < 1 / 2 := fun t ht => by
    have h1 : 2 * C < Real.exp (c * t) := by
      have := Real.add_one_le_exp (c * t)
      nlinarith
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)]
    linarith
  set L : ℝ := max C₀ (T ^ 2) with hL
  have hLT : T ^ 2 ≤ L := le_max_right _ _
  have hL1 : 1 ≤ L := by nlinarith
  refine ⟨L, by linarith, fun N _ a ha => ?_⟩
  obtain ⟨β, θ, hθ, hb⟩ := H N
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hB : (4 : ℝ) ≤ 4 * N := by linarith
  set X : ℝ := (4 * N : ℝ) ^ L with hX
  have hX4 : 4 ≤ X := by
    have := Real.rpow_le_rpow_of_exponent_le (x := 4 * (N : ℝ)) (by linarith) hL1
    rw [Real.rpow_one] at this
    linarith
  have hlog : 1 ≤ Real.log (4 * N) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hlX : Real.log X = L * Real.log (4 * N) := Real.log_rpow (by linarith) _
  have hb' := hb a ha X (Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _))
  have e1 : C * Real.exp (-(c * Real.log X / Real.log (4 * N))) < 1 / 2 := by
    have : c * Real.log X / Real.log (4 * N) = c * L := by
      rw [hlX]; field_simp
    rw [this]; exact hexp L (by nlinarith)
  have e2 : C * Real.exp (-(c * Real.sqrt (Real.log X))) < 1 / 2 :=
    hexp _ (Real.le_sqrt_of_sq_le (by rw [hlX]; nlinarith))
  have hm : 0 < ((∫ t in (2 : ℝ)..X, 1 / Real.log t) - θ a * ∫ t in (2 : ℝ)..X ^ β, 1 / Real.log t) /
      (Nat.totient N : ℝ) := by
    refine div_pos (mainTerm_pos_model hX4 ?_) (by exact_mod_cast Nat.totient_pos.2 (NeZero.pos N))
    rcases hθ with ⟨h1, -⟩ | ⟨χ, h1, h2, h3, -⟩
    · exact Or.inl (h1 a)
    · refine Or.inr ⟨?_, h2, h3⟩
      have := χ.norm_le_one a
      rw [h1 a, Complex.norm_real, Real.norm_eq_abs] at this
      exact (abs_le.1 this).2
  have hpos : (0 : ℝ) < (((Finset.Icc 1 ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ (p : ZMod N) = a)).card : ℝ) := by
    have := (abs_le.1 hb').1
    nlinarith
  obtain ⟨p, hp⟩ := Finset.card_pos.1 (Nat.cast_pos.1 hpos)
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  exact ⟨p, hp.2.1, hp.2.2, (Nat.le_floor_iff (by linarith)).1 hp.1.2⟩

end GlobalTheory.CompanionTheory.PrimesAP

end

open scoped BigOperators Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel

/- English proof (translation)
Apply `ContinuousOn.intervalIntegrable` to reduce the goal to its premises. Establish `h2 : ∀ t ∈ Set.uIcc u v, (2 : ℝ) ≤ t` using `fun t ht => le_trans (le_min hu hv) ht.1`. Use `ContinuousOn.div continuousOn_const (Real.continuousOn_log.mono ?_) ?_` and prove the remaining obligations. Introduce `t ht`. Use `h2 t ht` as an intermediate fact.

Simplify using `only [Set.mem_compl_iff, Set.mem_singleton_iff]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `t ht; have := h2 t ht; exact (Real.log_pos (by linarith)).ne'`.
-/
theorem invLog_intervalIntegrable {u v : ℝ} (hu : 2 ≤ u) (hv : 2 ≤ v) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume u v := by
  apply ContinuousOn.intervalIntegrable
  have h2 : ∀ t ∈ Set.uIcc u v, (2 : ℝ) ≤ t := fun t ht => le_trans (le_min hu hv) ht.1
  refine ContinuousOn.div continuousOn_const (Real.continuousOn_log.mono ?_) ?_
  · intro t ht; have := h2 t ht; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith
  · intro t ht; have := h2 t ht; exact (Real.log_pos (by linarith)).ne'

/- English proof (translation)
Use `intervalIntegral.intervalIntegral_pos_of_pos_on (invLog_intervalIntegrable hu (by linarith)) ?_ huv` and prove the remaining obligations. Introduce `t ht`. Conclude with `one_div_pos.2 (Real.log_pos (by linarith [ht.1]))`.
-/
theorem invLog_integral_pos {u v : ℝ} (hu : 2 ≤ u) (huv : u < v) :
    0 < ∫ t in u..v, 1 / Real.log t := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (invLog_intervalIntegrable hu (by linarith)) ?_ huv
  intro t ht
  exact one_div_pos.2 (Real.log_pos (by linarith [ht.1]))

/- English proof (translation)
Establish `h1` using `intervalIntegral.integral_add_adjacent_intervals (invLog_intervalIntegrable (le_refl 2) hY) (invLog_intervalIntegrable hY (by linarith : (2:ℝ) ≤ X))`. Establish `h2` using `invLog_integral_pos hY hYX`. Establish `h3 : 0 ≤ ∫ t in (2 : ℝ)..Y, 1 / Real.log t`. Break down `hY.eq_or_lt with h | h` into its components or cases. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Conclude with `(invLog_integral_pos le_rfl h).le`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem main_pos {X Y θ : ℝ} (hθ : θ ≤ 1) (hY : 2 ≤ Y) (hYX : Y < X) :
    0 < (∫ t in (2 : ℝ)..X, 1 / Real.log t) - θ * ∫ t in (2 : ℝ)..Y, 1 / Real.log t := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (invLog_intervalIntegrable (le_refl 2) hY) (invLog_intervalIntegrable hY (by linarith : (2:ℝ) ≤ X))
  have h2 := invLog_integral_pos hY hYX
  have h3 : 0 ≤ ∫ t in (2 : ℝ)..Y, 1 / Real.log t := by
    rcases hY.eq_or_lt with h | h
    · subst h; simp
    · exact (invLog_integral_pos le_rfl h).le
  nlinarith

/- English proof (translation)
Establish `t1 : Filter.Tendsto (fun L : ℝ => Real.exp (-(c * L))) Filter.atTop (nhds 0)` using `Real.tendsto_exp_neg_atTop_nhds_zero.comp (Filter.tendsto_id.const_mul_atTop hc)`. Establish `t2 : Filter.Tendsto (fun L : ℝ => Real.exp (-(c * Real.sqrt L))) Filter.atTop (nhds 0)` using `t1.comp Real.tendsto_sqrt_atTop`. Establish `t3` using `(t1.const_mul C).add (t2.const_mul C)`. Simplify using `only [mul_zero, add_zero] at t3`. Use `(t3.eventually (gt_mem_nhds zero_lt_one)).and ((Filter.eventually_ge_atTop C₀).and (Filter.eventually_ge_atTop 2))` as an intermediate fact.

Take `⟨L, h, h1, h2⟩` from `this.exists`. Conclude with `⟨L, h1, h2, h⟩`.
-/
theorem exists_exponent {C c : ℝ} (C₀ : ℝ) (hc : 0 < c) :
    ∃ L : ℝ, C₀ ≤ L ∧ 2 ≤ L ∧ C * Real.exp (-(c * L)) + C * Real.exp (-(c * Real.sqrt L)) < 1 := by
  have t1 : Filter.Tendsto (fun L : ℝ => Real.exp (-(c * L))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (Filter.tendsto_id.const_mul_atTop hc)
  have t2 : Filter.Tendsto (fun L : ℝ => Real.exp (-(c * Real.sqrt L))) Filter.atTop (nhds 0) :=
    t1.comp Real.tendsto_sqrt_atTop
  have t3 := (t1.const_mul C).add (t2.const_mul C)
  simp only [mul_zero, add_zero] at t3
  have := (t3.eventually (gt_mem_nhds zero_lt_one)).and
    ((Filter.eventually_ge_atTop C₀).and (Filter.eventually_ge_atTop 2))
  obtain ⟨L, h, h1, h2⟩ := this.exists
  exact ⟨L, h1, h2, h⟩

/- English proof (translation)
Take `⟨L, -, hL⟩` from `GlobalTheory.CompanionTheory.PrimesAP.linnik_of_relative_model h`. Conclude with `⟨L, hL⟩`.
-/
theorem linnik (h : PrimesInProgressionsRelative) :
    ∃ L : ℝ, ∀ (N : ℕ) [NeZero N] (a : ZMod N), IsUnit a →
      ∃ p : ℕ, p.Prime ∧ (p : ZMod N) = a ∧ (p : ℝ) ≤ (4 * N : ℝ) ^ L := by
  obtain ⟨L, -, hL⟩ := GlobalTheory.CompanionTheory.PrimesAP.linnik_of_relative_model h
  exact ⟨L, hL⟩

end GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel

end
