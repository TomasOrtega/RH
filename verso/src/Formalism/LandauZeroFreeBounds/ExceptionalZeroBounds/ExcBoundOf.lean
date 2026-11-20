import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Establish `hl3 : 0 < Real.log 3` using `Real.log_pos (by norm_num)`. Use `⟨Real.log 3 + 1 / δ, add_pos hl3 (div_pos one_pos hδ), fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx0 : 0 < x` using `by linarith`. Establish `h1 : 1 ≤ x ^ δ` using `Real.one_le_rpow hx hδ.le`. Establish `h2 : Real.log x ≤ x ^ δ / δ` using `Real.log_le_rpow_div hx0.le hδ`.

Establish `h4 : Real.log 3 ≤ Real.log 3 * x ^ δ` using `by nlinarith`. Establish `h5 : (Real.log 3 + 1 / δ) * x ^ δ = Real.log 3 * x ^ δ + x ^ δ / δ` using `by ring`. Rewrite using `[Real.log_mul (by norm_num) hx0.ne', h5]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma log_le_const_mul_rpow (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 1 ≤ x → Real.log (3 * x) ≤ K * x ^ δ := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨Real.log 3 + 1 / δ, add_pos hl3 (div_pos one_pos hδ), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have h1 : 1 ≤ x ^ δ := Real.one_le_rpow hx hδ.le
  have h2 : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδ
  have h4 : Real.log 3 ≤ Real.log 3 * x ^ δ := by nlinarith
  have h5 : (Real.log 3 + 1 / δ) * x ^ δ = Real.log 3 * x ^ δ + x ^ δ / δ := by ring
  rw [Real.log_mul (by norm_num) hx0.ne', h5]
  linarith

/- English proof (translation)
Establish `hk' : (k : ℝ) ≠ 0` using `by exact_mod_cast hk.ne'`. Rewrite using `[← Real.rpow_mul_natCast hx.le, div_mul_cancel₀ ε hk', Real.rpow_neg hx.le]`.
-/
lemma rpow_neg_eq_inv_pow (x ε : ℝ) (hx : 0 < x) (k : ℕ) (hk : 0 < k) :
    x ^ (-ε) = ((x ^ (ε / k)) ^ k)⁻¹ := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [← Real.rpow_mul_natCast hx.le, div_mul_cancel₀ ε hk', Real.rpow_neg hx.le]

/- English proof (translation)
Unfold `ExcBoundOf ExcBound`. Introduce `hS hL ε hε`. Establish `hε3 : 0 < ε / 3` using `by linarith`. Take `⟨c0, hc0, hS'⟩` from `hS (ε / 3) hε3`. Take `⟨C, hC⟩` from `hL`.

Take `⟨K, hK, hKb⟩` from `log_le_const_mul_rpow (ε / 3) hε3`. Take `⟨M, hM, hCM⟩ : ∃ M : ℝ, 0 < M ∧ C ≤ M` from `⟨max C 1, lt_max_of_lt_right one_pos, le_max_left _ _⟩`. Establish `hcpos : 0 < min (1 / K) (c0 / (M * K ^ 2))` using `lt_min (div_pos one_pos hK) (div_pos hc0 (mul_pos hM (pow_pos hK 2)))`. Use `⟨min (1 / K) (c0 / (M * K ^ 2)), hcpos, ?_⟩` and prove the remaining obligations. Introduce `q _ χ β hχ2 hχ1 hβ`.

Establish `hcK : min (1 / K) (c0 / (M * K ^ 2)) ≤ 1 / K` using `min_le_left _ _`. Establish `hc2 : min (1 / K) (c0 / (M * K ^ 2)) ≤ c0 / (M * K ^ 2)` using `min_le_right _ _`. Generalize the expression as in `min (1 / K) (c0 / (M * K ^ 2)) = c at hcpos hcK hc2 ⊢`. Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)`. Establish `hq0 : (0 : ℝ) < q` using `by linarith`.

Establish `hu1 : 1 ≤ (q : ℝ) ^ (ε / 3)` using `Real.one_le_rpow hq1 hε3.le`. Establish `hqε : (q : ℝ) ^ (-ε) = (((q : ℝ) ^ (ε / 3)) ^ 3)⁻¹`. Establish `h` using `rpow_neg_eq_inv_pow (q : ℝ) ε hq0 3 (by norm_num)`. Simplify using `using h`. Establish `hq3 : (q : ℝ) ^ (-(ε / 3)) = ((q : ℝ) ^ (ε / 3))⁻¹` using `Real.rpow_neg hq0.le _`.

Establish `hlogK : Real.log (3 * q) ≤ K * (q : ℝ) ^ (ε / 3)` using `hKb q hq1`. Establish `hlog_pos : 0 < Real.log (3 * q)` using `Real.log_pos (by linarith)`. Establish `hβ1 : β < 1`. Assume the negation of the conclusion as `hge`. Simplify using `only [not_lt] at hge`.

Conclude with `DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by simpa using hge) hβ`. Establish `hlow` using `hS' q χ hχ2 hχ1`. Rewrite `hlow` using `[hq3]`. Rewrite using `[hqε]`. Generalize the expression as in `(q : ℝ) ^ (ε / 3) = u at hu1 hlogK hlow ⊢`.

Establish `hu0 : 0 < u` using `by linarith`. Distinguish the cases in `hcase : β ≤ 1 - 1 / Real.log (3 * q)`. Establish `key : c * Real.log (3 * q) ≤ u ^ 3`. Establish `hu3 : u ≤ u ^ 3` using `le_self_pow₀ hu1 (by norm_num)`. Combine the equalities or inequalities in the displayed calculation.

Establish `h1 : c * (u ^ 3)⁻¹ ≤ 1 / Real.log (3 * q)`. Rewrite using `[← div_eq_mul_inv, div_le_div_iff₀ (pow_pos hu0 3) hlog_pos, one_mul]`. Conclude with `key`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [not_le] at hcase`.

Establish `hdiff` using `DirichletCharacter.differentiable_LFunction hχ1`. Establish `hmvt : ‖(fun t : ℝ => DirichletCharacter.LFunction χ (t : ℂ)) 1 - (fun t : ℝ => DirichletCharacter.LFunction χ (t : ℂ)) β‖ ≤ (C * Real.log (3 * q) ^ 2) * (1 - β)`. Use `norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t : ℝ => DirichletCharacter.LFunction χ (t : ℂ)) (a := β) (b := 1) (f' := fun t : ℝ => deriv (DirichletCharacter.LFunction χ) (t : ℂ)) ?_ ?_ 1 ⟨hβ1.le, le_refl _⟩` and prove the remaining obligations. Introduce `t _`. Conclude with `((hdiff (t : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt`.

Introduce `t ht`. Conclude with `hC q χ hχ1 t (by linarith [ht.1]) ht.2.le`. Simplify using `only [hβ, sub_zero, Complex.ofReal_one] at hmvt`. Establish `h1β : 0 < 1 - β` using `by linarith`. Establish `hlog2 : Real.log (3 * q) ^ 2 ≤ (K * u) ^ 2` using `pow_le_pow_left₀ hlog_pos.le hlogK 2`.

Establish `hCle : C * Real.log (3 * q) ^ 2 ≤ M * (K * u) ^ 2` using `mul_le_mul hCM hlog2 (sq_nonneg _) hM.le`. Establish `hmain : c0 * u⁻¹ ≤ M * (K * u) ^ 2 * (1 - β)` using `le_trans hlow (le_trans hmvt (mul_le_mul_of_nonneg_right hCle h1β.le))`. Establish `hc0' : c0 ≤ M * K ^ 2 * u ^ 3 * (1 - β)`. Establish `h` using `mul_le_mul_of_nonneg_right hmain hu0.le`. Establish `e1 : c0 * u⁻¹ * u = c0` using `by field_simp`.

Establish `e2 : M * (K * u) ^ 2 * (1 - β) * u = M * K ^ 2 * u ^ 3 * (1 - β)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hMKu : 0 < M * K ^ 2 * u ^ 3` using `mul_pos (mul_pos hM (pow_pos hK 2)) (pow_pos hu0 3)`. Establish `hfin : c * (u ^ 3)⁻¹ ≤ 1 - β`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[div_le_iff₀ hMKu]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exceptional_zero_bound_of : ExcBoundOf := by
  unfold ExcBoundOf ExcBound
  intro hS hL ε hε
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨c0, hc0, hS'⟩ := hS (ε / 3) hε3
  obtain ⟨C, hC⟩ := hL
  obtain ⟨K, hK, hKb⟩ := log_le_const_mul_rpow (ε / 3) hε3
  obtain ⟨M, hM, hCM⟩ : ∃ M : ℝ, 0 < M ∧ C ≤ M := ⟨max C 1, lt_max_of_lt_right one_pos, le_max_left _ _⟩
  have hcpos : 0 < min (1 / K) (c0 / (M * K ^ 2)) :=
    lt_min (div_pos one_pos hK) (div_pos hc0 (mul_pos hM (pow_pos hK 2)))
  refine ⟨min (1 / K) (c0 / (M * K ^ 2)), hcpos, ?_⟩
  intro q _ χ β hχ2 hχ1 hβ
  have hcK : min (1 / K) (c0 / (M * K ^ 2)) ≤ 1 / K := min_le_left _ _
  have hc2 : min (1 / K) (c0 / (M * K ^ 2)) ≤ c0 / (M * K ^ 2) := min_le_right _ _
  generalize min (1 / K) (c0 / (M * K ^ 2)) = c at hcpos hcK hc2 ⊢
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hu1 : 1 ≤ (q : ℝ) ^ (ε / 3) := Real.one_le_rpow hq1 hε3.le
  have hqε : (q : ℝ) ^ (-ε) = (((q : ℝ) ^ (ε / 3)) ^ 3)⁻¹ := by
    have h := rpow_neg_eq_inv_pow (q : ℝ) ε hq0 3 (by norm_num)
    simpa using h
  have hq3 : (q : ℝ) ^ (-(ε / 3)) = ((q : ℝ) ^ (ε / 3))⁻¹ := Real.rpow_neg hq0.le _
  have hlogK : Real.log (3 * q) ≤ K * (q : ℝ) ^ (ε / 3) := hKb q hq1
  have hlog_pos : 0 < Real.log (3 * q) := Real.log_pos (by linarith)
  have hβ1 : β < 1 := by
    by_contra hge
    simp only [not_lt] at hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by simpa using hge) hβ
  have hlow := hS' q χ hχ2 hχ1
  rw [hq3] at hlow
  rw [hqε]
  generalize (q : ℝ) ^ (ε / 3) = u at hu1 hlogK hlow ⊢
  have hu0 : 0 < u := by linarith
  by_cases hcase : β ≤ 1 - 1 / Real.log (3 * q)
  · have key : c * Real.log (3 * q) ≤ u ^ 3 := by
      have hu3 : u ≤ u ^ 3 := le_self_pow₀ hu1 (by norm_num)
      calc c * Real.log (3 * q) ≤ (1 / K) * (K * u) :=
            mul_le_mul hcK hlogK hlog_pos.le (div_pos one_pos hK).le
        _ = u := by field_simp
        _ ≤ u ^ 3 := hu3
    have h1 : c * (u ^ 3)⁻¹ ≤ 1 / Real.log (3 * q) := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ (pow_pos hu0 3) hlog_pos, one_mul]
      exact key
    linarith
  · simp only [not_le] at hcase
    have hdiff := DirichletCharacter.differentiable_LFunction hχ1
    have hmvt : ‖(fun t : ℝ => DirichletCharacter.LFunction χ (t : ℂ)) 1 -
        (fun t : ℝ => DirichletCharacter.LFunction χ (t : ℂ)) β‖ ≤
        (C * Real.log (3 * q) ^ 2) * (1 - β) := by
      refine norm_image_sub_le_of_norm_deriv_le_segment'
        (f := fun t : ℝ => DirichletCharacter.LFunction χ (t : ℂ)) (a := β) (b := 1)
        (f' := fun t : ℝ => deriv (DirichletCharacter.LFunction χ) (t : ℂ)) ?_ ?_ 1 ⟨hβ1.le, le_refl _⟩
      · intro t _
        exact ((hdiff (t : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt
      · intro t ht
        exact hC q χ hχ1 t (by linarith [ht.1]) ht.2.le
    simp only [hβ, sub_zero, Complex.ofReal_one] at hmvt
    have h1β : 0 < 1 - β := by linarith
    have hlog2 : Real.log (3 * q) ^ 2 ≤ (K * u) ^ 2 := pow_le_pow_left₀ hlog_pos.le hlogK 2
    have hCle : C * Real.log (3 * q) ^ 2 ≤ M * (K * u) ^ 2 :=
      mul_le_mul hCM hlog2 (sq_nonneg _) hM.le
    have hmain : c0 * u⁻¹ ≤ M * (K * u) ^ 2 * (1 - β) :=
      le_trans hlow (le_trans hmvt (mul_le_mul_of_nonneg_right hCle h1β.le))
    have hc0' : c0 ≤ M * K ^ 2 * u ^ 3 * (1 - β) := by
      have h := mul_le_mul_of_nonneg_right hmain hu0.le
      have e1 : c0 * u⁻¹ * u = c0 := by field_simp
      have e2 : M * (K * u) ^ 2 * (1 - β) * u = M * K ^ 2 * u ^ 3 * (1 - β) := by ring
      linarith
    have hMKu : 0 < M * K ^ 2 * u ^ 3 := mul_pos (mul_pos hM (pow_pos hK 2)) (pow_pos hu0 3)
    have hfin : c * (u ^ 3)⁻¹ ≤ 1 - β := by
      calc c * (u ^ 3)⁻¹ ≤ c0 / (M * K ^ 2) * (u ^ 3)⁻¹ :=
            mul_le_mul_of_nonneg_right hc2 (inv_nonneg.2 (pow_pos hu0 3).le)
        _ = c0 / (M * K ^ 2 * u ^ 3) := by field_simp
        _ ≤ 1 - β := by
          rw [div_le_iff₀ hMKu]
          linarith
    linarith

end Formalism.ZeroFreeDirichlet
