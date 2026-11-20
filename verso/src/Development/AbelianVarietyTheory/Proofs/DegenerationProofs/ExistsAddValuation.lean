import Mathlib

namespace GlobalTheory.PadicVal

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Establish `hint : IsIntegral ℚ_[p] x` using `Algebra.IsIntegral.isIntegral x`. Establish `hc : (minpoly ℚ_[p] x).coeff 0 ≠ 0` using `minpoly.coeff_zero_ne_zero hint hx`. Establish `hn : ‖x‖ = ‖(minpoly ℚ_[p] x).coeff 0‖ ^ (1 / (minpoly ℚ_[p] x).natDegree : ℝ)`. Rewrite using `[← PadicAlgCl.spectralNorm_eq]`. Conclude with `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[p] (PadicAlgCl p) x`.

Use `⟨((-((minpoly ℚ_[p] x).coeff 0).valuation : ℤ) : ℚ) / ((minpoly ℚ_[p] x).natDegree : ℚ), ?_⟩` and prove the remaining obligations. Rewrite using `[hn, Real.log_rpow (norm_pos_iff.2 hc), Padic.norm_eq_zpow_neg_valuation hc, Real.log_zpow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_rat_log (x : PadicAlgCl p) (hx : x ≠ 0) : ∃ q : ℚ, Real.log ‖x‖ = q * Real.log p := by
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  have hc : (minpoly ℚ_[p] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx
  have hn : ‖x‖ = ‖(minpoly ℚ_[p] x).coeff 0‖ ^ (1 / (minpoly ℚ_[p] x).natDegree : ℝ) := by
    rw [← PadicAlgCl.spectralNorm_eq]
    exact spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[p] (PadicAlgCl p) x
  refine ⟨((-((minpoly ℚ_[p] x).coeff 0).valuation : ℤ) : ℚ) / ((minpoly ℚ_[p] x).natDegree : ℚ), ?_⟩
  rw [hn, Real.log_rpow (norm_pos_iff.2 hc), Padic.norm_eq_zpow_neg_valuation hc, Real.log_zpow]
  push_cast
  ring

open Classical in

/- English proof (translation)
Establish `hL : Real.log ‖π‖ < 0` using `Real.log_neg h0 h1`. Establish `hex : ∀ x : PadicAlgCl p, x ≠ 0 → ∃ q : ℚ, Real.log ‖x‖ = q * Real.log ‖π‖`. Introduce `x hx`. Take `⟨a, ha⟩` from `exists_rat_log x hx`. Take `⟨b, hb⟩` from `exists_rat_log π (norm_pos_iff.1 h0)`.

Establish `hb0 : (b : ℝ) ≠ 0`. Introduce `h`. Rewrite `hb` using `[h, zero_mul]`. Conclude with `hL.ne hb`. Establish `hlp : Real.log p ≠ 0`.

Introduce `h`. Rewrite `hb` using `[h, mul_zero]`. Conclude with `hL.ne hb`. Use `⟨a / b, ?_⟩` and prove the remaining obligations. Rewrite using `[ha, hb]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Set `r : PadicAlgCl p → ℚ` to `fun x => if hx : x = 0 then 0 else Classical.choose (hex x hx)`. Establish `hr : ∀ x, x ≠ 0 → Real.log ‖x‖ = r x * Real.log ‖π‖`. Introduce `x hx`.

Simplify using `only [r, dif_neg hx]`. Conclude with `Classical.choose_spec (hex x hx)`. Establish `hr' : ∀ x, x ≠ 0 → (r x : ℝ) = Real.log ‖x‖ / Real.log ‖π‖`. Introduce `x hx`. Rewrite using `[hr x hx, mul_div_cancel_right₀ _ hL.ne]`.

Set `f : PadicAlgCl p → WithTop ℚ` to `fun x => if x = 0 then ⊤ else (r x : WithTop ℚ)`. Establish `f_ne : ∀ x, x ≠ 0 → f x = (r x : WithTop ℚ)` using `fun x hx => if_neg hx`. Establish `f_zero : f 0 = ⊤` using `if_pos rfl`. Use `⟨AddValuation.of f f_zero ?_ ?_ ?_, ?_⟩` and prove the remaining obligations. Establish `h : (r 1 : ℝ) = 0`.

Rewrite using `[hr' 1 one_ne_zero, norm_one, Real.log_one, zero_div]`. Rewrite using `[f_ne 1 one_ne_zero, Rat.cast_eq_zero.1 h]`. Both sides reduce to the same expression. Introduce `x y`. Distinguish the cases in `hx : x = 0`.

Substitute `hx` using the available equality. Rewrite using `[f_zero, zero_add]`. Conclude with `min_le_right _ _`. Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality.

Rewrite using `[f_zero, add_zero]`. Conclude with `min_le_left _ _`. Distinguish the cases in `hxy : x + y = 0`. Rewrite using `[hxy, f_zero]`. Conclude with `le_top`.

Rewrite using `[f_ne x hx, f_ne y hy, f_ne _ hxy, ← WithTop.coe_min, WithTop.coe_le_coe, ← Rat.cast_le (K := ℝ), Rat.cast_min, hr' x hx, hr' y hy, hr' _ hxy]`. Establish `hle : ‖x + y‖ ≤ max ‖x‖ ‖y‖` using `IsUltrametricDist.norm_add_le_max x y`. Establish `hpos : 0 < ‖x + y‖` using `norm_pos_iff.2 hxy`. Break down `le_total ‖y‖ ‖x‖ with h | h` into its components or cases. Rewrite `hle` using `[max_eq_left h]`.

Conclude with `(min_le_left _ _).trans (div_le_div_of_nonpos_of_le hL.le (Real.log_le_log hpos hle))`. Rewrite `hle` using `[max_eq_right h]`. Conclude with `(min_le_right _ _).trans (div_le_div_of_nonpos_of_le hL.le (Real.log_le_log hpos hle))`. Introduce `x y`. Distinguish the cases in `hx : x = 0`.

Substitute `hx` using the available equality. Rewrite using `[zero_mul, f_zero, top_add]`. Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality. Rewrite using `[mul_zero, f_zero, add_top]`.

Establish `hxy : x * y ≠ 0` using `mul_ne_zero hx hy`. Rewrite using `[f_ne x hx, f_ne y hy, f_ne _ hxy, ← WithTop.coe_add, WithTop.coe_eq_coe]`. Establish `h : (r (x * y) : ℝ) = r x + r y`. Rewrite using `[hr' _ hxy, hr' x hx, hr' y hy, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy), add_div]`. Conclude with `h` after adjusting the coercions.

Introduce `x hx`. Conclude with `⟨r x, f_ne x hx, hr x hx⟩`.
-/
theorem exists_addValuation (π : PadicAlgCl p) (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1) :
    ∃ v : AddValuation (PadicAlgCl p) (WithTop ℚ), ∀ x, x ≠ 0 →
      ∃ q : ℚ, v x = (q : WithTop ℚ) ∧ Real.log ‖x‖ = q * Real.log ‖π‖ := by
  have hL : Real.log ‖π‖ < 0 := Real.log_neg h0 h1
  have hex : ∀ x : PadicAlgCl p, x ≠ 0 → ∃ q : ℚ, Real.log ‖x‖ = q * Real.log ‖π‖ := by
    intro x hx
    obtain ⟨a, ha⟩ := exists_rat_log x hx
    obtain ⟨b, hb⟩ := exists_rat_log π (norm_pos_iff.1 h0)
    have hb0 : (b : ℝ) ≠ 0 := by
      intro h
      rw [h, zero_mul] at hb
      exact hL.ne hb
    have hlp : Real.log p ≠ 0 := by
      intro h
      rw [h, mul_zero] at hb
      exact hL.ne hb
    refine ⟨a / b, ?_⟩
    rw [ha, hb]
    push_cast
    field_simp
  let r : PadicAlgCl p → ℚ := fun x => if hx : x = 0 then 0 else Classical.choose (hex x hx)
  have hr : ∀ x, x ≠ 0 → Real.log ‖x‖ = r x * Real.log ‖π‖ := by
    intro x hx
    simp only [r, dif_neg hx]
    exact Classical.choose_spec (hex x hx)
  have hr' : ∀ x, x ≠ 0 → (r x : ℝ) = Real.log ‖x‖ / Real.log ‖π‖ := by
    intro x hx
    rw [hr x hx, mul_div_cancel_right₀ _ hL.ne]
  let f : PadicAlgCl p → WithTop ℚ := fun x => if x = 0 then ⊤ else (r x : WithTop ℚ)
  have f_ne : ∀ x, x ≠ 0 → f x = (r x : WithTop ℚ) := fun x hx => if_neg hx
  have f_zero : f 0 = ⊤ := if_pos rfl
  refine ⟨AddValuation.of f f_zero ?_ ?_ ?_, ?_⟩
  · have h : (r 1 : ℝ) = 0 := by
      rw [hr' 1 one_ne_zero, norm_one, Real.log_one, zero_div]
    rw [f_ne 1 one_ne_zero, Rat.cast_eq_zero.1 h]
    rfl
  · intro x y
    by_cases hx : x = 0
    · subst hx
      rw [f_zero, zero_add]
      exact min_le_right _ _
    by_cases hy : y = 0
    · subst hy
      rw [f_zero, add_zero]
      exact min_le_left _ _
    by_cases hxy : x + y = 0
    · rw [hxy, f_zero]
      exact le_top
    rw [f_ne x hx, f_ne y hy, f_ne _ hxy, ← WithTop.coe_min, WithTop.coe_le_coe,
      ← Rat.cast_le (K := ℝ), Rat.cast_min, hr' x hx, hr' y hy, hr' _ hxy]
    have hle : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := IsUltrametricDist.norm_add_le_max x y
    have hpos : 0 < ‖x + y‖ := norm_pos_iff.2 hxy
    rcases le_total ‖y‖ ‖x‖ with h | h
    · rw [max_eq_left h] at hle
      exact (min_le_left _ _).trans
        (div_le_div_of_nonpos_of_le hL.le (Real.log_le_log hpos hle))
    · rw [max_eq_right h] at hle
      exact (min_le_right _ _).trans
        (div_le_div_of_nonpos_of_le hL.le (Real.log_le_log hpos hle))
  · intro x y
    by_cases hx : x = 0
    · subst hx
      rw [zero_mul, f_zero, top_add]
    by_cases hy : y = 0
    · subst hy
      rw [mul_zero, f_zero, add_top]
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    rw [f_ne x hx, f_ne y hy, f_ne _ hxy, ← WithTop.coe_add, WithTop.coe_eq_coe]
    have h : (r (x * y) : ℝ) = r x + r y := by
      rw [hr' _ hxy, hr' x hx, hr' y hy, norm_mul,
        Real.log_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy), add_div]
    exact_mod_cast h
  · intro x hx
    exact ⟨r x, f_ne x hx, hr x hx⟩

/- English proof (translation)
Establish `hL : Real.log ‖π‖ < 0` using `Real.log_neg h0 h1`. Rewrite using `[tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]`. Introduce `ε hε`. Take `⟨q, hq⟩` from `exists_rat_gt (Real.log ε / Real.log ‖π‖)`. Rewrite using `[Filter.eventually_cofinite]`.

Use `(hx q).subset ?_` and prove the remaining obligations. Introduce `i hi`. Simplify using `only [Set.mem_ofPred_eq] at hi ⊢`. Assume the negation of the conclusion as `hlt`. Apply `hi` to reduce the goal to its premises.

Rewrite using `[dist_zero_right, norm_norm]`. Distinguish the cases in `hxi : x i = 0`. Rewrite using `[hxi, norm_zero]`. Conclude with `hε`. Take `⟨q', hv', hlog⟩` from `hv (x i) hxi`.

Establish `hqq : q ≤ q'`. Rewrite `hlt` using `[hv', not_lt, WithTop.coe_le_coe]`. Conclude with `hlt`. Establish `h2 : (q' : ℝ) * Real.log ‖π‖ ≤ q * Real.log ‖π‖` using `mul_le_mul_of_nonpos_right (by exact_mod_cast hqq) hL.le`. Establish `h3 : (q : ℝ) * Real.log ‖π‖ < Real.log ε` using `(div_lt_iff_of_neg hL).1 hq`.

Establish `h4 : Real.log ‖x i‖ < Real.log ε` using `by linarith`. Conclude with `(Real.log_lt_log_iff (norm_pos_iff.2 hxi) hε).1 h4`.
-/
theorem tendsto_of_null {π : PadicAlgCl p} (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1)
    {v : AddValuation (PadicAlgCl p) (WithTop ℚ)}
    (hv : ∀ x, x ≠ 0 → ∃ q : ℚ, v x = (q : WithTop ℚ) ∧ Real.log ‖x‖ = q * Real.log ‖π‖)
    {I : Type} {x : I → PadicAlgCl p} (hx : ∀ q : ℚ, {i | v (x i) < (q : WithTop ℚ)}.Finite) :
    Filter.Tendsto x Filter.cofinite (nhds 0) := by
  have hL : Real.log ‖π‖ < 0 := Real.log_neg h0 h1
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨q, hq⟩ := exists_rat_gt (Real.log ε / Real.log ‖π‖)
  rw [Filter.eventually_cofinite]
  refine (hx q).subset ?_
  intro i hi
  simp only [Set.mem_ofPred_eq] at hi ⊢
  by_contra hlt
  apply hi
  rw [dist_zero_right, norm_norm]
  by_cases hxi : x i = 0
  · rw [hxi, norm_zero]
    exact hε
  obtain ⟨q', hv', hlog⟩ := hv (x i) hxi
  have hqq : q ≤ q' := by
    rw [hv', not_lt, WithTop.coe_le_coe] at hlt
    exact hlt
  have h2 : (q' : ℝ) * Real.log ‖π‖ ≤ q * Real.log ‖π‖ :=
    mul_le_mul_of_nonpos_right (by exact_mod_cast hqq) hL.le
  have h3 : (q : ℝ) * Real.log ‖π‖ < Real.log ε := (div_lt_iff_of_neg hL).1 hq
  have h4 : Real.log ‖x i‖ < Real.log ε := by linarith
  exact (Real.log_lt_log_iff (norm_pos_iff.2 hxi) hε).1 h4

/- English proof (translation)
Establish `: CompleteSpace K` using `FiniteDimensional.complete ℚ_[p] K`. Set `y : I → K` to `fun i => ⟨x i, hK i⟩`. Establish `hy : Filter.Tendsto y Filter.cofinite (nhds 0)`. Rewrite using `[tendsto_subtype_rng]`. Conclude with `hx`.

Establish `hs : Summable y` using `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hy`. Conclude with `hs.map K.val continuous_subtype_val`.
-/
theorem summable_of_mem (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {I : Type} {x : I → PadicAlgCl p} (hK : ∀ i, x i ∈ K) (hx : Filter.Tendsto x Filter.cofinite (nhds 0)) :
    Summable x := by
  have : CompleteSpace K := FiniteDimensional.complete ℚ_[p] K
  let y : I → K := fun i => ⟨x i, hK i⟩
  have hy : Filter.Tendsto y Filter.cofinite (nhds 0) := by
    rw [tendsto_subtype_rng]
    exact hx
  have hs : Summable y := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hy
  exact hs.map K.val continuous_subtype_val

end GlobalTheory.PadicVal
