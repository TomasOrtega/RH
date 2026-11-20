import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

/- English proof (translation)
Rewrite using `[MeasureTheory.volume_pi_pi]`. Simplify using `[Real.volume_Ioc]`.
-/
theorem fourBasic_cube_vol (f : ℕ) :
    volume (Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1)) = 1 := by
  rw [MeasureTheory.volume_pi_pi]; simp [Real.volume_Ioc]

/- English proof (translation)
Establish `hsplit : (∑ k, (ν k : ℂ) * ((x k : ℂ) + (b k : ℂ) * Complex.I)) = ((∑ k, (ν k : ℝ) * x k : ℝ) : ℂ) + ((∑ k, (ν k : ℝ) * b k : ℝ) : ℂ) * Complex.I`. Use `push_cast`. Rewrite using `[Finset.sum_mul, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`. Establish `harg : -2 * Real.pi * Complex.I * (∑ k, (ν k : ℂ) * ((x k : ℂ) + (b k : ℂ) * Complex.I)) = ((2 * Real.pi * ∑ k, (ν k : ℝ) * b k : ℝ) : ℂ) + ((-2 * Real.pi * ∑ k, (ν k : ℝ) * x k : ℝ) : ℂ) * Complex.I`.

Rewrite using `[hsplit]`. Use `push_cast`. Take the linear combination `(-2 * (Real.pi : ℂ) * ∑ k, (ν k : ℂ) * (b k : ℂ)) * Complex.I_sq`. Rewrite using `[harg, Complex.norm_exp]`. Use `congr 1`.

Simplify using the standard rewrite rules.
-/
theorem fourBasic_norm_exp {f : ℕ} (ν : Fin f → ℤ) (x b : Fin f → ℝ) :
    ‖Complex.exp (-2 * Real.pi * Complex.I *
        ∑ k, (ν k : ℂ) * ((x k : ℂ) + (b k : ℂ) * Complex.I))‖ =
      Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k) := by
  have hsplit : (∑ k, (ν k : ℂ) * ((x k : ℂ) + (b k : ℂ) * Complex.I)) =
      ((∑ k, (ν k : ℝ) * x k : ℝ) : ℂ) + ((∑ k, (ν k : ℝ) * b k : ℝ) : ℂ) * Complex.I := by
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have harg : -2 * Real.pi * Complex.I *
        (∑ k, (ν k : ℂ) * ((x k : ℂ) + (b k : ℂ) * Complex.I)) =
      ((2 * Real.pi * ∑ k, (ν k : ℝ) * b k : ℝ) : ℂ) +
        ((-2 * Real.pi * ∑ k, (ν k : ℝ) * x k : ℝ) : ℂ) * Complex.I := by
    rw [hsplit]
    push_cast
    linear_combination (-2 * (Real.pi : ℂ) * ∑ k, (ν k : ℂ) * (b k : ℂ)) * Complex.I_sq
  rw [harg, Complex.norm_exp]
  congr 1
  simp

/- English proof (translation)
Introduce `h b ν C hC`. Establish `hint_r : ‖fourCoeff h b ν‖ ≤ C * Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k)`. Unfold `fourCoeff`. Establish `: IsFiniteMeasure (volume.restrict (Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1)))` using `⟨by rw [Measure.restrict_apply_univ, fourBasic_cube_vol]; exact ENNReal.one_lt_top⟩`. Establish `hle` using `norm_integral_le_of_norm_le_const (μ := volume.restrict (Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1))) (f := fun x : Fin f → ℝ => h (fun k => (x k : ℂ) + (b k : ℂ) * Complex.I) * Complex.exp (-2 * Real.pi * Complex.I * ∑ k, (ν k : ℂ) * ((x k : ℂ) + (b k : ℂ) * Complex.I))) ( …`.

Rewrite using `[norm_mul, fourBasic_norm_exp]`. Conclude with `mul_le_mul_of_nonneg_right (hC x) (Real.exp_pos _).le)`. Simplify `hle` using `[Measure.real, Measure.restrict_apply_univ, fourBasic_cube_vol]`. Establish `h1 : Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k) * Real.exp (-2 * Real.pi * ∑ k, (ν k : ℝ) * b k) = 1`. Rewrite using `[← Real.exp_add]`.

Rewrite using `[show 2 * Real.pi * ∑ k, (ν k : ℝ) * b k + -2 * Real.pi * ∑ k, (ν k : ℝ) * b k = 0 by ring]`. Conclude with `Real.exp_zero`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem four_bound (f : ℕ) : FOURBoundStatement f := by
  intro h b ν C hC
  have hint_r : ‖fourCoeff h b ν‖ ≤ C * Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k) := by
    unfold fourCoeff
    have : IsFiniteMeasure
        (volume.restrict (Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1))) :=
      ⟨by rw [Measure.restrict_apply_univ, fourBasic_cube_vol]; exact ENNReal.one_lt_top⟩
    have hle := norm_integral_le_of_norm_le_const
      (μ := volume.restrict (Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1)))
      (f := fun x : Fin f → ℝ => h (fun k => (x k : ℂ) + (b k : ℂ) * Complex.I) *
        Complex.exp (-2 * Real.pi * Complex.I *
          ∑ k, (ν k : ℂ) * ((x k : ℂ) + (b k : ℂ) * Complex.I)))
      (C := C * Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k))
      (ae_of_all _ fun x => by
        rw [norm_mul, fourBasic_norm_exp]
        exact mul_le_mul_of_nonneg_right (hC x) (Real.exp_pos _).le)
    simpa [Measure.real, Measure.restrict_apply_univ, fourBasic_cube_vol] using hle
  have h1 : Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k) *
      Real.exp (-2 * Real.pi * ∑ k, (ν k : ℝ) * b k) = 1 := by
    rw [← Real.exp_add]
    rw [show 2 * Real.pi * ∑ k, (ν k : ℝ) * b k + -2 * Real.pi * ∑ k, (ν k : ℝ) * b k = 0 by ring]
    exact Real.exp_zero
  calc ‖fourCoeff h b ν‖ * Real.exp (-2 * Real.pi * ∑ k, (ν k : ℝ) * b k)
      ≤ C * Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k) *
          Real.exp (-2 * Real.pi * ∑ k, (ν k : ℝ) * b k) :=
        mul_le_mul_of_nonneg_right hint_r (Real.exp_pos _).le
    _ = C := by rw [mul_assoc, h1, mul_one]

/- English proof (translation)
Introduce `Ω h b0 κ C E hΩ hpre hd hper hray hgrowth ν hne`. Assume the negation of the conclusion as `hneg0`. Establish `hneg` using `not_le.mp hneg0`. Take `⟨S0, hS0⟩ : ∃ S : ℝ, S = ∑ k, (ν k : ℝ) * b0 k` from `⟨_, rfl⟩`. Take `⟨Sκ, hSκ⟩ : ∃ S : ℝ, S = ∑ k, (ν k : ℝ) * κ k` from `⟨_, rfl⟩`.

Rewrite `hneg` using `[← hSκ]`. Establish `hb0 : b0 ∈ Ω` using `by simpa using hray 0 le_rfl`. Establish `hsum : ∀ t : ℝ, ∑ k, (ν k : ℝ) * (b0 + t • κ) k = S0 + t * Sκ`. Introduce `t`. Rewrite using `[hS0, hSκ, Finset.mul_sum, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun k _ => by`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨β, hβ⟩ : ∃ β : ℝ, β = -2 * Real.pi * Sκ` from `⟨_, rfl⟩`. Establish `hβpos : 0 < β`.

Rewrite using `[hβ]`. Use polynomial arithmetic with `[mul_pos Real.pi_pos (neg_pos.mpr hneg)]`. Establish `hK : 0 < ‖fourCoeff h b0 ν‖ * Real.exp (-2 * Real.pi * S0)` using `mul_pos (norm_pos_iff.mpr hne) (Real.exp_pos _)`. Establish `hle : ∀ t : ℝ, 0 ≤ t → ‖fourCoeff h b0 ν‖ * Real.exp (-2 * Real.pi * S0) ≤ C * ((1 + t) ^ E * Real.exp (-β * t))`. Introduce `t ht`.

Establish `hcoef` using `hI Ω h hΩ hpre hd hper b0 hb0 (b0 + t • κ) (hray t ht) ν`. Establish `hbd` using `hB h (b0 + t • κ) ν (C * (1 + t) ^ E) (hgrowth t ht)`. Rewrite `hbd` using `[← hcoef, hsum t]`. Establish `hexp : Real.exp (-2 * Real.pi * (S0 + t * Sκ)) = Real.exp (-2 * Real.pi * S0) * Real.exp (β * t)`. Rewrite using `[← Real.exp_add, hβ]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hbd` using `[hexp]`. Establish `h1 : Real.exp (β * t) * Real.exp (-β * t) = 1`. Rewrite using `[← Real.exp_add, show β * t + -β * t = 0 by ring, Real.exp_zero]`.

Combine the equalities or inequalities in the displayed calculation. Take the linear combination `(-(‖fourCoeff h b0 ν‖ * Real.exp (-2 * Real.pi * S0))) * h1`. Use `_ ≤ C * (1 + t) ^ E * Real.exp (-β * t) := mul_le_mul_of_nonneg_right hbd (Real.exp_pos _).le`. Use `_ = C * ((1 + t) ^ E * Real.exp (-β * t)) := by ring`. Establish `hlim : Tendsto (fun t : ℝ => C * ((1 + t) ^ E * Real.exp (-β * t))) atTop (𝓝 0)`.

Establish `h1` using `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero E β hβpos`. Establish `h2 : Tendsto (fun t : ℝ => 1 + t) atTop atTop` using `tendsto_atTop_mono (fun t => le_add_of_nonneg_left zero_le_one) tendsto_id`. Establish `h3` using `(h1.comp h2).const_mul (Real.exp β)`. Rewrite `h3` using `[mul_zero]`. Establish `h4 : Tendsto (fun t : ℝ => (1 + t) ^ E * Real.exp (-β * t)) atTop (𝓝 0)`.

Use `h3.congr fun t => ?_` and prove the remaining obligations. Establish `he : Real.exp β * Real.exp (-β * (1 + t)) = Real.exp (-β * t)`. Rewrite using `[← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Use `show Real.exp β * ((1 + t) ^ E * Real.exp (-β * (1 + t))) = _`. Rewrite using `[← he]`. Expand and normalize the polynomial expressions, which then agree. Establish `h5` using `h4.const_mul C`. Rewrite `h5` using `[mul_zero]`. Then use the resulting hypothesis.

Establish `hfin` using `ge_of_tendsto hlim ((eventually_ge_atTop (0 : ℝ)).mono fun t ht => hle t ht)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem four_sign (f : ℕ) (hI : FOURIndepStatement f) (hB : FOURBoundStatement f) :
    FOURSignStatement f := by
  intro Ω h b0 κ C E hΩ hpre hd hper hray hgrowth ν hne
  by_contra hneg0
  have hneg := not_le.mp hneg0
  obtain ⟨S0, hS0⟩ : ∃ S : ℝ, S = ∑ k, (ν k : ℝ) * b0 k := ⟨_, rfl⟩
  obtain ⟨Sκ, hSκ⟩ : ∃ S : ℝ, S = ∑ k, (ν k : ℝ) * κ k := ⟨_, rfl⟩
  rw [← hSκ] at hneg
  have hb0 : b0 ∈ Ω := by simpa using hray 0 le_rfl
  have hsum : ∀ t : ℝ, ∑ k, (ν k : ℝ) * (b0 + t • κ) k = S0 + t * Sκ := by
    intro t
    rw [hS0, hSκ, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = -2 * Real.pi * Sκ := ⟨_, rfl⟩
  have hβpos : 0 < β := by
    rw [hβ]; nlinarith [mul_pos Real.pi_pos (neg_pos.mpr hneg)]
  have hK : 0 < ‖fourCoeff h b0 ν‖ * Real.exp (-2 * Real.pi * S0) :=
    mul_pos (norm_pos_iff.mpr hne) (Real.exp_pos _)
  have hle : ∀ t : ℝ, 0 ≤ t → ‖fourCoeff h b0 ν‖ * Real.exp (-2 * Real.pi * S0) ≤
      C * ((1 + t) ^ E * Real.exp (-β * t)) := by
    intro t ht
    have hcoef := hI Ω h hΩ hpre hd hper b0 hb0 (b0 + t • κ) (hray t ht) ν
    have hbd := hB h (b0 + t • κ) ν (C * (1 + t) ^ E) (hgrowth t ht)
    rw [← hcoef, hsum t] at hbd
    have hexp : Real.exp (-2 * Real.pi * (S0 + t * Sκ)) =
        Real.exp (-2 * Real.pi * S0) * Real.exp (β * t) := by
      rw [← Real.exp_add, hβ]; congr 1; ring
    rw [hexp] at hbd
    have h1 : Real.exp (β * t) * Real.exp (-β * t) = 1 := by
      rw [← Real.exp_add, show β * t + -β * t = 0 by ring, Real.exp_zero]
    calc ‖fourCoeff h b0 ν‖ * Real.exp (-2 * Real.pi * S0)
        = ‖fourCoeff h b0 ν‖ * (Real.exp (-2 * Real.pi * S0) * Real.exp (β * t)) *
            Real.exp (-β * t) := by
          linear_combination (-(‖fourCoeff h b0 ν‖ * Real.exp (-2 * Real.pi * S0))) * h1
      _ ≤ C * (1 + t) ^ E * Real.exp (-β * t) :=
          mul_le_mul_of_nonneg_right hbd (Real.exp_pos _).le
      _ = C * ((1 + t) ^ E * Real.exp (-β * t)) := by ring
  have hlim : Tendsto (fun t : ℝ => C * ((1 + t) ^ E * Real.exp (-β * t))) atTop (𝓝 0) := by
    have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero E β hβpos
    have h2 : Tendsto (fun t : ℝ => 1 + t) atTop atTop :=
      tendsto_atTop_mono (fun t => le_add_of_nonneg_left zero_le_one) tendsto_id
    have h3 := (h1.comp h2).const_mul (Real.exp β)
    rw [mul_zero] at h3
    have h4 : Tendsto (fun t : ℝ => (1 + t) ^ E * Real.exp (-β * t)) atTop (𝓝 0) := by
      refine h3.congr fun t => ?_
      have he : Real.exp β * Real.exp (-β * (1 + t)) = Real.exp (-β * t) := by
        rw [← Real.exp_add]; congr 1; ring
      show Real.exp β * ((1 + t) ^ E * Real.exp (-β * (1 + t))) = _
      rw [← he]; ring
    have h5 := h4.const_mul C
    rwa [mul_zero] at h5
  have hfin := ge_of_tendsto hlim ((eventually_ge_atTop (0 : ℝ)).mono fun t ht => hle t ht)
  linarith

end

end ReciprocityTheory.L2DbarEstimates.Y
