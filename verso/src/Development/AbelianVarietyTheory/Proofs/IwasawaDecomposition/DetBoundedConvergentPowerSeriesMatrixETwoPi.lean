import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open Filter Topology

/- English proof (translation)
Establish `hlim : Tendsto (fun q : ℂ => ∑' m : ℕ, a m * q ^ m) (𝓝 0) (𝓝 (∑' m : ℕ, if m = 0 then a 0 else 0))`. Use `tendsto_tsum_of_dominated_convergence (bound := fun m => ‖a m * q₀ ^ m‖) hs.norm ?_ ?_` and prove the remaining obligations. Introduce `m`. Establish `hc : Continuous (fun q : ℂ => a m * q ^ m)` using `by fun_prop`. Establish `h` using `hc.tendsto 0`.

Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Simplify using `using h`. Establish `h0 : a m * (0 : ℂ) ^ m = 0` using `by simp [hm.ne']`. Rewrite `h` using `[h0]`. Simplify `h` using `[hm.ne']`.

Establish `hpos : 0 < ‖q₀‖` using `norm_pos_iff.mpr hq₀ filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hpos] with q hq m`. Establish `hq' : ‖q‖ ≤ ‖q₀‖`. Establish `: ‖q‖ < ‖q₀‖` using `by simpa using hq`. Conclude with `this.le`. Rewrite using `[norm_mul, norm_mul, norm_pow, norm_pow]`.

Use `gcongr`. Simplify using `using hlim`.
-/
theorem tendsto_tsum_coeff_mul_pow_zero (a : ℕ → ℂ) (q₀ : ℂ) (hq₀ : q₀ ≠ 0)
    (hs : Summable (fun m : ℕ => a m * q₀ ^ m)) :
    Tendsto (fun q : ℂ => ∑' m : ℕ, a m * q ^ m) (𝓝 0) (𝓝 (a 0)) := by
  have hlim : Tendsto (fun q : ℂ => ∑' m : ℕ, a m * q ^ m) (𝓝 0)
      (𝓝 (∑' m : ℕ, if m = 0 then a 0 else 0)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun m => ‖a m * q₀ ^ m‖) hs.norm ?_ ?_
    · intro m
      have hc : Continuous (fun q : ℂ => a m * q ^ m) := by fun_prop
      have h := hc.tendsto 0
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simpa using h
      · have h0 : a m * (0 : ℂ) ^ m = 0 := by simp [hm.ne']
        rw [h0] at h
        simpa [hm.ne'] using h
    · have hpos : 0 < ‖q₀‖ := norm_pos_iff.mpr hq₀
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hpos] with q hq m
      have hq' : ‖q‖ ≤ ‖q₀‖ := by
        have : ‖q‖ < ‖q₀‖ := by simpa using hq
        exact this.le
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
      gcongr
  simpa using hlim

/- English proof (translation)
Introduce `g A w₀ hdet hsum`. Establish `hq₀ : eTwoPi w₀ ≠ 0` using `Complex.exp_ne_zero _`. Use `set d₀ : ℂ := (A.map (PowerSeries.constantCoeff (R := ℂ))).det with hd₀`. Establish `hd₀eq : d₀ = PowerSeries.constantCoeff (R` using `ℂ) A.det := by`. Rewrite using `[RingHom.map_det]`.

Both sides reduce to the same expression. Establish `hd₀ne : d₀ ≠ 0`. Rewrite using `[hd₀eq]`. Conclude with `(hdet.map (PowerSeries.constantCoeff (R := ℂ))).ne_zero`. Establish `hmat : Tendsto (fun q : ℂ => (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * q ^ m : Matrix (Fin g) (Fin g) ℂ)) (𝓝 0) (𝓝 (A.map (PowerSeries.constantCoeff (R` using `ℂ)))) := by`.

Use `tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_` and prove the remaining obligations. Establish `h` using `tendsto_tsum_coeff_mul_pow_zero (fun m => PowerSeries.coeff m (A i j)) (eTwoPi w₀) hq₀ (hsum i j)`. Simplify using `using h`. Establish `hdetlim : Tendsto (fun q : ℂ => (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * q ^ m : Matrix (Fin g) (Fin g) ℂ).det) (𝓝 0) (𝓝 d₀)` using `((continuous_id.matrix_det).tendsto _).comp hmat`. Establish `hdpos : 0 < ‖d₀‖` using `norm_pos_iff.mpr hd₀ne`.

Take `⟨ε, hε, hball⟩` from `Metric.eventually_nhds_iff.mp (Metric.tendsto_nhds.mp hdetlim (‖d₀‖ / 2) (by positivity))`. Use `⟨-Real.log ε / (2 * Real.pi), 2 / ‖d₀‖ + 3 * ‖d₀‖ / 2 + 1, by positivity, ?_⟩` and prove the remaining obligations. Introduce `w hw`. Establish `hpi : 0 < 2 * Real.pi` using `by positivity`. Establish `hnorm : ‖eTwoPi w‖ < ε`.

Establish `hn : ‖eTwoPi w‖ = Real.exp (-(2 * Real.pi * w.im))`. Rewrite using `[eTwoPi, Complex.norm_exp]`. Use `congr 1`. Simplify using `[Complex.mul_re, Complex.mul_im]`. Rewrite using `[hn, ← Real.lt_log_iff_exp_lt hε]`.

Rewrite `hw` using `[div_lt_iff₀ hpi]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hclose` using `hball (y := eTwoPi w) (by simpa using hnorm)`. Rewrite `hclose` using `[dist_eq_norm]`. Use `set D : ℂ := (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m : Matrix (Fin g) (Fin g) ℂ).det with hD`.

Establish `hlow : ‖d₀‖ / 2 ≤ ‖D‖`. Use `norm_sub_norm_le d₀ D` as an intermediate fact. Rewrite `this` using `[norm_sub_rev]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hup : ‖D‖ ≤ 3 * ‖d₀‖ / 2`.

Use `norm_sub_norm_le D d₀` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : 0 < 2 / ‖d₀‖` using `by positivity`. Prove the components needed by the constructor for the conclusion. Use `le_trans ?_ hlow` and prove the remaining obligations.

Establish `hC : 2 / ‖d₀‖ ≤ 2 / ‖d₀‖ + 3 * ‖d₀‖ / 2 + 1`. Establish `: 0 ≤ 3 * ‖d₀‖ / 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Use `inv_anti₀ h2 hC` as an intermediate fact. Rewrite `this` using `[inv_div]`. Then use the resulting hypothesis.

Establish `: 0 < 2 / ‖d₀‖` using `h2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem det_bounded_eTwoPi : ∀ (g : ℕ) (A : Matrix (Fin g) (Fin g) (PowerSeries ℂ)) (w₀ : ℂ),
    IsUnit A.det → (∀ i j, Summable (fun m : ℕ => PowerSeries.coeff m (A i j) * eTwoPi w₀ ^ m)) →
    ∃ T' C : ℝ, 0 < C ∧ ∀ w : ℂ, T' < w.im →
      C⁻¹ ≤ ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ∧
      ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ≤ C := by
  intro g A w₀ hdet hsum
  have hq₀ : eTwoPi w₀ ≠ 0 := Complex.exp_ne_zero _
  set d₀ : ℂ := (A.map (PowerSeries.constantCoeff (R := ℂ))).det with hd₀
  have hd₀eq : d₀ = PowerSeries.constantCoeff (R := ℂ) A.det := by
    rw [RingHom.map_det]
    rfl
  have hd₀ne : d₀ ≠ 0 := by
    rw [hd₀eq]
    exact (hdet.map (PowerSeries.constantCoeff (R := ℂ))).ne_zero
  have hmat : Tendsto
      (fun q : ℂ => (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * q ^ m :
        Matrix (Fin g) (Fin g) ℂ)) (𝓝 0) (𝓝 (A.map (PowerSeries.constantCoeff (R := ℂ)))) := by
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
    have h := tendsto_tsum_coeff_mul_pow_zero (fun m => PowerSeries.coeff m (A i j))
      (eTwoPi w₀) hq₀ (hsum i j)
    simpa using h
  have hdetlim : Tendsto
      (fun q : ℂ => (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * q ^ m :
        Matrix (Fin g) (Fin g) ℂ).det) (𝓝 0) (𝓝 d₀) :=
    ((continuous_id.matrix_det).tendsto _).comp hmat
  have hdpos : 0 < ‖d₀‖ := norm_pos_iff.mpr hd₀ne
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hdetlim (‖d₀‖ / 2) (by positivity))
  refine ⟨-Real.log ε / (2 * Real.pi), 2 / ‖d₀‖ + 3 * ‖d₀‖ / 2 + 1, by positivity, ?_⟩
  intro w hw
  have hpi : 0 < 2 * Real.pi := by positivity
  have hnorm : ‖eTwoPi w‖ < ε := by
    have hn : ‖eTwoPi w‖ = Real.exp (-(2 * Real.pi * w.im)) := by
      rw [eTwoPi, Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.mul_im]
    rw [hn, ← Real.lt_log_iff_exp_lt hε]
    rw [div_lt_iff₀ hpi] at hw
    linarith
  have hclose := hball (y := eTwoPi w) (by simpa using hnorm)
  rw [dist_eq_norm] at hclose
  set D : ℂ := (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m :
    Matrix (Fin g) (Fin g) ℂ).det with hD
  have hlow : ‖d₀‖ / 2 ≤ ‖D‖ := by
    have := norm_sub_norm_le d₀ D
    rw [norm_sub_rev] at this
    linarith
  have hup : ‖D‖ ≤ 3 * ‖d₀‖ / 2 := by
    have := norm_sub_norm_le D d₀
    linarith
  have h2 : 0 < 2 / ‖d₀‖ := by positivity
  constructor
  · refine le_trans ?_ hlow
    have hC : 2 / ‖d₀‖ ≤ 2 / ‖d₀‖ + 3 * ‖d₀‖ / 2 + 1 := by
      have : 0 ≤ 3 * ‖d₀‖ / 2 := by positivity
      linarith
    have := inv_anti₀ h2 hC
    rwa [inv_div] at this
  · have : 0 < 2 / ‖d₀‖ := h2
    linarith

end GlobalTheory
