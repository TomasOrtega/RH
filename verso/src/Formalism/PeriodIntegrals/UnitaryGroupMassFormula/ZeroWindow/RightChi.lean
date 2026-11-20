import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.RightHalfWith

noncomputable section

open Metric Complex

namespace PI.ZW

/- English proof (translation)
Establish `hX0 : 0 < X` using `by linarith`. Establish `h256 : Real.log 256 = 8 * Real.log 2`. Rewrite using `[show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]`. Evaluate the numerical expressions. Establish `h170 : Real.log 170 ≤ Real.log 256` using `Real.log_le_log (by norm_num) (by norm_num)`.

Establish `h2 : Real.log 2 ≤ Real.log X` using `Real.log_le_log (by norm_num) hX`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma log_le_nine (X M' : ℝ) (hX : 2 ≤ X) (hM : 0 < M') (h : M' ≤ 170 * X) :
    Real.log M' ≤ 9 * Real.log X := by
  have hX0 : 0 < X := by linarith
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    norm_num
  have h170 : Real.log 170 ≤ Real.log 256 := Real.log_le_log (by norm_num) (by norm_num)
  have h2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  calc Real.log M' ≤ Real.log (170 * X) := Real.log_le_log hM h
    _ = Real.log 170 + Real.log X := Real.log_mul (by norm_num) hX0.ne'
    _ ≤ 9 * Real.log X := by linarith

/- English proof (translation)
Rewrite using `[Metric.mem_closedBall, dist_eq_norm]`. Establish `hsq : ‖ρ - (2 + t * I)‖ ^ 2 ≤ (37 / 20) ^ 2`. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Simplify using the standard rewrite rules. Establish `h4` using `abs_le.mp h3`.

Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr h1) (by linarith : (0 : ℝ) ≤ 7 / 2 - ρ.re), mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (ρ.im - t)) (by linarith : (0 : ℝ) ≤ 1 + (ρ.im - t))]`. Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp hsq`.
-/
lemma mem_closedBall_of_right {ρ : ℂ} {t : ℝ} (h1 : 1 / 2 ≤ ρ.re) (h2 : ρ.re < 1) (h3 : |ρ.im - t| ≤ 1) :
    ρ ∈ closedBall (2 + t * I) (37 / 20) := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hsq : ‖ρ - (2 + t * I)‖ ^ 2 ≤ (37 / 20) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    have h4 := abs_le.mp h3
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (by linarith : (0 : ℝ) ≤ 7 / 2 - ρ.re),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (ρ.im - t)) (by linarith : (0 : ℝ) ≤ 1 + (ρ.im - t))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp hsq

/- English proof (translation)
Rewrite `hz` using `[mem_sphere, dist_eq_norm]`. Establish `hc : ‖(2 : ℂ) + t * I‖ ≤ 2 + |t|`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Simplify using `[Complex.norm_real]`. Prove the components needed by the constructor for the conclusion.

Establish `h1` using `Complex.abs_re_le_norm (z - (2 + t * I))`. Rewrite `h1` using `[hz]`. Simplify using `at h1`. Combine the linear relations using `[(abs_le.mp h1).1]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma sphere_facts {z : ℂ} {t : ℝ} (hz : z ∈ sphere (2 + t * I) (19 / 10)) :
    1 / 10 ≤ z.re ∧ ‖z‖ ≤ |t| + 4 := by
  rw [mem_sphere, dist_eq_norm] at hz
  have hc : ‖(2 : ℂ) + t * I‖ ≤ 2 + |t| := by
    refine (norm_add_le _ _).trans ?_
    simp [Complex.norm_real]
  constructor
  · have h1 := Complex.abs_re_le_norm (z - (2 + t * I))
    rw [hz] at h1
    simp at h1
    linarith [(abs_le.mp h1).1]
  · calc ‖z‖ = ‖(z - (2 + t * I)) + (2 + t * I)‖ := by ring_nf
      _ ≤ ‖z - (2 + t * I)‖ + ‖(2 : ℂ) + t * I‖ := norm_add_le _ _
      _ ≤ |t| + 4 := by rw [hz]; linarith

/- English proof (translation)
Introduce `hL hI`. Establish `hl : 0 < Real.log ((19 / 10) / (37 / 20) : ℝ)` using `Real.log_pos (by norm_num)`. Use `⟨9 / Real.log ((19 / 10) / (37 / 20)), fun N _ χ hχ t => ?_⟩` and prove the remaining obligations. Establish `hNr : (1 : ℝ) ≤ N` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)`. Establish `hcre : (2 + t * I : ℂ).re = 2` using `by simp`.

Establish `hc0 : DirichletCharacter.LFunction χ (2 + t * I) ≠ 0` using `DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by rw [hcre]; norm_num)`. Establish `hpos : 0 < ‖DirichletCharacter.LFunction χ (2 + t * I)‖` using `norm_pos_iff.mpr hc0`. Establish `hinv` using `hI N χ (2 + t * I) (by rw [hcre]; norm_num)`. Rewrite `hinv` using `[hcre]`. Establish `hfc : 1 / 2 ≤ ‖DirichletCharacter.LFunction χ (2 + t * I)‖`.

Establish `h` using `(inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 2)).mp (hinv.trans (by norm_num))`. Combine the linear relations using `[show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]`. Establish `han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (closedBall (2 + t * I) (19 / 10))` using `fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z`. Establish `hM1 : (1 : ℝ) ≤ 1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4))`. Establish `: 0 ≤ 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4))` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbd : ∀ z ∈ sphere (2 + t * I) (19 / 10), ‖DirichletCharacter.LFunction χ z‖ ≤ 1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4))`. Introduce `z hz`. Take `⟨hre, hnorm⟩` from `sphere_facts hz`. Establish `hz0 : 0 < z.re` using `by linarith`.

Use `(hL N χ hχ z hz0).trans ?_` and prove the remaining obligations. Establish `h1 : ‖z‖ / z.re ≤ 10 * (|t| + 4)`. Rewrite using `[div_le_iff₀ hz0]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hre (by positivity : (0 : ℝ) ≤ 10 * (|t| + 4))]`. Establish `h2` using `mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * ((N : ℝ) + 1))`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hS : RightNear χ t ⊆ {z | z ∈ closedBall (2 + t * I) (37 / 20) ∧ DirichletCharacter.LFunction χ z = 0}` using `fun ρ hρ => ⟨mem_closedBall_of_right hρ.1 hρ.2.1 hρ.2.2.1, hρ.2.2.2⟩`. Take `⟨hfin, hsum⟩` from `hJ (DirichletCharacter.LFunction χ) (2 + t * I) _ han hc0 hM1 hbd (RightNear χ t) hS`. Use `⟨hfin, hsum.trans ?_⟩` and prove the remaining obligations. Establish `hX : 2 ≤ (N : ℝ) * (|t| + 2)` using `by nlinarith [abs_nonneg t]`.

Establish `htN : |t| ≤ N * |t|` using `le_mul_of_one_le_left (abs_nonneg t) hNr`. Establish `hM85 : 1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4)) ≤ 85 * ((N : ℝ) * (|t| + 2))`. Use polynomial arithmetic with `[abs_nonneg t]`. Establish `hM' : (1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4))) / ‖DirichletCharacter.LFunction χ (2 + t * I)‖ ≤ 170 * ((N : ℝ) * (|t| + 2))`. Rewrite using `[div_le_iff₀ hpos]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hfc (by linarith : (0 : ℝ) ≤ (N : ℝ) * (|t| + 2))]`. Establish `h9` using `log_le_nine _ _ hX (by positivity) hM'`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rightChi_of (hJ : JensenCount) : RightChi := by
  intro hL hI
  have hl : 0 < Real.log ((19 / 10) / (37 / 20) : ℝ) := Real.log_pos (by norm_num)
  refine ⟨9 / Real.log ((19 / 10) / (37 / 20)), fun N _ χ hχ t => ?_⟩
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hcre : (2 + t * I : ℂ).re = 2 := by simp
  have hc0 : DirichletCharacter.LFunction χ (2 + t * I) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by rw [hcre]; norm_num)
  have hpos : 0 < ‖DirichletCharacter.LFunction χ (2 + t * I)‖ := norm_pos_iff.mpr hc0
  have hinv := hI N χ (2 + t * I) (by rw [hcre]; norm_num)
  rw [hcre] at hinv
  have hfc : 1 / 2 ≤ ‖DirichletCharacter.LFunction χ (2 + t * I)‖ := by
    have h := (inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 2)).mp (hinv.trans (by norm_num))
    linarith [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (closedBall (2 + t * I) (19 / 10)) :=
    fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hM1 : (1 : ℝ) ≤ 1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4)) := by
    have : 0 ≤ 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4)) := by positivity
    linarith
  have hbd : ∀ z ∈ sphere (2 + t * I) (19 / 10), ‖DirichletCharacter.LFunction χ z‖ ≤
      1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4)) := by
    intro z hz
    obtain ⟨hre, hnorm⟩ := sphere_facts hz
    have hz0 : 0 < z.re := by linarith
    refine (hL N χ hχ z hz0).trans ?_
    have h1 : ‖z‖ / z.re ≤ 10 * (|t| + 4) := by
      rw [div_le_iff₀ hz0]
      nlinarith [mul_le_mul_of_nonneg_left hre (by positivity : (0 : ℝ) ≤ 10 * (|t| + 4))]
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * ((N : ℝ) + 1))
    nlinarith
  have hS : RightNear χ t ⊆ {z | z ∈ closedBall (2 + t * I) (37 / 20) ∧ DirichletCharacter.LFunction χ z = 0} :=
    fun ρ hρ => ⟨mem_closedBall_of_right hρ.1 hρ.2.1 hρ.2.2.1, hρ.2.2.2⟩
  obtain ⟨hfin, hsum⟩ := hJ (DirichletCharacter.LFunction χ) (2 + t * I) _ han hc0 hM1 hbd (RightNear χ t) hS
  refine ⟨hfin, hsum.trans ?_⟩
  have hX : 2 ≤ (N : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t]
  have htN : |t| ≤ N * |t| := le_mul_of_one_le_left (abs_nonneg t) hNr
  have hM85 : 1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4)) ≤ 85 * ((N : ℝ) * (|t| + 2)) := by
    nlinarith [abs_nonneg t]
  have hM' : (1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4))) / ‖DirichletCharacter.LFunction χ (2 + t * I)‖ ≤
      170 * ((N : ℝ) * (|t| + 2)) := by
    rw [div_le_iff₀ hpos]
    nlinarith [mul_le_mul_of_nonneg_left hfc (by linarith : (0 : ℝ) ≤ (N : ℝ) * (|t| + 2))]
  have h9 := log_le_nine _ _ hX (by positivity) hM'
  calc Real.log ((1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4))) /
        ‖DirichletCharacter.LFunction χ (2 + t * I)‖) / Real.log ((19 / 10) / (37 / 20))
      ≤ (9 * Real.log ((N : ℝ) * (|t| + 2))) / Real.log ((19 / 10) / (37 / 20)) :=
        div_le_div_of_nonneg_right h9 hl.le
    _ = 9 / Real.log ((19 / 10) / (37 / 20)) * Real.log ((N : ℝ) * (|t| + 2)) := by ring

end PI.ZW
