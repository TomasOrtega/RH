import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HsEighthLeOfSmall
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ProdSubLtEqFactorial
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdScale
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarBasic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PBridge
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntegrableOfContinuousCompact
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdUpperA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdUpperB

noncomputable section

open Finset Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
The claim follows from `inv_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega)))`.
-/
theorem fdU_s_pos {t : ℕ} (ht : 1 ≤ t) : 0 < (Real.sqrt (t : ℝ))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega)))

/- English proof (translation)
Establish `ht' : (0 : ℝ) < t` using `Nat.cast_pos.mpr (by omega)`. Rewrite using `[inv_pow, Real.sq_sqrt ht'.le, inv_mul_cancel₀ ht'.ne']`.
-/
theorem fdU_s_sq {t : ℕ} (ht : 1 ≤ t) : (Real.sqrt (t : ℝ))⁻¹ ^ 2 * t = 1 := by
  have ht' : (0 : ℝ) < t := Nat.cast_pos.mpr (by omega)
  rw [inv_pow, Real.sq_sqrt ht'.le, inv_mul_cancel₀ ht'.ne']

/- English proof (translation)
Establish `ht1 : 1 ≤ t` using `le_trans (by omega) ht`. Establish `hs0` using `fdU_s_pos ht1`. Establish `hst` using `fdU_s_sq ht1`. Establish `hfar` using `fdU_far hlam (t₀ := 16 * n * q0 ε + 1) (by omega) ht hs0 hst y`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises.

Use `hfar.trans ?_` and prove the remaining obligations. Rewrite using `[sub_eq_add_neg, Real.exp_add]`. Apply `mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le` to reduce the goal to its premises. Break down `isEmpty_or_nonempty (PCoord ε) with hE | hN` into its components or cases. Establish `hp : pmat y = 0`.

Use extensionality with `a b`. Simplify using `only [pmat, Matrix.zero_apply]`. Use `split_ifs with h1 h2`. Conclude with `(hE.false ⟨(a, b), h1⟩).elim`. Conclude with `(hE.false ⟨(b, a), h2⟩).elim`.

Both sides reduce to the same expression. Establish `hh : hs (pmat y) = 0` using `by rw [hp]; simp [hs]`. Rewrite using `[hh, Real.sqrt_zero, mul_zero, neg_zero, Real.exp_zero]`. Simplify using the standard rewrite rules. Establish `ab : PCoord ε` using `Classical.choice hN`.

Establish `hc` using `fdU_c_pos ab`. Establish `h2` using `fdU_exp_le_prod hc.le y`. Rewrite using `[← neg_mul]`. Conclude with `h2`.
-/
theorem fdU_major {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (t : ℕ)
    (ht : 16 * n * q0 ε + 1 ≤ t) (y : PCoord ε → ℂ) :
    ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) ≤
      ENNReal.ofReal (Real.exp ((Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ))) ^ 2 / 32) *
        ∏ ab : PCoord ε, Real.exp (-((Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ)) / 8 -
          |(n : ℝ) - 1| * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ)) /
            ((Fintype.card (PCoord ε) : ℝ) + 1)) * ‖y ab‖)) := by
  have ht1 : 1 ≤ t := le_trans (by omega) ht
  have hs0 := fdU_s_pos ht1
  have hst := fdU_s_sq ht1
  have hfar := fdU_far hlam (t₀ := 16 * n * q0 ε + 1) (by omega) ht hs0 hst y
  apply ENNReal.ofReal_le_ofReal
  refine hfar.trans ?_
  rw [sub_eq_add_neg, Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rcases isEmpty_or_nonempty (PCoord ε) with hE | hN
  · have hp : pmat y = 0 := by
      ext a b
      simp only [pmat, Matrix.zero_apply]
      split_ifs with h1 h2
      · exact (hE.false ⟨(a, b), h1⟩).elim
      · exact (hE.false ⟨(b, a), h2⟩).elim
      · rfl
    have hh : hs (pmat y) = 0 := by rw [hp]; simp [hs]
    rw [hh, Real.sqrt_zero, mul_zero, neg_zero, Real.exp_zero]
    simp
  · have ab : PCoord ε := Classical.choice hN
    have hc := fdU_c_pos ab
    have h2 := fdU_exp_le_prod hc.le y
    rw [← neg_mul]
    exact h2

/- English proof (translation)
Use `set ρ := rhoP y`. Use `set r := Real.sqrt (hs (pmat y))`. Use `set C := ((n : ℝ) - 1) * Real.sqrt (2 * (q0 ε : ℝ))`. Use `set φ : ℝ → ℝ := fun v => Real.exp (-(1 - v * ρ) * Qf (0 : Fin n → ℝ) y + C * (v * r)) with hφdef`. Establish `hφ : Continuous φ`.

Simplify using `only [hφdef]`. Use `fun_prop`. Establish `hu : Tendsto (fun t : ℕ => (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹) atTop (𝓝 0)` using `tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat T)))`. Establish `hev : ∀ᶠ t : ℕ in atTop, (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ * ρ < 1`. Establish `h` using `hu.mul_const ρ`.

Rewrite `h` using `[zero_mul]`. Conclude with `h.eventually (gt_mem_nhds one_pos)`. Establish `hle : ∀ᶠ t : ℕ in atTop, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam (t + T)) (pmat ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) * Jac ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y)) ≤ ENNReal.ofReal (φ (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹)` using `hev.mono fun t ht => ENNReal.ofReal_le_ofReal (fdU_near hlam (fdU_s_pos (by omega)) (fdU_s_sq (by omega)) y ht.le)`. Establish `hlim : Tendsto (fun t : ℕ => ENNReal.ofReal (φ (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹)) atTop (𝓝 (ENNReal.ofReal (φ 0)))` using `ENNReal.tendsto_ofReal ((hφ.tendsto 0).comp hu)`. Establish `h0 : φ 0 = Real.exp (-Qf (0 : Fin n → ℝ) y)` using `by simp [hφdef]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem fdU_pointwise {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (T : ℕ) (hT : 1 ≤ T)
    (y : PCoord ε → ℂ) :
    limsup (fun t : ℕ => ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam (t + T))
        (pmat ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) atTop ≤
      ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) := by
  set ρ := rhoP y
  set r := Real.sqrt (hs (pmat y))
  set C := ((n : ℝ) - 1) * Real.sqrt (2 * (q0 ε : ℝ))
  set φ : ℝ → ℝ := fun v => Real.exp (-(1 - v * ρ) * Qf (0 : Fin n → ℝ) y + C * (v * r)) with hφdef
  have hφ : Continuous φ := by
    simp only [hφdef]; fun_prop
  have hu : Tendsto (fun t : ℕ => (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat T)))
  have hev : ∀ᶠ t : ℕ in atTop, (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ * ρ < 1 := by
    have h := hu.mul_const ρ
    rw [zero_mul] at h
    exact h.eventually (gt_mem_nhds one_pos)
  have hle : ∀ᶠ t : ℕ in atTop, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam (t + T))
        (pmat ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y)) ≤
        ENNReal.ofReal (φ (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹) :=
    hev.mono fun t ht => ENNReal.ofReal_le_ofReal
      (fdU_near hlam (fdU_s_pos (by omega)) (fdU_s_sq (by omega)) y ht.le)
  have hlim : Tendsto (fun t : ℕ => ENNReal.ofReal (φ (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹)) atTop
      (𝓝 (ENNReal.ofReal (φ 0))) :=
    ENNReal.tendsto_ofReal ((hφ.tendsto 0).comp hu)
  have h0 : φ 0 = Real.exp (-Qf (0 : Fin n → ℝ) y) := by simp [hφdef]
  calc _ ≤ limsup (fun t : ℕ => ENNReal.ofReal (φ (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹)) atTop :=
        limsup_le_limsup hle
    _ = ENNReal.ofReal (φ 0) := hlim.limsup_eq
    _ = _ := by rw [h0]

/- English proof (translation)
Establish `hscale : ∀ t : ℕ, 1 ≤ t → ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) * ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat z)) * Jac z) = ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y))) * Jac (((( …`. Introduce `t ht`. Establish `htpos : (0 : ℝ) < t` using `by exact_mod_cast ht`. Rewrite using `[lintegral_pcoord_smul _ (fdU_s_pos ht), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]`. Establish `e : (t : ℝ) ^ (pOf ε * qOf ε) * ((Real.sqrt t)⁻¹) ^ (2 * (pOf ε * qOf ε)) = 1`.

Rewrite using `[inv_pow, pow_mul (Real.sqrt (t : ℝ)) 2, Real.sq_sqrt htpos.le, mul_inv_cancel₀ (pow_ne_zero _ htpos.ne')]`. Rewrite using `[e, ENNReal.ofReal_one, one_mul]`. Use `set T : ℕ := 16 * n * q0 ε + 1 with hT`. Rewrite using `[← Filter.limsup_nat_add _ T]`. Use `le_trans (le_of_eq (Filter.limsup_congr (Filter.Eventually.of_forall fun i => hscale (i + T) (by omega)))) ?_` and prove the remaining obligations.

Establish `hmeas : ∀ t : ℕ, Measurable (fun y : PCoord ε → ℂ => ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam (t + T)) (pmat ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) * Jac ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y)))`. Introduce `t`. Apply `ENNReal.measurable_ofReal.comp` to reduce the goal to its premises. Apply `Continuous.measurable` to reduce the goal to its premises. Establish `hc : Continuous (fun y : PCoord ε → ℂ => (((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y)` using `continuous_const_smul _`.

Conclude with `(Real.continuous_exp.comp (continuous_const.mul ((continuous_potential_pmat _).comp hc))).mul ((jac_continuous ε).comp hc)`. Establish `hint` using `((fdU_integrable_prod_exp (ε := ε) (c := (Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ)) / 8 - |(n : ℝ) - 1| * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ)) / ((Fintype.card (PCoord ε) : ℝ) + 1)) (fun ab => div_pos (fdU_c_pos ab) (by …`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem formal_degree_limsup_upper_bound {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) :
    Filter.limsup (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat z)) * Jac z)) Filter.atTop ≤
      ENNReal.ofReal (PiW ε 0) := by
  have hscale : ∀ t : ℕ, 1 ≤ t → ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat z)) * Jac z) =
      ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t)
        (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y))) * Jac ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) := by
    intro t ht
    have htpos : (0 : ℝ) < t := by exact_mod_cast ht
    rw [lintegral_pcoord_smul _ (fdU_s_pos ht), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    have e : (t : ℝ) ^ (pOf ε * qOf ε) * ((Real.sqrt t)⁻¹) ^ (2 * (pOf ε * qOf ε)) = 1 := by
      rw [inv_pow, pow_mul (Real.sqrt (t : ℝ)) 2, Real.sq_sqrt htpos.le, mul_inv_cancel₀ (pow_ne_zero _ htpos.ne')]
    rw [e, ENNReal.ofReal_one, one_mul]
  set T : ℕ := 16 * n * q0 ε + 1 with hT
  rw [← Filter.limsup_nat_add _ T]
  refine le_trans (le_of_eq (Filter.limsup_congr (Filter.Eventually.of_forall fun i => hscale (i + T) (by omega)))) ?_
  have hmeas : ∀ t : ℕ, Measurable (fun y : PCoord ε → ℂ => ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam (t + T))
      (pmat ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) := by
    intro t
    apply ENNReal.measurable_ofReal.comp
    apply Continuous.measurable
    have hc : Continuous (fun y : PCoord ε → ℂ => (((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y) :=
      continuous_const_smul _
    exact (Real.continuous_exp.comp (continuous_const.mul ((continuous_potential_pmat _).comp hc))).mul
      ((jac_continuous ε).comp hc)
  have hint := ((fdU_integrable_prod_exp (ε := ε)
    (c := (Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ)) / 8 -
          |(n : ℝ) - 1| * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ)) /
            ((Fintype.card (PCoord ε) : ℝ) + 1))
    (fun ab => div_pos (fdU_c_pos ab) (by positivity))).const_mul
    (Real.exp ((Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ))) ^ 2 / 32)))
  calc _ ≤ ∫⁻ y, limsup (fun t : ℕ => ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam (t + T))
        (pmat ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) atTop :=
        limsup_lintegral_le _ hmeas
          (fun t => Filter.Eventually.of_forall fun y => fdU_major hlam (t + T) (by omega) y)
          hint.lintegral_lt_top.ne
    _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) :=
        lintegral_mono fun y => fdU_pointwise hlam T (by omega) y
    _ = _ := fdU_lintegral_gauss ε

end ReciprocityTheory.ChartRestriction.DS
