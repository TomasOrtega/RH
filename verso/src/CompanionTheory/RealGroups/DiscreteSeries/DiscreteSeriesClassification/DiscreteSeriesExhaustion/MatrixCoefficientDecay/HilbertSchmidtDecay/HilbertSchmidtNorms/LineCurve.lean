import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HilbertSchmidtNorms.ContinuousHs

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal

namespace CompanionTheory.RgExh.Dec.L.AB

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {S : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)} {m : ℕ}
    {A : Fin m → Matrix (Fin n) (Fin n) ℂ} {ν : ∀ j, Measure (PSub ε (A j))} {τ : Fin m → S7.UJ ε → ℝ}
    {r : Fin m → ℝ} {Z : Fin m → Finset ℂ} {M c₁ R₀ C : ℝ}

/- English proof (translation)
Use `⟨fun t => Classical.choose (H.lines j x t), ?_, fun t => Classical.choose_spec (H.lines j x t)⟩` and prove the remaining obligations. Rewrite using `[(ReciprocityTheory.ChartRestriction.DS.S7.isClosedEmbedding_toM ε).isInducing.continuous_iff]`. Establish `: (fun g : S7.UJ ε => S7.toM g) ∘ (fun t => ((Classical.choose (H.lines j x t) : PSub ε (A j)) : S7.UJ ε)) = fun t => S7.toM (x : S7.UJ ε) * aT (A j) t`. Use function extensionality and compare the values at `t`. Conclude with `(Classical.choose_spec (H.lines j x t)).1`.

Rewrite using `[this]`. Conclude with `continuous_const.matrix_mul (continuous_aT (A j))`.
-/
theorem line_curve (H : Hyp ε S m A ν τ r Z M c₁ R₀ C) (j : Fin m) (x : PSub ε (A j)) :
    ∃ ℓ : ℝ → PSub ε (A j), Continuous (fun t => ((ℓ t : PSub ε (A j)) : S7.UJ ε)) ∧
      ∀ t, S7.toM ((ℓ t : PSub ε (A j)) : S7.UJ ε) = S7.toM (x : S7.UJ ε) * aT (A j) t ∧ τ j (ℓ t) = τ j x + t := by
  refine ⟨fun t => Classical.choose (H.lines j x t), ?_, fun t => Classical.choose_spec (H.lines j x t)⟩
  rw [(ReciprocityTheory.ChartRestriction.DS.S7.isClosedEmbedding_toM ε).isInducing.continuous_iff]
  have : (fun g : S7.UJ ε => S7.toM g) ∘ (fun t => ((Classical.choose (H.lines j x t) : PSub ε (A j)) : S7.UJ ε)) =
      fun t => S7.toM (x : S7.UJ ε) * aT (A j) t := by
    funext t
    exact (Classical.choose_spec (H.lines j x t)).1
  rw [this]
  exact continuous_const.matrix_mul (continuous_aT (A j))

/- English proof (translation)
Take `⟨ℓ, hℓ, hℓe⟩` from `line_curve H j x`. Establish `: (fun t : ℝ => q (S7.toM (x : S7.UJ ε) * aT (A j) t)) = fun t => q (S7.toM ((ℓ t : PSub ε (A j)) : S7.UJ ε))`. Use function extensionality and compare the values at `t`. Rewrite using `[(hℓe t).1]`. Rewrite using `[this]`.

Conclude with `hq.comp hℓ`.
-/
theorem line_cont (H : Hyp ε S m A ν τ r Z M c₁ R₀ C) (j : Fin m) (x : PSub ε (A j)) (q : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hq : Continuous fun g : S7.UJ ε => q (S7.toM g)) :
    Continuous fun t : ℝ => q (S7.toM (x : S7.UJ ε) * aT (A j) t) := by
  obtain ⟨ℓ, hℓ, hℓe⟩ := line_curve H j x
  have : (fun t : ℝ => q (S7.toM (x : S7.UJ ε) * aT (A j) t)) = fun t => q (S7.toM ((ℓ t : PSub ε (A j)) : S7.UJ ε)) := by
    funext t; rw [(hℓe t).1]
  rw [this]
  exact hq.comp hℓ

/- English proof (translation)
Take `⟨C₀, hC₀, hC⟩` from `hLC mm z R (r j + 1) hR hzR`. Use `⟨C₀, hC₀, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx' : ReciprocityTheory.ChartRestriction.DS.inUJ ε (S7.toM (x : S7.UJ ε))` using `(x : S7.UJ ε).2`. Use `hC (fun k t => F k (S7.toM (x : S7.UJ ε) * aT (A j) t)) (fun k t _ => hder k _ t hx') (fun k => line_cont H j x (F k) (H.cont _ (hF k))) hx` as an intermediate fact. Simplify `this` using `only [hlast]`.
-/
theorem ode_line (hLC : LineChain) (H : Hyp ε S m A ν τ r Z M c₁ R₀ C) (j : Fin m) (h : Matrix (Fin n) (Fin n) ℂ → ℂ) {mm : ℕ} (z : Fin mm → ℂ)
    (F : Fin (mm + 1) → Matrix (Fin n) (Fin n) ℂ → ℂ) (hF : ∀ k, F k ∈ S) (hlast : F (Fin.last mm) = h)
    (hder : ∀ (k : Fin mm) (g : Matrix (Fin n) (Fin n) ℂ) (t : ℝ), ReciprocityTheory.ChartRestriction.DS.inUJ ε g →
      HasDerivAt (fun s : ℝ => F k.succ (g * aT (A j) s)) (z k * F k.succ (g * aT (A j) t) + F k.castSucc (g * aT (A j) t)) t)
    (R : ℝ) (hR : R ≤ r j + 1) (hzR : ∀ k, (z k).re ≠ -R) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ x : PSub ε (A j),
      (∀ k, ∫⁻ t in Set.Ioi (0 : ℝ), ‖F k (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
        ENNReal.ofReal (Real.exp (2 * (r j + 1) * t)) < ⊤) →
      ∫⁻ t in Set.Ioi (0 : ℝ), ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * R * t)) ≤
        ENNReal.ofReal C₀ * (∑ k, ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖F k (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 +
          ∫⁻ t in Set.Ioi (0 : ℝ), ‖F 0 (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * R * t))) := by
  obtain ⟨C₀, hC₀, hC⟩ := hLC mm z R (r j + 1) hR hzR
  refine ⟨C₀, hC₀, fun x hx => ?_⟩
  have hx' : ReciprocityTheory.ChartRestriction.DS.inUJ ε (S7.toM (x : S7.UJ ε)) := (x : S7.UJ ε).2
  have := hC (fun k t => F k (S7.toM (x : S7.UJ ε) * aT (A j) t))
    (fun k t _ => hder k _ t hx') (fun k => line_cont H j x (F k) (H.cont _ (hF k))) hx
  simpa only [hlast] using this

/- English proof (translation)
Establish `hpt : ∀ t ∈ Set.Ioi (0 : ℝ), ‖f₀ (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * R * t)) ≤ (T.card : ℝ≥0∞) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * ρ * t))`. Introduce `t ht`. Establish `ht0 : (0 : ℝ) < t` using `ht`. Take `⟨y, hy, hyt⟩` from `H.lines j x t`. Establish `hy0 : 0 ≤ τ j y` using `by rw [hyt]; linarith`.

Establish `hb` using `hT y hy0`. Rewrite `hb` using `[hy]`. Use `set a : (Matrix (Fin n) (Fin n) ℂ → ℂ) → ℝ := fun h => ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ with ha`. Use `set b := ‖f₀ (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ with hbdef`. Establish `hb' : b ≤ Real.exp (-t) * ∑ h ∈ T, a h`.

Use `hb.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by rw [hyt]; linarith)) (Finset.sum_nonneg fun h _ => norm_nonneg _))` and prove the remaining obligations. Establish `hsq : (∑ h ∈ T, a h) ^ 2 ≤ T.card * ∑ h ∈ T, a h ^ 2` using `sq_sum_le_card_mul_sum_sq`. Establish `hb2 : b ^ 2 ≤ Real.exp (-t) ^ 2 * (T.card * ∑ h ∈ T, a h ^ 2)`. Combine the equalities or inequalities in the displayed calculation. Establish `hexp : Real.exp (-t) ^ 2 * Real.exp (2 * R * t) ≤ Real.exp (2 * ρ * t)`.

Rewrite using `[sq, ← Real.exp_add, ← Real.exp_add]`. Conclude with `Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hRρ ht0.le])`. Establish `hS0 : 0 ≤ (T.card : ℝ) * ∑ h ∈ T, a h ^ 2` using `by positivity`. Establish `hreal : b ^ 2 * Real.exp (2 * R * t) ≤ (T.card : ℝ) * ∑ h ∈ T, a h ^ 2 * Real.exp (2 * ρ * t)`. Rewrite using `[← Finset.sum_mul, ← mul_assoc]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hL : ‖f₀ (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * R * t)) = ENNReal.ofReal (b ^ 2 * Real.exp (2 * R * t))`. Rewrite using `[ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _)]`. Simplify using `only [hbdef, ofReal_norm_eq_enorm]`. Establish `hR : (T.card : ℝ≥0∞) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * ρ * t)) = ENNReal.ofReal ((T.card : ℝ) * ∑ h ∈ T, a h ^ 2 * Real.exp (2 * ρ * t))`.

Rewrite using `[ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]`. Use `congr 1`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _)]`. Simplify using `only [ha, ofReal_norm_eq_enorm]`.

Rewrite using `[hL, hR]`. Conclude with `ENNReal.ofReal_le_ofReal hreal`. Establish `hmeas : ∀ h ∈ T, Measurable fun t : ℝ => ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * ρ * t))`. Introduce `h hh`. Establish `hc` using `line_cont H j x h (H.cont h (hTS h hh))`.

Conclude with `(hc.enorm.measurable.pow_const 2).mul (by fun_prop)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem src_line (H : Hyp ε S m A ν τ r Z M c₁ R₀ C) (j : Fin m) (f₀ : Matrix (Fin n) (Fin n) ℂ → ℂ) (T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (hTS : ∀ h ∈ T, h ∈ S)
    (hT : ∀ x : PSub ε (A j), 0 ≤ τ j x → ‖f₀ (S7.toM (x : S7.UJ ε))‖ ≤ Real.exp (-τ j x) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε))‖)
    (x : PSub ε (A j)) (hx : 0 ≤ τ j x) (R ρ : ℝ) (hRρ : R - 1 ≤ ρ) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ‖f₀ (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * R * t)) ≤
      (T.card : ℝ≥0∞) * ∑ h ∈ T, ∫⁻ t in Set.Ioi (0 : ℝ), ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
        ENNReal.ofReal (Real.exp (2 * ρ * t)) := by
  classical
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ), ‖f₀ (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * R * t)) ≤
      (T.card : ℝ≥0∞) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * ρ * t)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    obtain ⟨y, hy, hyt⟩ := H.lines j x t
    have hy0 : 0 ≤ τ j y := by rw [hyt]; linarith
    have hb := hT y hy0
    rw [hy] at hb
    set a : (Matrix (Fin n) (Fin n) ℂ → ℂ) → ℝ := fun h => ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ with ha
    set b := ‖f₀ (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ with hbdef
    have hb' : b ≤ Real.exp (-t) * ∑ h ∈ T, a h := by
      refine hb.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by rw [hyt]; linarith))
        (Finset.sum_nonneg fun h _ => norm_nonneg _))
    have hsq : (∑ h ∈ T, a h) ^ 2 ≤ T.card * ∑ h ∈ T, a h ^ 2 := sq_sum_le_card_mul_sum_sq
    have hb2 : b ^ 2 ≤ Real.exp (-t) ^ 2 * (T.card * ∑ h ∈ T, a h ^ 2) := by
      calc b ^ 2 ≤ (Real.exp (-t) * ∑ h ∈ T, a h) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb' 2
        _ = Real.exp (-t) ^ 2 * (∑ h ∈ T, a h) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hsq (by positivity)
    have hexp : Real.exp (-t) ^ 2 * Real.exp (2 * R * t) ≤ Real.exp (2 * ρ * t) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hRρ ht0.le])
    have hS0 : 0 ≤ (T.card : ℝ) * ∑ h ∈ T, a h ^ 2 := by positivity
    have hreal : b ^ 2 * Real.exp (2 * R * t) ≤ (T.card : ℝ) * ∑ h ∈ T, a h ^ 2 * Real.exp (2 * ρ * t) := by
      rw [← Finset.sum_mul, ← mul_assoc]
      calc b ^ 2 * Real.exp (2 * R * t) ≤ Real.exp (-t) ^ 2 * (T.card * ∑ h ∈ T, a h ^ 2) * Real.exp (2 * R * t) :=
            mul_le_mul_of_nonneg_right hb2 (Real.exp_pos _).le
        _ = (T.card * ∑ h ∈ T, a h ^ 2) * (Real.exp (-t) ^ 2 * Real.exp (2 * R * t)) := by ring
        _ ≤ (T.card * ∑ h ∈ T, a h ^ 2) * Real.exp (2 * ρ * t) := mul_le_mul_of_nonneg_left hexp hS0
    have hL : ‖f₀ (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * R * t)) =
        ENNReal.ofReal (b ^ 2 * Real.exp (2 * R * t)) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _)]
      simp only [hbdef, ofReal_norm_eq_enorm]
    have hR : (T.card : ℝ≥0∞) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * ρ * t)) =
        ENNReal.ofReal ((T.card : ℝ) * ∑ h ∈ T, a h ^ 2 * Real.exp (2 * ρ * t)) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
      congr 1
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _)]
      simp only [ha, ofReal_norm_eq_enorm]
    rw [hL, hR]
    exact ENNReal.ofReal_le_ofReal hreal
  have hmeas : ∀ h ∈ T, Measurable fun t : ℝ =>
      ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * ρ * t)) := by
    intro h hh
    have hc := line_cont H j x h (H.cont h (hTS h hh))
    exact (hc.enorm.measurable.pow_const 2).mul (by fun_prop)
  calc ∫⁻ t in Set.Ioi (0 : ℝ), ‖f₀ (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * R * t))
      ≤ ∫⁻ t in Set.Ioi (0 : ℝ), (T.card : ℝ≥0∞) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
          ENNReal.ofReal (Real.exp (2 * ρ * t)) := setLIntegral_mono' measurableSet_Ioi hpt
    _ = (T.card : ℝ≥0∞) * ∫⁻ t in Set.Ioi (0 : ℝ), ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
          ENNReal.ofReal (Real.exp (2 * ρ * t)) := lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)
    _ = _ := by rw [lintegral_finsetSum T hmeas]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Use `setLIntegral_mono' measurableSet_Ioc fun t ht => ?_` and prove the remaining obligations. Establish `h1 : (1 : ℝ) ≤ Real.exp (2 * |ρ|) * Real.exp (2 * ρ * t)`. Rewrite using `[← Real.exp_add]`. Apply `Real.one_le_exp` to reduce the goal to its premises.

Establish `: |ρ * t| ≤ |ρ|`. Rewrite using `[abs_mul]`. Apply the tactic sequence `have : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]`. Combine the equalities or inequalities in the displayed calculation. Use `neg_abs_le (ρ * t)` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← ENNReal.ofReal_one]`. Conclude with `ENNReal.ofReal_le_ofReal h1`. Use `_ = _ := by`.

Rewrite using `[ENNReal.ofReal_mul (Real.exp_pos _).le]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ENNReal.ofReal (Real.exp (2 * |ρ|)) * ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖u t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * ρ * t)) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top`. Use `_ ≤ _ := mul_le_mul' le_rfl (lintegral_mono_set Set.Ioc_subset_Ioi_self)`.
-/
theorem unit_line (u : ℝ → ℂ) (ρ : ℝ) :
    ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖u t‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.exp (2 * |ρ|)) * ∫⁻ t in Set.Ioi (0 : ℝ), ‖u t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * ρ * t)) := by
  calc ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖u t‖ₑ ^ 2
      ≤ ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (Real.exp (2 * |ρ|)) * (‖u t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * ρ * t))) := by
        refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
        have h1 : (1 : ℝ) ≤ Real.exp (2 * |ρ|) * Real.exp (2 * ρ * t) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp
          have : |ρ * t| ≤ |ρ| := by
            rw [abs_mul]
            have : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
            calc |ρ| * |t| ≤ |ρ| * 1 := by gcongr
              _ = |ρ| := mul_one _
          have := neg_abs_le (ρ * t)
          nlinarith
        calc ‖u t‖ₑ ^ 2 = ‖u t‖ₑ ^ 2 * 1 := (mul_one _).symm
          _ ≤ ‖u t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * |ρ|) * Real.exp (2 * ρ * t)) := by
            gcongr
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal h1
          _ = _ := by
            rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
            ring
    _ = ENNReal.ofReal (Real.exp (2 * |ρ|)) * ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖u t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * ρ * t)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono_set Set.Ioc_subset_Ioi_self)

/- English proof (translation)
Use `set X := S7.toM (x : S7.UJ ε) with hX`. Establish `hX1 : 1 ≤ Formalism.REAL.hs X` using `one_le_hs hn (x : S7.UJ ε)`. Establish `haT0 : aT (A j) 0 = 1`. Simplify using `[aT]`. Establish `hC1 : 1 ≤ C`.

Establish `h0` using `(H.hsLine j x 0 hx le_rfl).2`. Rewrite `h0` using `[haT0, Matrix.mul_one]`. Simplify using `only [mul_zero, Real.exp_zero, mul_one] at h0`. Rewrite `h0` using `[← hX]`. Assume the negation of the conclusion as `hC`.

Establish `hC'` using `not_le.mp hC`. Use the polynomial consequences of the given equalities and inequalities. Establish `hCpos : 0 < C` using `lt_of_lt_of_le one_pos hC1`. Combine the equalities or inequalities in the displayed calculation. Use `setLIntegral_mono' measurableSet_Ioi fun t ht => ?_` and prove the remaining obligations.

Take `⟨y, hy, -⟩` from `H.lines j x t`. Establish `ht0 : (0 : ℝ) ≤ t` using `le_of_lt ht`. Establish `hup` using `(H.hsLine j x t hx ht0).2`. Rewrite `hup`, the goal using `[← hy]`. Establish `hy1 : 1 ≤ Formalism.REAL.hs (S7.toM (y : S7.UJ ε))` using `one_le_hs hn (y : S7.UJ ε)`.

Establish `hge` using `psiK_ge q s (y : S7.UJ ε)`. Establish `key : Formalism.REAL.hs X ^ s * Real.exp (2 * (r j + s) * t) ≤ C ^ (-s) * Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ s * Real.exp (2 * r j * t)`. Establish `h1 : (C * Real.exp (2 * t) * Formalism.REAL.hs X) ^ s ≤ Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ s` using `Real.rpow_le_rpow_of_nonpos (by linarith) hup hs`. Rewrite `h1` using `[Real.mul_rpow (by positivity) (by linarith), Real.mul_rpow hCpos.le (Real.exp_pos _).le, ← Real.exp_mul]`. Establish `hCC : C ^ (-s) * C ^ s = 1`.

Rewrite using `[← Real.rpow_add hCpos]`. Simplify using the standard rewrite rules. Establish `e1 : Real.exp (2 * (r j + s) * t) = Real.exp (2 * r j * t) * Real.exp (2 * t * s)`. Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form.

Rewrite using `[e1]`. Establish `hpos : 0 ≤ C ^ (-s)` using `Real.rpow_nonneg hCpos.le _`. Establish `hE : 0 ≤ Real.exp (2 * r j * t)` using `(Real.exp_pos _).le`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc (C ^ (-s)), ← mul_assoc (C ^ (-s)), hCC]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ C ^ (-s) * Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ s * Real.exp (2 * r j * t) := by gcongr`. Establish `hn1 : 0 ≤ Formalism.REAL.hs X ^ s` using `Real.rpow_nonneg (by linarith) _`. Establish `hn2 : 0 ≤ C ^ (-s) * Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ s` using `mul_nonneg (Real.rpow_nonneg hCpos.le _) (Real.rpow_nonneg (by linarith) _)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[ENNReal.ofReal_mul hn1]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ‖q (S7.toM (y : S7.UJ ε))‖ₑ ^ 2 * ENNReal.ofReal (C ^ (-s) * Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ s * Real.exp (2 * r j * t)) := by gcongr`. Use `_ = ENNReal.ofReal (C ^ (-s)) * ((‖q (S7.toM (y : S7.UJ ε))‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ s)) * ENNReal.ofReal (Real.exp (2 * r j * t))) := by`. Rewrite using `[ENNReal.ofReal_mul hn2, ENNReal.ofReal_mul (Real.rpow_nonneg hCpos.le _)]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ENNReal.ofReal (C ^ (-s)) * (PsiK ε q s (S7.toM (y : S7.UJ ε)) * ENNReal.ofReal (Real.exp (2 * r j * t))) := by gcongr`. Use `_ = ENNReal.ofReal (C ^ (-s)) * ∫⁻ t in Set.Ioi (0 : ℝ), PsiK ε q s (X * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top`. Use `_ ≤ _ := mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)`.
-/
theorem back_line (H : Hyp ε S m A ν τ r Z M c₁ R₀ C) (hn : 0 < n) (j : Fin m) (x : PSub ε (A j)) (hx : 0 ≤ τ j x)
    (q : Matrix (Fin n) (Fin n) ℂ → ℂ) (s : ℝ) (hs : s ≤ 0) :
    ENNReal.ofReal (Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ^ s) *
        ∫⁻ t in Set.Ioi (0 : ℝ), ‖q (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (r j + s) * t)) ≤
      ENNReal.ofReal (C ^ (-s)) * ∫⁻ t : ℝ, PsiK ε q s (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) := by
  set X := S7.toM (x : S7.UJ ε) with hX
  have hX1 : 1 ≤ Formalism.REAL.hs X := one_le_hs hn (x : S7.UJ ε)
  have haT0 : aT (A j) 0 = 1 := by
    simp [aT]
  have hC1 : 1 ≤ C := by
    have h0 := (H.hsLine j x 0 hx le_rfl).2
    rw [haT0, Matrix.mul_one] at h0
    simp only [mul_zero, Real.exp_zero, mul_one] at h0
    rw [← hX] at h0
    by_contra hC
    have hC' := not_le.mp hC
    nlinarith
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC1
  calc ENNReal.ofReal (Formalism.REAL.hs X ^ s) *
        ∫⁻ t in Set.Ioi (0 : ℝ), ‖q (X * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (r j + s) * t))
      = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Formalism.REAL.hs X ^ s) *
          (‖q (X * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (r j + s) * t))) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (C ^ (-s)) *
          (PsiK ε q s (X * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t))) := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        obtain ⟨y, hy, -⟩ := H.lines j x t
        have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
        have hup := (H.hsLine j x t hx ht0).2
        rw [← hy] at hup ⊢
        have hy1 : 1 ≤ Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) := one_le_hs hn (y : S7.UJ ε)
        have hge := psiK_ge q s (y : S7.UJ ε)

        have key : Formalism.REAL.hs X ^ s * Real.exp (2 * (r j + s) * t) ≤
            C ^ (-s) * Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ s * Real.exp (2 * r j * t) := by
          have h1 : (C * Real.exp (2 * t) * Formalism.REAL.hs X) ^ s ≤ Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ s :=
            Real.rpow_le_rpow_of_nonpos (by linarith) hup hs
          rw [Real.mul_rpow (by positivity) (by linarith), Real.mul_rpow hCpos.le (Real.exp_pos _).le,
            ← Real.exp_mul] at h1
          have hCC : C ^ (-s) * C ^ s = 1 := by
            rw [← Real.rpow_add hCpos]; simp
          have e1 : Real.exp (2 * (r j + s) * t) = Real.exp (2 * r j * t) * Real.exp (2 * t * s) := by
            rw [← Real.exp_add]; ring_nf
          rw [e1]
          have hpos : 0 ≤ C ^ (-s) := Real.rpow_nonneg hCpos.le _
          have hE : 0 ≤ Real.exp (2 * r j * t) := (Real.exp_pos _).le
          calc Formalism.REAL.hs X ^ s * (Real.exp (2 * r j * t) * Real.exp (2 * t * s))
              = C ^ (-s) * (C ^ s * Real.exp (2 * t * s) * Formalism.REAL.hs X ^ s) * Real.exp (2 * r j * t) := by
                rw [← mul_assoc (C ^ (-s)), ← mul_assoc (C ^ (-s)), hCC]; ring
            _ ≤ C ^ (-s) * Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ s * Real.exp (2 * r j * t) := by
                gcongr
        have hn1 : 0 ≤ Formalism.REAL.hs X ^ s := Real.rpow_nonneg (by linarith) _
        have hn2 : 0 ≤ C ^ (-s) * Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ s :=
          mul_nonneg (Real.rpow_nonneg hCpos.le _) (Real.rpow_nonneg (by linarith) _)
        calc ENNReal.ofReal (Formalism.REAL.hs X ^ s) *
              (‖q (S7.toM (y : S7.UJ ε))‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (r j + s) * t)))
            = ‖q (S7.toM (y : S7.UJ ε))‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs X ^ s * Real.exp (2 * (r j + s) * t)) := by
              rw [ENNReal.ofReal_mul hn1]; ring
          _ ≤ ‖q (S7.toM (y : S7.UJ ε))‖ₑ ^ 2 *
              ENNReal.ofReal (C ^ (-s) * Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ s * Real.exp (2 * r j * t)) := by
              gcongr
          _ = ENNReal.ofReal (C ^ (-s)) * ((‖q (S7.toM (y : S7.UJ ε))‖ₑ ^ 2 *
                ENNReal.ofReal (Formalism.REAL.hs (S7.toM (y : S7.UJ ε)) ^ s)) * ENNReal.ofReal (Real.exp (2 * r j * t))) := by
              rw [ENNReal.ofReal_mul hn2, ENNReal.ofReal_mul (Real.rpow_nonneg hCpos.le _)]; ring
          _ ≤ ENNReal.ofReal (C ^ (-s)) * (PsiK ε q s (S7.toM (y : S7.UJ ε)) * ENNReal.ofReal (Real.exp (2 * r j * t))) := by
              gcongr
    _ = ENNReal.ofReal (C ^ (-s)) * ∫⁻ t in Set.Ioi (0 : ℝ), PsiK ε q s (X * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

/- English proof (translation)
Take `⟨f₀, T, ⟨mm, z, F, hzZ, hFS, hlast, h0, hder⟩, hTS, hsrc⟩` from `H.chain h hh j`. Establish `hR : r j + s + c'' ≤ r j + 1` using `by linarith`. Establish `hzR : ∀ k, (z k).re ≠ -(r j + s + c'')` using `fun k => hz (z k) (hzZ k)`. Take `⟨C₀, hC₀, hode⟩` from `ode_line hLC H j h z F hFS hlast hder (r j + s + c'') hR hzR`. Use `set Q : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ) := Finset.univ.image F ∪ T with hQ`.

Establish `hQS : ∀ q ∈ Q, q ∈ S`. Introduce `q hq`. Break down `Finset.mem_union.1 hq with hq | hq` into its components or cases. Take `⟨k, -, rfl⟩` from `Finset.mem_image.1 hq`. Conclude with `hFS k`.

Conclude with `hTS q hq`. Establish `hFQ : ∀ k, F k ∈ Q` using `fun k => Finset.mem_union_left _ (Finset.mem_image_of_mem F (Finset.mem_univ k))`. Establish `hTQ : ∀ q ∈ T, q ∈ Q` using `fun q hq => Finset.mem_union_right _ hq`. Use `set Ψ : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞ := fun X => ∑ q ∈ Q, PsiK ε q s X with hΨ`. Use `set E : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * |r j + s|)) with hE`.

Use `set Cs : ℝ≥0∞ := ENNReal.ofReal (C ^ (-s)) with hCs`. Use `set cT : ℝ≥0∞ := (T.card : ℝ≥0∞) with hcT`. Use `⟨Ψ, ENNReal.ofReal C₀ * (((mm + 1 : ℕ) : ℝ≥0∞) * (E * Cs + cT * (cT * Cs))), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.add_ne_top.2 ⟨?_, ?_⟩))` and prove the remaining obligations. Conclude with `ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top`.

Conclude with `ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)`. Conclude with `Finset.measurable_sum Q (fun q hq => psiK_meas q s (H.cont q (hQS q hq)))`. Introduce `g k`. Conclude with `Finset.sum_congr rfl (fun q _ => psiK_inv q s g k)`. Rewrite using `[lintegral_finsetSum Q (fun q hq => psiK_meas q s (H.cont q (hQS q hq)))]`.

Use `ENNReal.sum_lt_top.2 (fun q hq => ?_)` and prove the remaining obligations. Take `⟨T', Cf, hT'S, hd⟩` from `H.dom q (hQS q hq)`. Conclude with `psiK_lint q s T' Cf hd (fun h' hh' => hL h' (hT'S h' hh')) (fun h' hh' => H.cont h' (hT'S h' hh'))`. Establish `hq_ae : ∀ᵐ (x : PSub ε (A j)) ∂(ν j), ∀ k, (∫⁻ t in Set.Ioi (0 : ℝ), ‖F k (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (r j + 1) * t))) < ⊤` using `ae_all_iff.2 (fun k => H.qual (F k) (hFS k) j) filter_upwards [hq_ae] with x hx hτ`. Establish `hx0 : 0 ≤ τ j x` using `hτ.1`.

Use `set a : ℝ≥0∞ := ENNReal.ofReal (Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ^ s) with ha`. Use `set Pall : ℝ≥0∞ := ∫⁻ t : ℝ, Ψ (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) with hPall`. Use `set L : (Matrix (Fin n) (Fin n) ℂ → ℂ) → ℝ≥0∞ := fun q => ∫⁻ t in Set.Ioi (0 : ℝ), ‖q (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (r j + s) * t)) with hLdef`. Establish `hback : ∀ q ∈ Q, a * L q ≤ Cs * Pall`. Introduce `q hq`.

Use `(back_line H hn j x hx0 q s hs).trans ?_` and prove the remaining obligations. Use `mul_le_mul_right (lintegral_mono fun t => ?_) _` and prove the remaining obligations. Use `mul_le_mul_left ?_ _` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun q => PsiK ε q s (S7.toM (x : S7.UJ ε) * aT (A j) t)) (fun _ _ => zero_le) hq`. Establish `hunit : ∀ k, ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖F k (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 ≤ E * L (F k)` using `fun k => unit_line (fun t => F k (S7.toM (x : S7.UJ ε) * aT (A j) t)) (r j + s)`.

Establish `hsrc' : ∫⁻ t in Set.Ioi (0 : ℝ), ‖F 0 (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (r j + s + c'') * t)) ≤ cT * ∑ h' ∈ T, L h'`. Rewrite using `[h0]`. Conclude with `src_line H j f₀ T hTS hsrc x hx0 (r j + s + c'') (r j + s) (by linarith)`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_right (mul_le_mul_right (Finset.sum_le_sum fun k _ => ?_) _) _` and prove the remaining obligations.

Rewrite using `[lintegral_add_right _ measurable_const, setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]`. Conclude with `add_le_add (hunit k) hsrc'`. Use `_ = ENNReal.ofReal C₀ * ∑ k : Fin (mm + 1), (E * (a * L (F k)) + cT * ∑ h' ∈ T, a * L h') := by`. Rewrite using `[mul_left_comm, Finset.mul_sum]`. Use `congrArg _ (Finset.sum_congr rfl fun k _ => ?_)` and prove the remaining obligations.

Rewrite using `[← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ENNReal.ofReal C₀ * ∑ _k : Fin (mm + 1), (E * (Cs * Pall) + cT * ∑ _h' ∈ T, Cs * Pall) := mul_le_mul_right (Finset.sum_le_sum fun k _ => add_le_add (mul_le_mul_right (hback _ (hFQ k)) _) (mul_le_mul_right (Finset.sum_le_sum fun h' hh' => hback _ (hTQ h' hh')) _)) _`. Use `_ = ENNReal.ofReal C₀ * (((mm + 1 : ℕ) : ℝ≥0∞) * (E * Cs + cT * (cT * Cs))) * Pall := by`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hcT]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem line_est (hLC : LineChain) (H : Hyp ε S m A ν τ r Z M c₁ R₀ C) (hn : 0 < n) (s : ℝ) (hs : s ≤ 0) (hL : ∀ f ∈ S, LevelF ε f s)
    (c'' : ℝ) (hc0 : 0 < c'') (hc1 : c'' ≤ 1) (j : Fin m) (hz : ∀ z ∈ Z j, z.re ≠ -(r j + s + c''))
    (h : Matrix (Fin n) (Fin n) ℂ → ℂ) (hh : h ∈ S) :
    ∃ (Ψ : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞) (K : ℝ≥0∞), K ≠ ⊤ ∧ Measurable (fun g : S7.UJ ε => Ψ (S7.toM g)) ∧
      (∀ (g : S7.UJ ε) (k : S7.KG ε), Ψ (S7.toM g * S7.toMK k) = Ψ (S7.toM g)) ∧
      ∫⁻ g : S7.UJ ε, Ψ (S7.toM g) ∂Measure.haar < ⊤ ∧
      ∀ᵐ (x : PSub ε (A j)) ∂(ν j), τ j x ∈ Set.Ico 0 1 →
        ENNReal.ofReal (Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ^ s) *
          ∫⁻ t in Set.Ioi (0 : ℝ), ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
            ENNReal.ofReal (Real.exp (2 * (r j + s + c'') * t)) ≤
        K * ∫⁻ t : ℝ, Ψ (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) := by
  classical
  obtain ⟨f₀, T, ⟨mm, z, F, hzZ, hFS, hlast, h0, hder⟩, hTS, hsrc⟩ := H.chain h hh j
  have hR : r j + s + c'' ≤ r j + 1 := by linarith
  have hzR : ∀ k, (z k).re ≠ -(r j + s + c'') := fun k => hz (z k) (hzZ k)
  obtain ⟨C₀, hC₀, hode⟩ := ode_line hLC H j h z F hFS hlast hder (r j + s + c'') hR hzR
  set Q : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ) := Finset.univ.image F ∪ T with hQ
  have hQS : ∀ q ∈ Q, q ∈ S := by
    intro q hq
    rcases Finset.mem_union.1 hq with hq | hq
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hq
      exact hFS k
    · exact hTS q hq
  have hFQ : ∀ k, F k ∈ Q := fun k => Finset.mem_union_left _ (Finset.mem_image_of_mem F (Finset.mem_univ k))
  have hTQ : ∀ q ∈ T, q ∈ Q := fun q hq => Finset.mem_union_right _ hq
  set Ψ : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞ := fun X => ∑ q ∈ Q, PsiK ε q s X with hΨ
  set E : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * |r j + s|)) with hE
  set Cs : ℝ≥0∞ := ENNReal.ofReal (C ^ (-s)) with hCs
  set cT : ℝ≥0∞ := (T.card : ℝ≥0∞) with hcT
  refine ⟨Ψ, ENNReal.ofReal C₀ * (((mm + 1 : ℕ) : ℝ≥0∞) * (E * Cs + cT * (cT * Cs))), ?_, ?_, ?_, ?_, ?_⟩
  · refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.add_ne_top.2 ⟨?_, ?_⟩))
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)
  · exact Finset.measurable_sum Q (fun q hq => psiK_meas q s (H.cont q (hQS q hq)))
  · intro g k
    exact Finset.sum_congr rfl (fun q _ => psiK_inv q s g k)
  · rw [lintegral_finsetSum Q (fun q hq => psiK_meas q s (H.cont q (hQS q hq)))]
    refine ENNReal.sum_lt_top.2 (fun q hq => ?_)
    obtain ⟨T', Cf, hT'S, hd⟩ := H.dom q (hQS q hq)
    exact psiK_lint q s T' Cf hd (fun h' hh' => hL h' (hT'S h' hh')) (fun h' hh' => H.cont h' (hT'S h' hh'))
  · have hq_ae : ∀ᵐ (x : PSub ε (A j)) ∂(ν j), ∀ k, (∫⁻ t in Set.Ioi (0 : ℝ),
        ‖F k (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (r j + 1) * t))) < ⊤ :=
      ae_all_iff.2 (fun k => H.qual (F k) (hFS k) j)
    filter_upwards [hq_ae] with x hx hτ
    have hx0 : 0 ≤ τ j x := hτ.1
    set a : ℝ≥0∞ := ENNReal.ofReal (Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ^ s) with ha
    set Pall : ℝ≥0∞ := ∫⁻ t : ℝ, Ψ (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t)) with hPall
    set L : (Matrix (Fin n) (Fin n) ℂ → ℂ) → ℝ≥0∞ := fun q => ∫⁻ t in Set.Ioi (0 : ℝ),
      ‖q (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (r j + s) * t)) with hLdef
    have hback : ∀ q ∈ Q, a * L q ≤ Cs * Pall := by
      intro q hq
      refine (back_line H hn j x hx0 q s hs).trans ?_
      refine mul_le_mul_right (lintegral_mono fun t => ?_) _
      refine mul_le_mul_left ?_ _
      exact Finset.single_le_sum (f := fun q => PsiK ε q s (S7.toM (x : S7.UJ ε) * aT (A j) t))
        (fun _ _ => zero_le) hq
    have hunit : ∀ k, ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖F k (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 ≤ E * L (F k) :=
      fun k => unit_line (fun t => F k (S7.toM (x : S7.UJ ε) * aT (A j) t)) (r j + s)
    have hsrc' : ∫⁻ t in Set.Ioi (0 : ℝ), ‖F 0 (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
        ENNReal.ofReal (Real.exp (2 * (r j + s + c'') * t)) ≤ cT * ∑ h' ∈ T, L h' := by
      rw [h0]
      exact src_line H j f₀ T hTS hsrc x hx0 (r j + s + c'') (r j + s) (by linarith)
    calc a * ∫⁻ t in Set.Ioi (0 : ℝ), ‖h (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
            ENNReal.ofReal (Real.exp (2 * (r j + s + c'') * t))
        ≤ a * (ENNReal.ofReal C₀ * (∑ k, ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖F k (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 +
          ∫⁻ t in Set.Ioi (0 : ℝ), ‖F 0 (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 *
            ENNReal.ofReal (Real.exp (2 * (r j + s + c'') * t)))) := mul_le_mul_right (hode x hx) a
      _ ≤ a * (ENNReal.ofReal C₀ * ∑ k : Fin (mm + 1), (E * L (F k) + cT * ∑ h' ∈ T, L h')) := by
          refine mul_le_mul_right (mul_le_mul_right (Finset.sum_le_sum fun k _ => ?_) _) _
          rw [lintegral_add_right _ measurable_const, setLIntegral_const, Real.volume_Ioc, sub_zero,
            ENNReal.ofReal_one, mul_one]
          exact add_le_add (hunit k) hsrc'
      _ = ENNReal.ofReal C₀ * ∑ k : Fin (mm + 1), (E * (a * L (F k)) + cT * ∑ h' ∈ T, a * L h') := by
          rw [mul_left_comm, Finset.mul_sum]
          refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
          rw [← Finset.mul_sum]
          ring
      _ ≤ ENNReal.ofReal C₀ * ∑ _k : Fin (mm + 1), (E * (Cs * Pall) + cT * ∑ _h' ∈ T, Cs * Pall) :=
          mul_le_mul_right (Finset.sum_le_sum fun k _ => add_le_add (mul_le_mul_right (hback _ (hFQ k)) _)
            (mul_le_mul_right (Finset.sum_le_sum fun h' hh' => hback _ (hTQ h' hh')) _)) _
      _ = ENNReal.ofReal C₀ * (((mm + 1 : ℕ) : ℝ≥0∞) * (E * Cs + cT * (cT * Cs))) * Pall := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hcT]
          ring

end CompanionTheory.RgExh.Dec.L.AB
