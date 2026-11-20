import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FrobeniusBoundOfMulNearOne

open MeasureTheory Matrix Topology Metric Formalism.REAL
open scoped ENNReal

noncomputable section

namespace CompanionTheory.Lime.T3

section frob

open scoped Matrix.Norms.Frobenius

/- English proof (translation)
Unfold `hs`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hs_box {n : ℕ} {u : Matrix (Fin n) (Fin n) ℂ} {s : ℝ} (h : ∀ i j, ‖u i j‖ ≤ s) : hs u ≤ (n * s) ^ 2 := by
  unfold hs
  calc ∑ i, ∑ j, ‖u i j‖ ^ 2 ≤ ∑ _i : Fin n, ∑ _j : Fin n, s ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
    _ = (n * s) ^ 2 := by simp; ring

/- English proof (translation)
Rewrite `hu`, `hv`, the goal using `[frobenius_eq_norm_sq]`. Establish `hu' : ‖u - 1‖ ≤ t` using `(pow_le_pow_iff_left₀ (norm_nonneg _) ht0 two_ne_zero).1 hu`. Establish `hv' : ‖v - 1‖ ≤ t` using `(pow_le_pow_iff_left₀ (norm_nonneg _) ht0 two_ne_zero).1 hv`. Establish `e : k - 1 = (v - 1) - (k - 1) * (u - 1) - (u - 1)` using `by rw [← h]; noncomm_ring`. Establish `h1 : ‖k - 1‖ ≤ ‖v - 1‖ + ‖k - 1‖ * ‖u - 1‖ + ‖u - 1‖`.

Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ‖k - 1‖ * ‖u - 1‖ ≤ ‖k - 1‖ * (1 / 2)` using `mul_le_mul_of_nonneg_left (hu'.trans ht) (norm_nonneg _)`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2`.
-/
theorem near_one {n : ℕ} {k u v : Matrix (Fin n) (Fin n) ℂ} {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2)
    (hu : hs (u - 1) ≤ t ^ 2) (hv : hs (v - 1) ≤ t ^ 2) (h : k * u = v) : hs (k - 1) ≤ (4 * t) ^ 2 := by
  rw [frobenius_eq_norm_sq] at hu hv ⊢
  have hu' : ‖u - 1‖ ≤ t := (pow_le_pow_iff_left₀ (norm_nonneg _) ht0 two_ne_zero).1 hu
  have hv' : ‖v - 1‖ ≤ t := (pow_le_pow_iff_left₀ (norm_nonneg _) ht0 two_ne_zero).1 hv
  have e : k - 1 = (v - 1) - (k - 1) * (u - 1) - (u - 1) := by rw [← h]; noncomm_ring
  have h1 : ‖k - 1‖ ≤ ‖v - 1‖ + ‖k - 1‖ * ‖u - 1‖ + ‖u - 1‖ := by
    calc ‖k - 1‖ = ‖(v - 1) - (k - 1) * (u - 1) - (u - 1)‖ := by rw [← e]
      _ ≤ ‖(v - 1) - (k - 1) * (u - 1)‖ + ‖u - 1‖ := norm_sub_le _ _
      _ ≤ ‖v - 1‖ + ‖(k - 1) * (u - 1)‖ + ‖u - 1‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ _ := by gcongr; exact Matrix.frobenius_norm_mul _ _
  have h2 : ‖k - 1‖ * ‖u - 1‖ ≤ ‖k - 1‖ * (1 / 2) := mul_le_mul_of_nonneg_left (hu'.trans ht) (norm_nonneg _)
  exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2

/- English proof (translation)
Rewrite `hg`, `hu` using `[frobenius_eq_norm_sq]`. Establish `hg' : ‖g‖ ≤ R` using `(pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).1 hg`. Establish `hu1 : ‖u - 1‖ ≤ 1 / 2` using `(pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).1 hu`. Establish `hu' : ‖u‖ ≤ Real.sqrt n + 1`. Combine the equalities or inequalities in the displayed calculation.

Establish `he : ‖(g * u) i j‖ ≤ ‖g * u‖`. Use `f1auxiliary_entry_le (g * u) i j` as an intermediate fact. Rewrite `this` using `[frobenius_eq_norm_sq]`. Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem entry_le {n : ℕ} {g u : Matrix (Fin n) (Fin n) ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hg : hs g ≤ R ^ 2) (hu : hs (u - 1) ≤ (1 / 2) ^ 2) (i j : Fin n) : ‖(g * u) i j‖ ≤ R * (Real.sqrt n + 1) := by
  rw [frobenius_eq_norm_sq] at hg hu
  have hg' : ‖g‖ ≤ R := (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).1 hg
  have hu1 : ‖u - 1‖ ≤ 1 / 2 := (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).1 hu
  have hu' : ‖u‖ ≤ Real.sqrt n + 1 := by
    calc ‖u‖ = ‖1 + (u - 1)‖ := by rw [add_sub_cancel]
      _ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ + ‖u - 1‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_one_matrix_eq_sqrt]; linarith
  have he : ‖(g * u) i j‖ ≤ ‖g * u‖ := by
    have := f1auxiliary_entry_le (g * u) i j
    rw [frobenius_eq_norm_sq] at this
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  calc ‖(g * u) i j‖ ≤ ‖g * u‖ := he
    _ ≤ ‖g‖ * ‖u‖ := Matrix.frobenius_norm_mul _ _
    _ ≤ R * (Real.sqrt n + 1) := by gcongr

end frob

def nearSet {n : ℕ} (ε : Fin n → Bool) (δ : ℝ) : Set (UJ ε) := {k | hs (coeMatrixAlt ε k - 1) ≤ δ ^ 2}

/- English proof (translation)
Establish `hn' : (0 : ℝ) < n` using `by exact_mod_cast hn`. Set `lam : Measure (MatrixCoordinates n)` to `Measure.addHaar`. Use `set s : ℝ := δ / (4 * n) with hs_def`. Establish `hs0 : 0 < s` using `by positivity`. Establish `hns : n * s = δ / 4` using `by rw [hs_def]; field_simp`.

Set `O : Set (MatrixCoordinates n)` to `closedBall (Matrix.of.symm 1) s`. Establish `hO : ∀ x ∈ O, hs (Matrix.of x - 1) ≤ (δ / 4) ^ 2`. Introduce `x hx`. Rewrite using `[← hns]`. Use `hs_box fun i j => ?_` and prove the remaining obligations.

Use `set o : MatrixCoordinates n := Matrix.of.symm 1 with ho`. Establish `h1 : ‖x - o‖ ≤ s` using `by rwa [← mem_closedBall_iff_norm]`. Conclude with `((norm_le_pi_norm ((x - o) i) j).trans (norm_le_pi_norm (x - o) i)).trans h1`. Establish `hof : Continuous (fun x : MatrixCoordinates n => Matrix.of x)` using `continuous_id`. Establish `hofs : Continuous (fun x : Matrix (Fin n) (Fin n) ℂ => (Matrix.of.symm x : MatrixCoordinates n))` using `continuous_id`.

Establish `hfr : Module.finrank ℝ (MatrixCoordinates n) = 2 * n ^ 2`. Simplify using `[MatrixCoordinates, Module.finrank_pi_fintype, Complex.finrank_real_complex]`. Expand and normalize the polynomial expressions, which then agree. Establish `hB_pos : 0 < lam (ball 0 1)` using `measure_ball_pos lam _ one_pos`. Establish `hB_fin : lam (ball 0 1) < ⊤` using `measure_ball_lt_top`.

Establish `hOv : lam O = ENNReal.ofReal (s ^ (2 * n ^ 2)) * lam (ball 0 1)`. Rewrite using `[Measure.addHaar_closedBall lam _ hs0.le, hfr]`. Use `set W := nearSet ε δ`. Use `set ρ : ℝ := R * (Real.sqrt n + 1) with hρ`. Establish `hρ0 : 0 ≤ ρ` using `by positivity`.

Use `set S : Set (UJ ε) := {g | hsG g ≤ R ^ 2} with hS`. Establish `hS_meas : MeasurableSet S` using `(isClosed_le (continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)) continuous_const).measurableSet`. Set `Φ : UJ ε × MatrixCoordinates n → MatrixCoordinates n` to `fun p => leftMulReal (coeMatrixAlt ε p.1⁻¹) p.2`. Establish `hΦ : Continuous Φ` using `by show Continuous fun p : UJ ε × MatrixCoordinates n => (Matrix.of.symm (coeMatrixAlt ε p.1⁻¹ * Matrix.of p.2) : MatrixCoordinates n)`. Conclude with `hofs.comp (((continuous_coeMatrix ε).comp (continuous_inv.comp continuous_fst)).matrix_mul (hof.comp continuous_snd))`.

Set `T : Set (UJ ε × MatrixCoordinates n)` to `{p | hsG p.1 ≤ R ^ 2} ∩ Φ ⁻¹' O`. Establish `hT : MeasurableSet T` using `(isClosed_le ((continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)).comp continuous_fst) continuous_const).measurableSet.inter (isClosed_closedBall.preimage hΦ).measurableSet`. Establish `h1 : (μ.prod lam) T = μ S * lam O`. Rewrite using `[Measure.prod_apply hT]`. Establish `: ∀ g, lam (Prod.mk g ⁻¹' T) = S.indicator (fun _ => lam O) g`.

Introduce `g`. Distinguish the cases in `hg : g ∈ S`. Rewrite using `[Set.indicator_of_mem hg]`. Establish `hdet : LinearMap.det (leftMulReal (coeMatrixAlt ε g⁻¹)) = 1` using `det_leftMulReal_eq_one (g⁻¹).2`. Establish `e : Prod.mk g ⁻¹' T = leftMulReal (coeMatrixAlt ε g⁻¹) ⁻¹' O`.

Use extensionality with `x`. Simplify using `only [T, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, Φ]`. Conclude with `⟨fun h => h.2, fun h => ⟨hg, h⟩⟩`. Rewrite using `[e, Measure.addHaar_preimage_linearMap lam (by rw [hdet]; exact one_ne_zero), hdet]`. Simplify using the standard rewrite rules.

Rewrite using `[Set.indicator_of_notMem hg]`. Establish `e : Prod.mk g ⁻¹' T = ∅`. Use extensionality with `x`. Simplify using `only [T, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]`. Conclude with `fun h => absurd h hg`.

Rewrite using `[e, measure_empty]`. Repeatedly rewrite using `[this]`. Rewrite using `[lintegral_indicator_const hS_meas, mul_comm]`. Establish `hq : (δ / 4) ^ 2 ≤ (1 / 2 : ℝ) ^ 2` using `pow_le_pow_left₀ (by positivity) (by linarith) 2`. Establish `h2 : (μ.prod lam) T ≤ μ W * lam (closedBall 0 ρ)`.

Rewrite using `[Measure.prod_apply_symm hT]`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hne : ((fun g => (g, x)) ⁻¹' T).Nonempty`. Take `⟨h, hh⟩` from `hne`.

Establish `hh1 : hsG h ≤ R ^ 2` using `hh.1`. Establish `hh2` using `hO _ hh.2`. Simplify using `only [Φ] at hh2`. Rewrite `hh2` using `[of_leftMulReal_apply]`. Establish `hx : x ∈ closedBall (0 : MatrixCoordinates n) ρ`.

Rewrite using `[mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hρ0]`. Introduce `i`. Rewrite using `[pi_norm_le_iff_of_nonneg hρ0]`. Introduce `j`. Use `entry_le (g := coeMatrixAlt ε h) hR0 hh1 (hh2.trans hq) i j` as an intermediate fact.

Rewrite `this` using `[← Matrix.mul_assoc, determinant_character_mul_inv, Matrix.one_mul]`. Conclude with `this`. Rewrite using `[Set.indicator_of_mem hx]`. Combine the equalities or inequalities in the displayed calculation. Use `measure_mono fun g hg => ?_` and prove the remaining obligations.

Establish `hg2` using `hO _ hg.2`. Simplify using `only [Φ] at hg2`. Rewrite `hg2` using `[of_leftMulReal_apply]`. Use `show hs (coeMatrixAlt ε (h⁻¹ * g) - 1) ≤ δ ^ 2`. Use `near_one (k := coeMatrixAlt ε (h⁻¹ * g)) (by positivity) (by linarith) hg2 hh2 (by` as an intermediate fact.

Rewrite using `[determinant_character_mul, ← Matrix.mul_assoc, Matrix.mul_assoc (coeMatrixAlt ε h⁻¹), determinant_character_mul_inv, Matrix.mul_one])`. Rewrite `this` using `[show 4 * (δ / 4) = δ by ring]`. Then use the resulting hypothesis. Use `_ = μ W := measure_preimage_mul μ h⁻¹ W`. Rewrite using `[Set.not_nonempty_iff_eq_empty.1 hne, measure_empty]`. Conclude with `bot_le`.

Use `_ = μ W * lam (closedBall 0 ρ) := lintegral_indicator_const measurableSet_closedBall _`. Establish `h3 : lam (closedBall 0 ρ) = ENNReal.ofReal (ρ ^ (2 * n ^ 2)) * lam (ball 0 1)`. Rewrite using `[Measure.addHaar_closedBall lam _ hρ0, hfr]`. Establish `hO0 : lam O ≠ 0`. Rewrite using `[hOv]; exact mul_ne_zero (ENNReal.ofReal_pos.2 (by positivity)).ne' hB_pos.ne'`.

Establish `hOt : lam O ≠ ⊤` using `measure_closedBall_lt_top.ne`. Use `(ENNReal.mul_le_mul_iff_left hO0 hOt).1 ?_` and prove the remaining obligations. Rewrite using `[← h1]`. Use `h2.trans (le_of_eq ?_)` and prove the remaining obligations. Establish `e : ρ ^ (2 * n ^ 2) = (4 * n * (Real.sqrt n + 1) * R / δ) ^ (2 * n ^ 2) * s ^ (2 * n ^ 2)`.

Rewrite using `[← mul_pow]`. Use `congr 1`. Rewrite using `[hρ, hs_def]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h3, hOv, e, ENNReal.ofReal_mul (by positivity)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem vol_ratio {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [SFinite μ] [μ.IsMulLeftInvariant]
    {δ R : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2) (hR0 : 0 ≤ R) :
    μ {g | hsG g ≤ R ^ 2} ≤ ENNReal.ofReal ((4 * n * (Real.sqrt n + 1) * R / δ) ^ (2 * n ^ 2)) * μ (nearSet ε δ) := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let lam : Measure (MatrixCoordinates n) := Measure.addHaar
  set s : ℝ := δ / (4 * n) with hs_def
  have hs0 : 0 < s := by positivity
  have hns : n * s = δ / 4 := by rw [hs_def]; field_simp
  let O : Set (MatrixCoordinates n) := closedBall (Matrix.of.symm 1) s
  have hO : ∀ x ∈ O, hs (Matrix.of x - 1) ≤ (δ / 4) ^ 2 := by
    intro x hx
    rw [← hns]
    refine hs_box fun i j => ?_
    set o : MatrixCoordinates n := Matrix.of.symm 1 with ho
    have h1 : ‖x - o‖ ≤ s := by rwa [← mem_closedBall_iff_norm]
    exact ((norm_le_pi_norm ((x - o) i) j).trans (norm_le_pi_norm (x - o) i)).trans h1
  have hof : Continuous (fun x : MatrixCoordinates n => Matrix.of x) := continuous_id
  have hofs : Continuous (fun x : Matrix (Fin n) (Fin n) ℂ => (Matrix.of.symm x : MatrixCoordinates n)) := continuous_id
  have hfr : Module.finrank ℝ (MatrixCoordinates n) = 2 * n ^ 2 := by
    simp [MatrixCoordinates, Module.finrank_pi_fintype, Complex.finrank_real_complex]; ring
  have hB_pos : 0 < lam (ball 0 1) := measure_ball_pos lam _ one_pos
  have hB_fin : lam (ball 0 1) < ⊤ := measure_ball_lt_top
  have hOv : lam O = ENNReal.ofReal (s ^ (2 * n ^ 2)) * lam (ball 0 1) := by
    rw [Measure.addHaar_closedBall lam _ hs0.le, hfr]
  set W := nearSet ε δ
  set ρ : ℝ := R * (Real.sqrt n + 1) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  set S : Set (UJ ε) := {g | hsG g ≤ R ^ 2} with hS
  have hS_meas : MeasurableSet S :=
    (isClosed_le (continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)) continuous_const).measurableSet
  let Φ : UJ ε × MatrixCoordinates n → MatrixCoordinates n := fun p => leftMulReal (coeMatrixAlt ε p.1⁻¹) p.2
  have hΦ : Continuous Φ := by
    show Continuous fun p : UJ ε × MatrixCoordinates n =>
      (Matrix.of.symm (coeMatrixAlt ε p.1⁻¹ * Matrix.of p.2) : MatrixCoordinates n)
    exact hofs.comp (((continuous_coeMatrix ε).comp (continuous_inv.comp continuous_fst)).matrix_mul
      (hof.comp continuous_snd))
  let T : Set (UJ ε × MatrixCoordinates n) := {p | hsG p.1 ≤ R ^ 2} ∩ Φ ⁻¹' O
  have hT : MeasurableSet T :=
    (isClosed_le ((continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)).comp continuous_fst)
      continuous_const).measurableSet.inter (isClosed_closedBall.preimage hΦ).measurableSet
  have h1 : (μ.prod lam) T = μ S * lam O := by
    rw [Measure.prod_apply hT]
    have : ∀ g, lam (Prod.mk g ⁻¹' T) = S.indicator (fun _ => lam O) g := by
      intro g
      by_cases hg : g ∈ S
      · rw [Set.indicator_of_mem hg]
        have hdet : LinearMap.det (leftMulReal (coeMatrixAlt ε g⁻¹)) = 1 := det_leftMulReal_eq_one (g⁻¹).2
        have e : Prod.mk g ⁻¹' T = leftMulReal (coeMatrixAlt ε g⁻¹) ⁻¹' O := by
          ext x
          simp only [T, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, Φ]
          exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
        rw [e, Measure.addHaar_preimage_linearMap lam (by rw [hdet]; exact one_ne_zero), hdet]
        simp
      · rw [Set.indicator_of_notMem hg]
        have e : Prod.mk g ⁻¹' T = ∅ := by
          ext x
          simp only [T, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq,
            Set.mem_empty_iff_false, iff_false, not_and]
          exact fun h => absurd h hg
        rw [e, measure_empty]
    simp_rw [this]
    rw [lintegral_indicator_const hS_meas, mul_comm]
  have hq : (δ / 4) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h2 : (μ.prod lam) T ≤ μ W * lam (closedBall 0 ρ) := by
    rw [Measure.prod_apply_symm hT]
    calc ∫⁻ x, μ ((fun g => (g, x)) ⁻¹' T) ∂lam
        ≤ ∫⁻ x, (closedBall (0 : MatrixCoordinates n) ρ).indicator (fun _ => μ W) x ∂lam := by
          refine lintegral_mono fun x => ?_
          by_cases hne : ((fun g => (g, x)) ⁻¹' T).Nonempty
          · obtain ⟨h, hh⟩ := hne
            have hh1 : hsG h ≤ R ^ 2 := hh.1
            have hh2 := hO _ hh.2
            simp only [Φ] at hh2
            rw [of_leftMulReal_apply] at hh2
            have hx : x ∈ closedBall (0 : MatrixCoordinates n) ρ := by
              rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hρ0]
              intro i
              rw [pi_norm_le_iff_of_nonneg hρ0]
              intro j
              have := entry_le (g := coeMatrixAlt ε h) hR0 hh1 (hh2.trans hq) i j
              rw [← Matrix.mul_assoc, determinant_character_mul_inv, Matrix.one_mul] at this
              exact this
            rw [Set.indicator_of_mem hx]
            calc μ ((fun g => (g, x)) ⁻¹' T) ≤ μ ((fun g => h⁻¹ * g) ⁻¹' W) := by
                  refine measure_mono fun g hg => ?_
                  have hg2 := hO _ hg.2
                  simp only [Φ] at hg2
                  rw [of_leftMulReal_apply] at hg2
                  show hs (coeMatrixAlt ε (h⁻¹ * g) - 1) ≤ δ ^ 2
                  have := near_one (k := coeMatrixAlt ε (h⁻¹ * g)) (by positivity) (by linarith) hg2 hh2 (by
                    rw [determinant_character_mul, ← Matrix.mul_assoc, Matrix.mul_assoc (coeMatrixAlt ε h⁻¹),
                      determinant_character_mul_inv, Matrix.mul_one])
                  rwa [show 4 * (δ / 4) = δ by ring] at this
              _ = μ W := measure_preimage_mul μ h⁻¹ W
          · rw [Set.not_nonempty_iff_eq_empty.1 hne, measure_empty]
            exact bot_le
      _ = μ W * lam (closedBall 0 ρ) := lintegral_indicator_const measurableSet_closedBall _
  have h3 : lam (closedBall 0 ρ) = ENNReal.ofReal (ρ ^ (2 * n ^ 2)) * lam (ball 0 1) := by
    rw [Measure.addHaar_closedBall lam _ hρ0, hfr]
  have hO0 : lam O ≠ 0 := by
    rw [hOv]; exact mul_ne_zero (ENNReal.ofReal_pos.2 (by positivity)).ne' hB_pos.ne'
  have hOt : lam O ≠ ⊤ := measure_closedBall_lt_top.ne
  refine (ENNReal.mul_le_mul_iff_left hO0 hOt).1 ?_
  rw [← h1]
  refine h2.trans (le_of_eq ?_)
  have e : ρ ^ (2 * n ^ 2) = (4 * n * (Real.sqrt n + 1) * R / δ) ^ (2 * n ^ 2) * s ^ (2 * n ^ 2) := by
    rw [← mul_pow]
    congr 1
    rw [hρ, hs_def]
    field_simp
  rw [h3, hOv, e, ENNReal.ofReal_mul (by positivity)]
  ring

/- English proof (translation)
Set `j : Fin n` to `⟨0, hn⟩`. Establish `hg : inUJ ε (coeMatrixAlt ε g)` using `g.2`. Establish `h1` using `congrFun (congrFun hg j) j`. Establish `h2 : ((coeMatrixAlt ε g)ᴴ * Jm ε * coeMatrixAlt ε g) j j = ∑ i, (if ε i then 1 else -1) * (((‖coeMatrixAlt ε g i j‖ ^ 2 : ℝ)) : ℂ)`. Simplify using `only [Jm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `Complex.conj_mul' (coeMatrixAlt ε g i j)` as an intermediate fact. Apply the tactic sequence `split_ifs <;> simp [← this]`. Apply the tactic sequence `have h3 : ‖Jm ε j j‖ = 1 := by simp only [Jm, Matrix.diagonal_apply_eq]; split_ifs <;> simp`. Establish `h4 : (1 : ℝ) ≤ ∑ i, ‖coeMatrixAlt ε g i j‖ ^ 2`.

Rewrite using `[← h3, ← h1, h2]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]`. Apply the tactic sequence `split_ifs <;> simp`. Use `h4.trans ?_` and prove the remaining obligations.

Use `show _ ≤ ∑ i, ∑ k, ‖coeMatrixAlt ε g i k‖ ^ 2`. Conclude with `Finset.sum_le_sum fun i _ => Finset.single_le_sum (f := fun k => ‖coeMatrixAlt ε g i k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)`.
-/
theorem one_le_hsG {n : ℕ} (hn : 1 ≤ n) {ε : Fin n → Bool} (g : UJ ε) : 1 ≤ hsG g := by
  let j : Fin n := ⟨0, hn⟩
  have hg : inUJ ε (coeMatrixAlt ε g) := g.2
  have h1 := congrFun (congrFun hg j) j
  have h2 : ((coeMatrixAlt ε g)ᴴ * Jm ε * coeMatrixAlt ε g) j j =
      ∑ i, (if ε i then 1 else -1) * (((‖coeMatrixAlt ε g i j‖ ^ 2 : ℝ)) : ℂ) := by
    simp only [Jm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := Complex.conj_mul' (coeMatrixAlt ε g i j)
    split_ifs <;> simp [← this]
  have h3 : ‖Jm ε j j‖ = 1 := by simp only [Jm, Matrix.diagonal_apply_eq]; split_ifs <;> simp
  have h4 : (1 : ℝ) ≤ ∑ i, ‖coeMatrixAlt ε g i j‖ ^ 2 := by
    rw [← h3, ← h1, h2]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    split_ifs <;> simp
  refine h4.trans ?_
  show _ ≤ ∑ i, ∑ k, ‖coeMatrixAlt ε g i k‖ ^ 2
  exact Finset.sum_le_sum fun i _ =>
    Finset.single_le_sum (f := fun k => ‖coeMatrixAlt ε g i k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)

/- English proof (translation)
Use `set c : ℝ := 8 * n * (Real.sqrt n + 1) / δ with hc`. Establish `hc0 : 0 ≤ c` using `by positivity`. Set `S : ℕ → Set (UJ ε)` to `fun j => {g | hsG g ≤ ((2 : ℝ) ^ (j + 1)) ^ 2}`. Establish `hSm : ∀ j, MeasurableSet (S j)` using `fun j => (isClosed_le (continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)) continuous_const).measurableSet`. Establish `hpt : ∀ g : UJ ε, ENNReal.ofReal ((Real.sqrt (hsG g))⁻¹ ^ A) ≤ ∑' j, (S j).indicator (fun _ => ENNReal.ofReal (((2 : ℝ) ^ j)⁻¹ ^ A)) g`.

Introduce `g`. Establish `h1 : 1 ≤ Real.sqrt (hsG g)` using `Real.one_le_sqrt.2 (one_le_hsG hn g)`. Take `⟨j, hj1, hj2⟩` from `exists_nat_pow_near h1 (by norm_num : (1 : ℝ) < 2)`. Use `le_trans ?_ (ENNReal.le_tsum j)` and prove the remaining obligations. Establish `hmem : g ∈ S j` using `by show hsG g ≤ _`.

Rewrite using `[← Real.sq_sqrt (le_trans zero_le_one (one_le_hsG hn g))]`. Conclude with `pow_le_pow_left₀ (Real.sqrt_nonneg _) hj2.le 2`. Rewrite using `[Set.indicator_of_mem hmem]`. Conclude with `ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) (inv_anti₀ (by positivity) hj1) A)`. Use `(lintegral_mono hpt).trans ?_` and prove the remaining obligations.

Rewrite using `[lintegral_tsum fun j => (measurable_const.indicator (hSm j)).aemeasurable]`. Establish `hterm : ∀ j, ∫⁻ g, (S j).indicator (fun _ => ENNReal.ofReal (((2 : ℝ) ^ j)⁻¹ ^ A)) g ∂μ ≤ ENNReal.ofReal (c ^ (2 * n ^ 2) * (1 / 2) ^ j) * μ (nearSet ε δ)`. Introduce `j`. Rewrite using `[lintegral_indicator_const (hSm j)]`. Use `(mul_le_mul_right (vol_ratio hn ε μ hδ hδ2 (by positivity)) _).trans ?_` and prove the remaining obligations.

Rewrite using `[← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]`. Use `mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _` and prove the remaining obligations. Establish `e : 4 * n * (Real.sqrt n + 1) * (2 : ℝ) ^ (j + 1) / δ = c * 2 ^ j` using `by rw [hc]; ring`. Establish `h2 : (1 : ℝ) ≤ 2 ^ j` using `one_le_pow₀ (by norm_num)`. Establish `h3 : ((2 : ℝ) ^ j)⁻¹ ^ A ≤ ((2 : ℝ) ^ j)⁻¹ ^ (2 * n ^ 2 + 1)` using `pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ h2) hA`.

Establish `h4 : ((2 : ℝ) ^ j)⁻¹ ^ (2 * n ^ 2 + 1) * (c * 2 ^ j) ^ (2 * n ^ 2) = c ^ (2 * n ^ 2) * (1 / 2) ^ j`. Rewrite using `[mul_pow, pow_succ, inv_pow, one_div, inv_pow]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, ← h4]`. Conclude with `mul_le_mul_of_nonneg_right h3 (by positivity)`.

Use `(ENNReal.tsum_le_tsum hterm).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) (summable_geometric_two.mul_left _), tsum_mul_left, tsum_geometric_two, mul_comm (c ^ _)]`.
-/
theorem int_ratio {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [SFinite μ] [μ.IsMulLeftInvariant]
    {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2) {A : ℕ} (hA : 2 * n ^ 2 + 1 ≤ A) :
    ∫⁻ g, ENNReal.ofReal ((Real.sqrt (hsG g))⁻¹ ^ A) ∂μ ≤
      ENNReal.ofReal (2 * (8 * n * (Real.sqrt n + 1) / δ) ^ (2 * n ^ 2)) * μ (nearSet ε δ) := by
  set c : ℝ := 8 * n * (Real.sqrt n + 1) / δ with hc
  have hc0 : 0 ≤ c := by positivity
  let S : ℕ → Set (UJ ε) := fun j => {g | hsG g ≤ ((2 : ℝ) ^ (j + 1)) ^ 2}
  have hSm : ∀ j, MeasurableSet (S j) := fun j =>
    (isClosed_le (continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)) continuous_const).measurableSet
  have hpt : ∀ g : UJ ε, ENNReal.ofReal ((Real.sqrt (hsG g))⁻¹ ^ A) ≤
      ∑' j, (S j).indicator (fun _ => ENNReal.ofReal (((2 : ℝ) ^ j)⁻¹ ^ A)) g := by
    intro g
    have h1 : 1 ≤ Real.sqrt (hsG g) := Real.one_le_sqrt.2 (one_le_hsG hn g)
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near h1 (by norm_num : (1 : ℝ) < 2)
    refine le_trans ?_ (ENNReal.le_tsum j)
    have hmem : g ∈ S j := by
      show hsG g ≤ _
      rw [← Real.sq_sqrt (le_trans zero_le_one (one_le_hsG hn g))]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hj2.le 2
    rw [Set.indicator_of_mem hmem]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) (inv_anti₀ (by positivity) hj1) A)
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_tsum fun j => (measurable_const.indicator (hSm j)).aemeasurable]
  have hterm : ∀ j, ∫⁻ g, (S j).indicator (fun _ => ENNReal.ofReal (((2 : ℝ) ^ j)⁻¹ ^ A)) g ∂μ ≤
      ENNReal.ofReal (c ^ (2 * n ^ 2) * (1 / 2) ^ j) * μ (nearSet ε δ) := by
    intro j
    rw [lintegral_indicator_const (hSm j)]
    refine (mul_le_mul_right (vol_ratio hn ε μ hδ hδ2 (by positivity)) _).trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    have e : 4 * n * (Real.sqrt n + 1) * (2 : ℝ) ^ (j + 1) / δ = c * 2 ^ j := by rw [hc]; ring
    have h2 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have h3 : ((2 : ℝ) ^ j)⁻¹ ^ A ≤ ((2 : ℝ) ^ j)⁻¹ ^ (2 * n ^ 2 + 1) :=
      pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ h2) hA
    have h4 : ((2 : ℝ) ^ j)⁻¹ ^ (2 * n ^ 2 + 1) * (c * 2 ^ j) ^ (2 * n ^ 2) = c ^ (2 * n ^ 2) * (1 / 2) ^ j := by
      rw [mul_pow, pow_succ, inv_pow, one_div, inv_pow]
      field_simp
    rw [e, ← h4]
    exact mul_le_mul_of_nonneg_right h3 (by positivity)
  refine (ENNReal.tsum_le_tsum hterm).trans (le_of_eq ?_)
  rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
    (summable_geometric_two.mul_left _), tsum_mul_left, tsum_geometric_two, mul_comm (c ^ _)]

end CompanionTheory.Lime.T3
