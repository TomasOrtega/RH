import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PoissonSummationInfinitePlaceGaussianLattice

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (hs)

noncomputable section

namespace GlobalTheory.LeviIso.RadLoc

section
open scoped Matrix.Norms.Frobenius

/- English proof (translation)
Rewrite using `[Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]`. Simplify using `[hs]`.
-/
theorem hs_eq_norm_sq {j : ℕ} (M : Matrix (Fin j) (Fin j) ℂ) : hs M = ‖M‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp [hs]

/- English proof (translation)
Simplify using `only [hs_eq_norm_sq] at *`. Establish `e : (x⁻¹ - 1) + (x - 1) = -((x⁻¹ - 1) * (x - 1))`. Rewrite using `[sub_mul, mul_sub, Matrix.nonsing_inv_mul _ (Ne.isUnit hx)]`. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.

Establish `h1 : ‖(x⁻¹ - 1) + (x - 1)‖ ≤ ‖x⁻¹ - 1‖ * ‖x - 1‖`. Rewrite using `[e, norm_neg]`. Conclude with `norm_mul_le _ _`. Establish `h2 : ‖x⁻¹ - 1‖ ≤ ‖(x⁻¹ - 1) + (x - 1)‖ + ‖x - 1‖`. Simplify using `using norm_sub_le ((x⁻¹ - 1) + (x - 1)) (x - 1)`.

Establish `h3 : ‖x - 1‖ ≤ ‖(x⁻¹ - 1) + (x - 1)‖ + ‖x⁻¹ - 1‖`. Simplify using `using norm_sub_le ((x⁻¹ - 1) + (x - 1)) (x⁻¹ - 1)`. Establish `hA` using `norm_nonneg (x - 1)`. Establish `hB` using `norm_nonneg (x⁻¹ - 1)`. Generalize the expression as in `‖x - 1‖ = A at *`.

Generalize the expression as in `‖x⁻¹ - 1‖ = B at *`. Establish `h4 : B ≤ 1 - a` using `(sq_le_sq₀ hB (by linarith)).1 h`. Establish `h5 : B * A ≤ (1 - a) * A` using `mul_le_mul_of_nonneg_right h4 hA`. Rewrite using `[← mul_pow, ← mul_pow, sq_le_sq₀ (by positivity) hB, sq_le_sq₀ (by positivity) hA]`. Prove the components needed by the constructor for the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h6 : a * B ≤ a * ((2 - a) * A)` using `mul_le_mul_of_nonneg_left (by linarith) ha.le`. Use polynomial arithmetic with `[mul_nonneg (sq_nonneg (1 - a)) hA]`.
-/
theorem hs_inv_compare {j : ℕ} (x : Matrix (Fin j) (Fin j) ℂ) (hx : x.det ≠ 0) {a : ℝ} (ha : 0 < a)
    (ha1 : a < 1) (h : hs (x⁻¹ - 1) ≤ (1 - a) ^ 2) :
    a ^ 2 * hs (x - 1) ≤ hs (x⁻¹ - 1) ∧ a ^ 2 * hs (x⁻¹ - 1) ≤ hs (x - 1) := by
  simp only [hs_eq_norm_sq] at *
  have e : (x⁻¹ - 1) + (x - 1) = -((x⁻¹ - 1) * (x - 1)) := by
    rw [sub_mul, mul_sub, Matrix.nonsing_inv_mul _ (Ne.isUnit hx)]
    simp
    abel
  have h1 : ‖(x⁻¹ - 1) + (x - 1)‖ ≤ ‖x⁻¹ - 1‖ * ‖x - 1‖ := by
    rw [e, norm_neg]; exact norm_mul_le _ _
  have h2 : ‖x⁻¹ - 1‖ ≤ ‖(x⁻¹ - 1) + (x - 1)‖ + ‖x - 1‖ := by
    simpa using norm_sub_le ((x⁻¹ - 1) + (x - 1)) (x - 1)
  have h3 : ‖x - 1‖ ≤ ‖(x⁻¹ - 1) + (x - 1)‖ + ‖x⁻¹ - 1‖ := by
    simpa using norm_sub_le ((x⁻¹ - 1) + (x - 1)) (x⁻¹ - 1)
  have hA := norm_nonneg (x - 1)
  have hB := norm_nonneg (x⁻¹ - 1)
  generalize ‖x - 1‖ = A at *
  generalize ‖x⁻¹ - 1‖ = B at *
  have h4 : B ≤ 1 - a := (sq_le_sq₀ hB (by linarith)).1 h
  have h5 : B * A ≤ (1 - a) * A := mul_le_mul_of_nonneg_right h4 hA
  rw [← mul_pow, ← mul_pow, sq_le_sq₀ (by positivity) hB, sq_le_sq₀ (by positivity) hA]
  constructor
  · linarith
  · have h6 : a * B ≤ a * ((2 - a) * A) := mul_le_mul_of_nonneg_left (by linarith) ha.le
    nlinarith [mul_nonneg (sq_nonneg (1 - a)) hA]

end

/- English proof (translation)
Unfold `hs`. Check the signs of the components of the expression.
-/
theorem hs_nonneg {j : ℕ} (M : Matrix (Fin j) (Fin j) ℂ) : 0 ≤ hs M := by
  unfold hs; positivity

/- English proof (translation)
Unfold `hs`. Use `fun_prop`.
-/
theorem continuous_hs {j : ℕ} : Continuous (hs : Matrix (Fin j) (Fin j) ℂ → ℝ) := by
  unfold hs; fun_prop

def unitBallAt (j : ℕ) (s : ℝ) : Set (Fin j → Fin j → ℂ) := {x | hs (Matrix.of x - 1) ≤ s ^ 2}

/- English proof (translation)
Use `(isClosed_le (continuous_hs.comp ?_) continuous_const).measurableSet` and prove the remaining obligations. Conclude with `(continuous_id (X := Matrix (Fin j) (Fin j) ℂ)).sub continuous_const`.
-/
theorem measurableSet_unitBallAt (j : ℕ) (s : ℝ) : MeasurableSet (unitBallAt j s) := by
  refine (isClosed_le (continuous_hs.comp ?_) continuous_const).measurableSet
  exact (continuous_id (X := Matrix (Fin j) (Fin j) ℂ)).sub continuous_const

/- English proof (translation)
Establish `hd : Module.finrank ℝ (EuclideanSpace ℂ (Fin j × Fin j)) = 2 * j ^ 2`. Rewrite using `[(WithLp.linearEquiv 2 ℝ (Fin j × Fin j → ℂ)).finrank_eq, Module.finrank_pi_fintype]`. Simplify using `[Complex.finrank_real_complex]`. Expand and normalize the polynomial expressions, which then agree. Use `set e := PoissonV.coords (Fin j) (Fin j) with he`.

Rewrite using `[← (PoissonV.measurePreserving_coords (Fin j) (Fin j)).measure_preimage (measurableSet_unitBallAt j s).nullMeasurableSet, ← he]`. Establish `h1 : e ⁻¹' unitBallAt j s = Metric.closedBall (e.symm (Matrix.of.symm (1 : Matrix (Fin j) (Fin j) ℂ))) s`. Use extensionality with `z`. Rewrite using `[mem_closedBall_iff_norm, ← sq_le_sq₀ (norm_nonneg _) hs0.le, ← PoissonV.norm_sq_coords, ← he, map_sub, e.apply_symm_apply]`. Both sides reduce to the same expression.

Rewrite using `[h1, Measure.addHaar_closedBall _ _ hs0.le, hd]`. Use `congr 1`. Rewrite using `[← hd]`. Establish `h` using `(stdOrthonormalBasis ℝ (EuclideanSpace ℂ (Fin j × Fin j))).measurePreserving_repr`. Rewrite using `[← h.measure_preimage measurableSet_ball.nullMeasurableSet]`.

Use `congr 1`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem volume_unitBallAt (j : ℕ) {s : ℝ} (hs0 : 0 < s) :
    volume (unitBallAt j s) = ENNReal.ofReal (s ^ (2 * j ^ 2)) *
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) := by
  have hd : Module.finrank ℝ (EuclideanSpace ℂ (Fin j × Fin j)) = 2 * j ^ 2 := by
    rw [(WithLp.linearEquiv 2 ℝ (Fin j × Fin j → ℂ)).finrank_eq, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
    ring
  set e := PoissonV.coords (Fin j) (Fin j) with he
  rw [← (PoissonV.measurePreserving_coords (Fin j) (Fin j)).measure_preimage
    (measurableSet_unitBallAt j s).nullMeasurableSet, ← he]
  have h1 : e ⁻¹' unitBallAt j s =
      Metric.closedBall (e.symm (Matrix.of.symm (1 : Matrix (Fin j) (Fin j) ℂ))) s := by
    ext z
    rw [mem_closedBall_iff_norm, ← sq_le_sq₀ (norm_nonneg _) hs0.le, ← PoissonV.norm_sq_coords, ← he,
      map_sub, e.apply_symm_apply]
    rfl
  rw [h1, Measure.addHaar_closedBall _ _ hs0.le, hd]
  congr 1
  rw [← hd]
  have h := (stdOrthonormalBasis ℝ (EuclideanSpace ℂ (Fin j × Fin j))).measurePreserving_repr
  rw [← h.measure_preimage measurableSet_ball.nullMeasurableSet]
  congr 1
  ext x
  simp

/- English proof (translation)
Take `⟨δ, hδ, H⟩` from `Metric.eventually_nhds_iff.1 h`. Use `⟨δ, hδ, fun s hs0 hsδ x hx => H (lt_of_le_of_lt ?_ hsδ)⟩` and prove the remaining obligations. Rewrite using `[dist_eq_norm, pi_norm_le_iff_of_nonneg hs0]`. Introduce `r`. Rewrite using `[pi_norm_le_iff_of_nonneg hs0]`.

Introduce `c`. Rewrite using `[← sq_le_sq₀ (norm_nonneg _) hs0]`. Use `le_trans ?_ hx` and prove the remaining obligations. Unfold `hs`. Use `le_trans ?_ (Finset.single_le_sum (fun i _ => by positivity) (Finset.mem_univ r))` and prove the remaining obligations.

Conclude with `Finset.single_le_sum (f := fun c => ‖(Matrix.of x - 1) r c‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ c)`.
-/
theorem exists_subset {j : ℕ} {P : (Fin j → Fin j → ℂ) → Prop}
    (h : ∀ᶠ x in nhds (Matrix.of.symm (1 : Matrix (Fin j) (Fin j) ℂ)), P x) :
    ∃ δ > 0, ∀ s, 0 ≤ s → s < δ → ∀ x ∈ unitBallAt j s, P x := by
  obtain ⟨δ, hδ, H⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun s hs0 hsδ x hx => H (lt_of_le_of_lt ?_ hsδ)⟩
  rw [dist_eq_norm, pi_norm_le_iff_of_nonneg hs0]
  intro r
  rw [pi_norm_le_iff_of_nonneg hs0]
  intro c
  rw [← sq_le_sq₀ (norm_nonneg _) hs0]
  refine le_trans ?_ hx
  unfold hs
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => by positivity) (Finset.mem_univ r))
  exact Finset.single_le_sum (f := fun c => ‖(Matrix.of x - 1) r c‖ ^ 2) (fun i _ => by positivity)
    (Finset.mem_univ c)

/- English proof (translation)
Use `show ∀ᶠ x : Matrix (Fin j) (Fin j) ℂ in nhds 1, (a ≤ (‖x.det‖ ^ 2)⁻¹ ^ j ∧ (‖x.det‖ ^ 2)⁻¹ ^ j ≤ a⁻¹) ∧ a ^ 2 * hs (x - 1) ≤ hs (x⁻¹ - 1) ∧ a ^ 2 * hs (x⁻¹ - 1) ≤ hs (x - 1)`. Establish `hdet : Continuous fun x : Matrix (Fin j) (Fin j) ℂ => x.det` using `continuous_id.matrix_det`. Establish `h1 : ContinuousAt (fun x : Matrix (Fin j) (Fin j) ℂ => (‖x.det‖ ^ 2)⁻¹ ^ j) 1` using `(((hdet.norm.pow 2).continuousAt).inv₀ (by simp)).pow j`. Establish `h2 : ContinuousAt (fun x : Matrix (Fin j) (Fin j) ℂ => hs (x⁻¹ - 1)) 1`. Use `continuous_hs.continuousAt.comp (ContinuousAt.sub (continuousAt_matrix_inv _ ?_) continuousAt_const)` and prove the remaining obligations.

Rewrite using `[Ring.inverse_eq_inv']`. Conclude with `continuousAt_inv₀ (by simp)`. Establish `h3` using `h1.eventually (lt_mem_nhds (a := a) (by simpa using ha1))`. Establish `h4` using `h1.eventually (gt_mem_nhds (a := a⁻¹) (by simpa using (one_lt_inv₀ ha).2 ha1))`. Establish `h5` using `h2.eventually (gt_mem_nhds (a := (1 - a) ^ 2) (by`.

Establish `: 0 < 1 - a` using `by linarith`. Simplify `pow_pos this 2))` using `[hs]`. Establish `h6` using `(hdet.continuousAt (x := 1)).eventually_ne (y := 0) (by simp)`. Use `filter_upwards [h3, h4, h5, h6] with x x3 x4 x5 x6`. Conclude with `⟨⟨x3.le, x4.le⟩, hs_inv_compare x x6 ha ha1 x5.le⟩`.
-/
theorem eventually_good (j : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∀ᶠ x : Fin j → Fin j → ℂ in nhds (Matrix.of.symm (1 : Matrix (Fin j) (Fin j) ℂ)),
      (a ≤ (‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j ∧ (‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j ≤ a⁻¹) ∧
      a ^ 2 * hs (Matrix.of x - 1) ≤ hs ((Matrix.of x)⁻¹ - 1) ∧
      a ^ 2 * hs ((Matrix.of x)⁻¹ - 1) ≤ hs (Matrix.of x - 1) := by
  show ∀ᶠ x : Matrix (Fin j) (Fin j) ℂ in nhds 1,
      (a ≤ (‖x.det‖ ^ 2)⁻¹ ^ j ∧ (‖x.det‖ ^ 2)⁻¹ ^ j ≤ a⁻¹) ∧
      a ^ 2 * hs (x - 1) ≤ hs (x⁻¹ - 1) ∧ a ^ 2 * hs (x⁻¹ - 1) ≤ hs (x - 1)
  have hdet : Continuous fun x : Matrix (Fin j) (Fin j) ℂ => x.det := continuous_id.matrix_det
  have h1 : ContinuousAt (fun x : Matrix (Fin j) (Fin j) ℂ => (‖x.det‖ ^ 2)⁻¹ ^ j) 1 :=
    (((hdet.norm.pow 2).continuousAt).inv₀ (by simp)).pow j
  have h2 : ContinuousAt (fun x : Matrix (Fin j) (Fin j) ℂ => hs (x⁻¹ - 1)) 1 := by
    refine continuous_hs.continuousAt.comp (ContinuousAt.sub (continuousAt_matrix_inv _ ?_) continuousAt_const)
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (by simp)
  have h3 := h1.eventually (lt_mem_nhds (a := a) (by simpa using ha1))
  have h4 := h1.eventually (gt_mem_nhds (a := a⁻¹) (by simpa using (one_lt_inv₀ ha).2 ha1))
  have h5 := h2.eventually (gt_mem_nhds (a := (1 - a) ^ 2) (by
    have : 0 < 1 - a := by linarith
    simpa [hs] using pow_pos this 2))
  have h6 := (hdet.continuousAt (x := 1)).eventually_ne (y := 0) (by simp)
  filter_upwards [h3, h4, h5, h6] with x x3 x4 x5 x6
  exact ⟨⟨x3.le, x4.le⟩, hs_inv_compare x x6 ha ha1 x5.le⟩

/- English proof (translation)
Take `⟨δ, hδ, H⟩` from `exists_subset (eventually_good j ha ha1)`. Use `filter_upwards [Ioo_mem_nhdsGT (mul_pos ha hδ)] with r ⟨hr, hrδ⟩`. Establish `h2 : (0 : ℝ) < √2` using `by positivity`. Establish `h21 : (1 : ℝ) ≤ √2` using `Real.one_le_sqrt.2 (by norm_num)`. Establish `h22 : (√2 : ℝ) ^ 2 = 2` using `Real.sq_sqrt (by norm_num)`.

Establish `hr1 : r < δ` using `by nlinarith`. Establish `hr2 : a * r / √2 < δ`. Use `lt_of_le_of_lt (div_le_self (by positivity) h21) (by nlinarith)` and prove the remaining obligations. Establish `hr3 : a⁻¹ * r / √2 < δ`. Use `lt_of_le_of_lt (div_le_self (by positivity) h21) ?_` and prove the remaining obligations.

Rewrite using `[inv_mul_lt_iff₀ ha]` and apply the resulting hypothesis. Establish `hrd : ENNReal.ofReal (r ^ (2 * j ^ 2)) ≠ 0`. Simplify using `using pow_pos hr _`. Establish `hvol : ∀ b : ℝ, 0 < b → ENNReal.ofReal (2 ^ (j ^ 2)) * (ENNReal.ofReal b * volume (unitBallAt j (b * r / √2))) = ENNReal.ofReal (b ^ (2 * j ^ 2 + 1)) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) * ENNReal.ofReal (r ^ (2 * j ^ 2))`. Introduce `b hb`.

Rewrite using `[volume_unitBallAt j (by positivity), mul_right_comm, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]`. Use `congr 2`. Rewrite using `[div_pow, pow_mul √2, h22, mul_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Prove the components needed by the constructor for the conclusion. Rewrite using `[ENNReal.le_div_iff_mul_le (Or.inl hrd) (Or.inl ENNReal.ofReal_ne_top), ← hvol a ha, Measure.smul_apply, smul_eq_mul] gcongr`. Use `le_trans ?_ (measure_mono (s := unitBallAt j (a * r / √2)) fun x hx => ?_)` and prove the remaining obligations. Rewrite using `[haarLoc, withDensity_apply _ (measurableSet_unitBallAt j _), ← setLIntegral_const]`. Conclude with `setLIntegral_mono' (measurableSet_unitBallAt j _) fun x hx => ENNReal.ofReal_le_ofReal (H _ (by positivity) hr2 x hx).1.1`.

Establish `h3` using `(H _ (by positivity) hr2 x hx).2.2`. Establish `h4 : hs (Matrix.of x - 1) ≤ a ^ 2 * r ^ 2 / 2`. Establish `: hs (Matrix.of x - 1) ≤ (a * r / √2) ^ 2` using `hx`. Rewrite `this` using `[div_pow, h22, mul_pow]`. Then use the resulting hypothesis. Establish `h5 : hs ((Matrix.of x)⁻¹ - 1) ≤ r ^ 2 / 2` using `le_of_mul_le_mul_left (a := a ^ 2) (by linarith) (by positivity)`.

Establish `h6 : a ^ 2 * r ^ 2 ≤ r ^ 2` using `mul_le_of_le_one_left (by positivity) (by nlinarith)`. Use `Real.sqrt_le_iff.2 ⟨hr.le, by linarith⟩` and prove the remaining obligations. Rewrite using `[ENNReal.div_le_iff hrd ENNReal.ofReal_ne_top, ← hvol a⁻¹ (by positivity), Measure.smul_apply, smul_eq_mul] gcongr`. Use `le_trans (measure_mono (t := unitBallAt j (a⁻¹ * r / √2)) fun x hx => ?_) ?_` and prove the remaining obligations. Establish `h1` using `(Real.sqrt_le_iff.1 hx).2`.

Establish `h0` using `hs_nonneg ((Matrix.of x)⁻¹ - 1)`. Establish `h0'` using `hs_nonneg (Matrix.of x - 1)`. Establish `h3` using `(H r hr.le hr1 x (show hs (Matrix.of x - 1) ≤ r ^ 2 by linarith)).2.1`. Establish `h6 : a ^ 2 * hs (Matrix.of x - 1) ≤ hs (Matrix.of x - 1)` using `mul_le_of_le_one_left h0' (by nlinarith)`. Use `show hs (Matrix.of x - 1) ≤ (a⁻¹ * r / √2) ^ 2`.

Rewrite using `[div_pow, h22, mul_pow, inv_pow, le_div_iff₀ (by norm_num), le_inv_mul_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[haarLoc, withDensity_apply _ (measurableSet_unitBallAt j _), ← setLIntegral_const]`. Conclude with `setLIntegral_mono' (measurableSet_unitBallAt j _) fun x hx => ENNReal.ofReal_le_ofReal (H _ (by positivity) hr3 x hx).1.2`.
-/
theorem sandwich (j : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ENNReal.ofReal (a ^ (2 * j ^ 2 + 1)) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) ≤
        (ENNReal.ofReal (2 ^ (j ^ 2)) • haarLoc j)
          {x | Real.sqrt (hs (Matrix.of x - 1) + hs ((Matrix.of x)⁻¹ - 1)) ≤ r} /
          ENNReal.ofReal (r ^ (2 * j ^ 2)) ∧
      (ENNReal.ofReal (2 ^ (j ^ 2)) • haarLoc j)
          {x | Real.sqrt (hs (Matrix.of x - 1) + hs ((Matrix.of x)⁻¹ - 1)) ≤ r} /
          ENNReal.ofReal (r ^ (2 * j ^ 2)) ≤
      ENNReal.ofReal (a⁻¹ ^ (2 * j ^ 2 + 1)) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) := by
  obtain ⟨δ, hδ, H⟩ := exists_subset (eventually_good j ha ha1)
  filter_upwards [Ioo_mem_nhdsGT (mul_pos ha hδ)] with r ⟨hr, hrδ⟩
  have h2 : (0 : ℝ) < √2 := by positivity
  have h21 : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.2 (by norm_num)
  have h22 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr1 : r < δ := by nlinarith
  have hr2 : a * r / √2 < δ := by
    refine lt_of_le_of_lt (div_le_self (by positivity) h21) (by nlinarith)
  have hr3 : a⁻¹ * r / √2 < δ := by
    refine lt_of_le_of_lt (div_le_self (by positivity) h21) ?_
    rwa [inv_mul_lt_iff₀ ha]
  have hrd : ENNReal.ofReal (r ^ (2 * j ^ 2)) ≠ 0 := by
    simpa using pow_pos hr _
  have hvol : ∀ b : ℝ, 0 < b → ENNReal.ofReal (2 ^ (j ^ 2)) * (ENNReal.ofReal b *
      volume (unitBallAt j (b * r / √2))) = ENNReal.ofReal (b ^ (2 * j ^ 2 + 1)) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) * ENNReal.ofReal (r ^ (2 * j ^ 2)) := by
    intro b hb
    rw [volume_unitBallAt j (by positivity), mul_right_comm, ← mul_assoc, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [div_pow, pow_mul √2, h22, mul_pow]
    field_simp
    ring
  constructor
  · rw [ENNReal.le_div_iff_mul_le (Or.inl hrd) (Or.inl ENNReal.ofReal_ne_top), ← hvol a ha,
      Measure.smul_apply, smul_eq_mul]
    gcongr
    refine le_trans ?_ (measure_mono (s := unitBallAt j (a * r / √2)) fun x hx => ?_)
    · rw [haarLoc, withDensity_apply _ (measurableSet_unitBallAt j _), ← setLIntegral_const]
      exact setLIntegral_mono' (measurableSet_unitBallAt j _) fun x hx =>
        ENNReal.ofReal_le_ofReal (H _ (by positivity) hr2 x hx).1.1
    · have h3 := (H _ (by positivity) hr2 x hx).2.2
      have h4 : hs (Matrix.of x - 1) ≤ a ^ 2 * r ^ 2 / 2 := by
        have : hs (Matrix.of x - 1) ≤ (a * r / √2) ^ 2 := hx
        rwa [div_pow, h22, mul_pow] at this
      have h5 : hs ((Matrix.of x)⁻¹ - 1) ≤ r ^ 2 / 2 :=
        le_of_mul_le_mul_left (a := a ^ 2) (by linarith) (by positivity)
      have h6 : a ^ 2 * r ^ 2 ≤ r ^ 2 := mul_le_of_le_one_left (by positivity) (by nlinarith)
      refine Real.sqrt_le_iff.2 ⟨hr.le, by linarith⟩
  · rw [ENNReal.div_le_iff hrd ENNReal.ofReal_ne_top, ← hvol a⁻¹ (by positivity),
      Measure.smul_apply, smul_eq_mul]
    gcongr
    refine le_trans (measure_mono (t := unitBallAt j (a⁻¹ * r / √2)) fun x hx => ?_) ?_
    · have h1 := (Real.sqrt_le_iff.1 hx).2
      have h0 := hs_nonneg ((Matrix.of x)⁻¹ - 1)
      have h0' := hs_nonneg (Matrix.of x - 1)
      have h3 := (H r hr.le hr1 x (show hs (Matrix.of x - 1) ≤ r ^ 2 by linarith)).2.1
      have h6 : a ^ 2 * hs (Matrix.of x - 1) ≤ hs (Matrix.of x - 1) :=
        mul_le_of_le_one_left h0' (by nlinarith)
      show hs (Matrix.of x - 1) ≤ (a⁻¹ * r / √2) ^ 2
      rw [div_pow, h22, mul_pow, inv_pow, le_div_iff₀ (by norm_num), le_inv_mul_iff₀ (by positivity)]
      linarith
    · rw [haarLoc, withDensity_apply _ (measurableSet_unitBallAt j _), ← setLIntegral_const]
      exact setLIntegral_mono' (measurableSet_unitBallAt j _) fun x hx =>
        ENNReal.ofReal_le_ofReal (H _ (by positivity) hr3 x hx).1.2

end GlobalTheory.LeviIso.RadLoc

namespace GlobalTheory.LeviIso

open RadLoc

/- English proof (translation)
Unfold `IsRadial`. Use `set ω := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) with hω`. Establish `hωt : ω ≠ ⊤` using `measure_ball_lt_top.ne`. Establish `hc : Filter.Tendsto (fun a : ℝ => ENNReal.ofReal (a ^ (2 * j ^ 2 + 1)) * ω) (nhds 1) (nhds ω)`. Establish `: Filter.Tendsto (fun a : ℝ => ENNReal.ofReal (a ^ (2 * j ^ 2 + 1))) (nhds 1) (nhds 1)`.

Simplify using `using ENNReal.tendsto_ofReal ((continuous_pow (2 * j ^ 2 + 1)).tendsto (1 : ℝ))`. Simplify using `using ENNReal.Tendsto.mul_const this (Or.inl one_ne_zero)`. Establish `hi : Filter.Tendsto (fun a : ℝ => a⁻¹) (nhds 1) (nhds 1)`. Simplify using `using Filter.Tendsto.inv₀ (Filter.tendsto_id (x := nhds (1 : ℝ))) one_ne_zero`. Use `tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩` and prove the remaining obligations.

Take `⟨a, h1, h2, h3⟩` from `(((hc.eventually (lt_mem_nhds hb)).filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT (zero_lt_one' ℝ))).exists filter_upwards [sandwich j h2 h3] with r hr`. Conclude with `lt_of_lt_of_le h1 hr.1`. Take `⟨a, h1, h2, h3⟩` from `((((hc.comp hi).eventually (gt_mem_nhds hb)).filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT (zero_lt_one' ℝ))).exists filter_upwards [sandwich j h2 h3] with r hr`. Conclude with `lt_of_le_of_lt hr.2 h1`.
-/
theorem isRadial_haarLoc (j : ℕ) : IsRadial (ENNReal.ofReal (2 ^ (j ^ 2)) • haarLoc j)
    (fun x => Formalism.REAL.hs (Matrix.of x - 1) + Formalism.REAL.hs ((Matrix.of x)⁻¹ - 1)) (2 * j ^ 2) := by
  unfold IsRadial
  set ω := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) with hω
  have hωt : ω ≠ ⊤ := measure_ball_lt_top.ne
  have hc : Filter.Tendsto (fun a : ℝ => ENNReal.ofReal (a ^ (2 * j ^ 2 + 1)) * ω) (nhds 1) (nhds ω) := by
    have : Filter.Tendsto (fun a : ℝ => ENNReal.ofReal (a ^ (2 * j ^ 2 + 1))) (nhds 1) (nhds 1) := by
      simpa using ENNReal.tendsto_ofReal ((continuous_pow (2 * j ^ 2 + 1)).tendsto (1 : ℝ))
    simpa using ENNReal.Tendsto.mul_const this (Or.inl one_ne_zero)
  have hi : Filter.Tendsto (fun a : ℝ => a⁻¹) (nhds 1) (nhds 1) := by
    simpa using Filter.Tendsto.inv₀ (Filter.tendsto_id (x := nhds (1 : ℝ))) one_ne_zero
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨a, h1, h2, h3⟩ := (((hc.eventually (lt_mem_nhds hb)).filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsLT (zero_lt_one' ℝ))).exists
    filter_upwards [sandwich j h2 h3] with r hr
    exact lt_of_lt_of_le h1 hr.1
  · obtain ⟨a, h1, h2, h3⟩ := ((((hc.comp hi).eventually (gt_mem_nhds hb)).filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsLT (zero_lt_one' ℝ))).exists
    filter_upwards [sandwich j h2 h3] with r hr
    exact lt_of_le_of_lt hr.2 h1

end GlobalTheory.LeviIso
