import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KFiniteSmoothVectors.UnitaryModelOfMultiplicityGardingDensity

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ContDiff

noncomputable section

namespace PI.KFinSmoothW

open PI.UpqRep

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Dense

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
The claim follows from `h.2`.
-/
lemma umat_mem_UJset (h : UJ ε) : umat h ∈ UJset ε := h.2

/- English proof (translation)
Conclude with `(UJ ε).one_mem`.
-/
lemma one_mem_UJset : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
  exact (UJ ε).one_mem

/- English proof (translation)
The claim follows from `(hτ.2.2 u).comp_continuous (Units.continuous_val.comp continuous_subtype_val) (fun h => h.2)`.
-/
lemma cont_orbit {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ) (u : H) :
    Continuous (fun h : UJ ε => τ (umat h) u) := (hτ.2.2 u).comp_continuous (Units.continuous_val.comp continuous_subtype_val) (fun h => h.2)

/- English proof (translation)
Establish `hc` using `cont_orbit hτ u`. Establish `hI1 : Integrable (fun h : UJ ε => Φr (umat h) • τ (umat h) u) (muG ε)`. Use `Integrable.mono' (hint.mul_const ‖u‖) ?_ ?_` and prove the remaining obligations. Conclude with `((hΦc.comp (continuous_coeMatrix ε)).smul hc).aestronglyMeasurable`. Use `filter_upwards with h`.

Rewrite using `[norm_smul, hτ.2.1 _ (umat_mem_UJset h), Real.norm_eq_abs, abs_of_nonneg (hΦ0 _)]`. Establish `hI2 : Integrable (fun h : UJ ε => Φr (umat h) • u) (muG ε)` using `hint.smul_const u`. Establish `hgv : gv ε τ (fun x => (Φr x : ℂ)) u = ∫ h, Φr (umat h) • τ (umat h) u ∂(muG ε)`. Unfold `gv`. Use `congr 1`.

Establish `hu : ∫ h, Φr (umat h) • u ∂(muG ε) = u`. Rewrite using `[integral_smul_const, h1, one_smul]`. Establish `hdiff : ∫ h, Φr (umat h) • (τ (umat h) u - u) ∂(muG ε) = ∫ h, Φr (umat h) • τ (umat h) u ∂(muG ε) - u`. Repeatedly rewrite using `[smul_sub]`. Rewrite using `[integral_sub hI1 hI2, hu]`.

Rewrite using `[hgv, ← hdiff]`. Combine the equalities or inequalities in the displayed calculation. Use `norm_integral_le_of_norm_le (hint.mul_const δ) ?_` and prove the remaining obligations. Use `filter_upwards with h`. Rewrite using `[norm_smul, Real.norm_eq_abs, abs_of_nonneg (hΦ0 _)]`.

Distinguish the cases in `hz : Φr (umat h) = 0`. Simplify using `[hz]`. Conclude with `mul_le_mul_of_nonneg_left (hsupp h hz) (hΦ0 _)`. Use `_ = δ := by rw [integral_mul_const, h1, one_mul]`.
-/
lemma gv_sub_norm_le [CompleteSpace H] {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hτ : IsURepOn (UJset ε) τ)
    (Φr : Matrix (Fin n) (Fin n) ℂ → ℝ) (hΦc : Continuous Φr) (hΦ0 : ∀ x, 0 ≤ Φr x)
    (hint : Integrable (fun h : UJ ε => Φr (umat h)) (muG ε))
    (h1 : ∫ h, Φr (umat h) ∂(muG ε) = 1) (u : H) (δ : ℝ)
    (hsupp : ∀ h : UJ ε, Φr (umat h) ≠ 0 → ‖τ (umat h) u - u‖ ≤ δ) :
    ‖gv ε τ (fun x => (Φr x : ℂ)) u - u‖ ≤ δ := by
  have hc := cont_orbit hτ u
  have hI1 : Integrable (fun h : UJ ε => Φr (umat h) • τ (umat h) u) (muG ε) := by
    refine Integrable.mono' (hint.mul_const ‖u‖) ?_ ?_
    · exact ((hΦc.comp (continuous_coeMatrix ε)).smul hc).aestronglyMeasurable
    · filter_upwards with h
      rw [norm_smul, hτ.2.1 _ (umat_mem_UJset h), Real.norm_eq_abs, abs_of_nonneg (hΦ0 _)]
  have hI2 : Integrable (fun h : UJ ε => Φr (umat h) • u) (muG ε) := hint.smul_const u
  have hgv : gv ε τ (fun x => (Φr x : ℂ)) u = ∫ h, Φr (umat h) • τ (umat h) u ∂(muG ε) := by
    unfold gv
    congr 1
  have hu : ∫ h, Φr (umat h) • u ∂(muG ε) = u := by
    rw [integral_smul_const, h1, one_smul]
  have hdiff : ∫ h, Φr (umat h) • (τ (umat h) u - u) ∂(muG ε) =
      ∫ h, Φr (umat h) • τ (umat h) u ∂(muG ε) - u := by
    simp_rw [smul_sub]
    rw [integral_sub hI1 hI2, hu]
  rw [hgv, ← hdiff]
  calc ‖∫ h, Φr (umat h) • (τ (umat h) u - u) ∂(muG ε)‖
      ≤ ∫ h, Φr (umat h) * δ ∂(muG ε) := by
        refine norm_integral_le_of_norm_le (hint.mul_const δ) ?_
        filter_upwards with h
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hΦ0 _)]
        by_cases hz : Φr (umat h) = 0
        · simp [hz]
        · exact mul_le_mul_of_nonneg_left (hsupp h hz) (hΦ0 _)
    _ = δ := by rw [integral_mul_const, h1, one_mul]

def qd (x : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖x i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2

/- English proof (translation)
Unfold `qd`. Use `ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_` and prove the remaining obligations. Conclude with `(contDiff_norm_sq ℝ).comp ((contDiff_apply_apply ℝ ℂ i j).sub contDiff_const)`.
-/
lemma qd_contDiff : ContDiff ℝ ∞ (qd (n := n)) := by
  unfold qd
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  exact (contDiff_norm_sq ℝ).comp ((contDiff_apply_apply ℝ ℂ i j).sub contDiff_const)

/- English proof (translation)
Simplify using `[qd]`.
-/
lemma qd_one : qd (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  simp [qd]

/- English proof (translation)
Simplify using `only [qd, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, Matrix.sub_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]`.
-/
lemma qd_eq_trace (x : Matrix (Fin n) (Fin n) ℂ) :
    qd x = (Matrix.trace ((x - 1)ᴴ * (x - 1))).re := by
  simp only [qd, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Matrix.sub_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/- English proof (translation)
Rewrite using `[qd_eq_trace, qd_eq_trace]`. Establish `e : a * m * aᴴ - 1 = a * (m - 1) * aᴴ`. Rewrite using `[mul_sub, sub_mul, mul_one, h1]`. Establish `e2 : (a * (m - 1) * aᴴ)ᴴ * (a * (m - 1) * aᴴ) = a * ((m - 1)ᴴ * (m - 1)) * aᴴ`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc aᴴ a, h2, Matrix.one_mul]`. Rewrite using `[e, e2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]`.
-/
lemma qd_conj (a m : Matrix (Fin n) (Fin n) ℂ) (h1 : a * aᴴ = 1) (h2 : aᴴ * a = 1) :
    qd (a * m * aᴴ) = qd m := by
  rw [qd_eq_trace, qd_eq_trace]
  have e : a * m * aᴴ - 1 = a * (m - 1) * aᴴ := by
    rw [mul_sub, sub_mul, mul_one, h1]
  have e2 : (a * (m - 1) * aᴴ)ᴴ * (a * (m - 1) * aᴴ) = a * ((m - 1)ᴴ * (m - 1)) * aᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc aᴴ a, h2, Matrix.one_mul]
  rw [e, e2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[dist_eq_norm, Matrix.norm_lt_iff hr]`. Introduce `i j`. Establish `hle : ‖(x - 1) i j‖ ^ 2 ≤ qd x`. Unfold `qd`. Rewrite using `[Matrix.sub_apply]`.

Combine the equalities or inequalities in the displayed calculation. Use polynomial arithmetic with `[norm_nonneg ((x - 1) i j)]`.
-/
lemma dist_lt_of_qd_lt {x : Matrix (Fin n) (Fin n) ℂ} {r : ℝ} (hr : 0 < r) (h : qd x < r ^ 2) :
    dist x 1 < r := by
  rw [dist_eq_norm, Matrix.norm_lt_iff hr]
  intro i j
  have hle : ‖(x - 1) i j‖ ^ 2 ≤ qd x := by
    unfold qd
    rw [Matrix.sub_apply]
    calc ‖x i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2
        ≤ ∑ j', ‖x i j' - (1 : Matrix (Fin n) (Fin n) ℂ) i j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' => ‖x i j' - (1 : Matrix (Fin n) (Fin n) ℂ) i j'‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', ‖x i' j' - (1 : Matrix (Fin n) (Fin n) ℂ) i' j'‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun i' => ∑ j', ‖x i' j' - (1 : Matrix (Fin n) (Fin n) ℂ) i' j'‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  nlinarith [norm_nonneg ((x - 1) i j)]

end Dense

/- English proof (translation)
Introduce `n ε H _ _ _ τ hτ W hW`. Set `R : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] H)` to `fun g => (τ g).comp W.subtypeL`. Establish `hR : ContinuousWithinAt R (UJset ε) 1` using `continuousWithinAt_clm_apply.2 fun y => hτ.2.2 (y : H) 1 one_mem_UJset`. Take `⟨r, hr, hr'⟩` from `Metric.continuousWithinAt_iff.mp hR (1 / 2) (by norm_num)`. Establish `hτ1 : τ 1 = 1` using `hτ.1.1`.

Establish `hclose : ∀ g ∈ UJset ε, dist g 1 < r → ∀ w ∈ W, ‖τ g w - w‖ ≤ ‖w‖ / 2`. Introduce `g hg hd w hw`. Establish `h1` using `hr' hg hd`. Rewrite `h1` using `[dist_eq_norm]`. Establish `h2` using `(R g - R 1).le_opNorm ⟨w, hw⟩`.

Establish `h3 : (R g - R 1) ⟨w, hw⟩ = τ g w - w`. Simplify using `[R, hτ1]`. Rewrite `h2` using `[h3]`. Establish `h4 : ‖(⟨w, hw⟩ : W)‖ = ‖w‖` using `rfl`. Rewrite `h2` using `[h4]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hr2 : 0 < r ^ 2` using `by positivity`. Set `ψ : ContDiffBump (0 : ℝ)` to `⟨r ^ 2 / 2, r ^ 2, half_pos hr2, half_lt_self hr2⟩`. Set `Φ0 : Matrix (Fin n) (Fin n) ℂ → ℝ` to `fun x => ψ (qd x)`. Establish `hΦ0c : Continuous Φ0` using `ψ.continuous.comp qd_contDiff.continuous`.

Establish `hsupp0 : ∀ x, Φ0 x ≠ 0 → dist x 1 < r`. Introduce `x hx`. Establish `hb : qd x ∈ Function.support ψ` using `hx`. Rewrite `hb` using `[ψ.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero]`. Conclude with `dist_lt_of_qd_lt hr (lt_of_le_of_lt (le_abs_self _) hb)`.

Establish `hcs : HasCompactSupport Φ0`. Use `HasCompactSupport.intro (isCompact_closedBall (1 : Matrix (Fin n) (Fin n) ℂ) r) ?_` and prove the remaining obligations. Introduce `x hx`. Assume the negation of the conclusion as `hne`. Conclude with `hx (Metric.mem_closedBall.2 (hsupp0 x hne).le)`.

Establish `hcomp : Continuous (fun h : UJ ε => Φ0 (umat h))` using `hΦ0c.comp (continuous_coeMatrix ε)`. Establish `hint : Integrable (fun h : UJ ε => Φ0 (umat h)) (muG ε)` using `hcomp.integrable_of_hasCompactSupport (hcs.comp_isClosedEmbedding (isClosedEmbeddingMatrix n ε).1)`. Establish `hpos : 0 < ∫ h, Φ0 (umat h) ∂(muG ε)`. Rewrite using `[integral_pos_iff_support_of_nonneg (fun h => ψ.nonneg) hint]`. Apply `IsOpen.measure_pos` to reduce the goal to its premises.

Conclude with `isOpen_ne_fun hcomp continuous_const`. Use `⟨1, ?_⟩ show ψ (qd (umat (1 : UJ ε))) ≠ 0` and prove the remaining obligations. Establish `h1 : umat (1 : UJ ε) = 1` using `rfl`. Rewrite using `[h1, qd_one, ψ.one_of_mem_closedBall (Metric.mem_closedBall_self ψ.rIn_pos.le)]`. Conclude with `one_ne_zero`.

Use `set c := ∫ h, Φ0 (umat h) ∂(muG ε) with hc`. Use `⟨fun x => ((Φ0 x / c : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Complex.ofRealCLM.contDiff.comp ((ψ.contDiff.comp qd_contDiff).div_const c)`. Conclude with `hcs.comp_left (g := fun t : ℝ => ((t / c : ℝ) : ℂ)) (by simp)`. Introduce `a ha m`.

Establish `hu1 : a * aᴴ = 1`. Use `Unitary.mul_star_self_of_mem ha.1` as an intermediate fact. Rewrite `this` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis. Establish `hu2 : aᴴ * a = 1`. Use `Unitary.star_mul_self_of_mem ha.1` as an intermediate fact.

Rewrite `this` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis. Simplify using `only [Φ0, qd_conj a m hu1 hu2]`. Introduce `w hw`. Use `gv_sub_norm_le hτ (fun x => Φ0 x / c) (hΦ0c.div_const c) (fun x => div_nonneg ψ.nonneg hpos.le) (hint.div_const c) (by rw [integral_div, ← hc, div_self hpos.ne']) w (‖w‖ / 2) ?_` and prove the remaining obligations. Introduce `h hz`.

Establish `hne : Φ0 (umat h) ≠ 0`. Introduce `h0`. Apply `hz` to reduce the goal to its premises. Use `show Φ0 (umat h) / c = 0`. Rewrite using `[h0, zero_div]`.

Conclude with `hclose _ (umat_mem_UJset h) (hsupp0 _ hne) w hw`.
-/
theorem dense_weak_vectors : StepDenseW := by
  intro n ε H _ _ _ τ hτ W hW

  let R : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] H) := fun g => (τ g).comp W.subtypeL
  have hR : ContinuousWithinAt R (UJset ε) 1 :=
    continuousWithinAt_clm_apply.2 fun y => hτ.2.2 (y : H) 1 one_mem_UJset
  obtain ⟨r, hr, hr'⟩ := Metric.continuousWithinAt_iff.mp hR (1 / 2) (by norm_num)
  have hτ1 : τ 1 = 1 := hτ.1.1
  have hclose : ∀ g ∈ UJset ε, dist g 1 < r → ∀ w ∈ W, ‖τ g w - w‖ ≤ ‖w‖ / 2 := by
    intro g hg hd w hw
    have h1 := hr' hg hd
    rw [dist_eq_norm] at h1
    have h2 := (R g - R 1).le_opNorm ⟨w, hw⟩
    have h3 : (R g - R 1) ⟨w, hw⟩ = τ g w - w := by
      simp [R, hτ1]
    rw [h3] at h2
    have h4 : ‖(⟨w, hw⟩ : W)‖ = ‖w‖ := rfl
    rw [h4] at h2
    calc ‖τ g w - w‖ ≤ ‖R g - R 1‖ * ‖w‖ := h2
      _ ≤ (1 / 2) * ‖w‖ := mul_le_mul_of_nonneg_right h1.le (norm_nonneg _)
      _ = ‖w‖ / 2 := by ring

  have hr2 : 0 < r ^ 2 := by positivity
  let ψ : ContDiffBump (0 : ℝ) := ⟨r ^ 2 / 2, r ^ 2, half_pos hr2, half_lt_self hr2⟩
  let Φ0 : Matrix (Fin n) (Fin n) ℂ → ℝ := fun x => ψ (qd x)
  have hΦ0c : Continuous Φ0 := ψ.continuous.comp qd_contDiff.continuous
  have hsupp0 : ∀ x, Φ0 x ≠ 0 → dist x 1 < r := by
    intro x hx
    have hb : qd x ∈ Function.support ψ := hx
    rw [ψ.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hb
    exact dist_lt_of_qd_lt hr (lt_of_le_of_lt (le_abs_self _) hb)
  have hcs : HasCompactSupport Φ0 := by
    refine HasCompactSupport.intro (isCompact_closedBall (1 : Matrix (Fin n) (Fin n) ℂ) r) ?_
    intro x hx
    by_contra hne
    exact hx (Metric.mem_closedBall.2 (hsupp0 x hne).le)
  have hcomp : Continuous (fun h : UJ ε => Φ0 (umat h)) := hΦ0c.comp (continuous_coeMatrix ε)
  have hint : Integrable (fun h : UJ ε => Φ0 (umat h)) (muG ε) :=
    hcomp.integrable_of_hasCompactSupport (hcs.comp_isClosedEmbedding (isClosedEmbeddingMatrix n ε).1)
  have hpos : 0 < ∫ h, Φ0 (umat h) ∂(muG ε) := by
    rw [integral_pos_iff_support_of_nonneg (fun h => ψ.nonneg) hint]
    apply IsOpen.measure_pos
    · exact isOpen_ne_fun hcomp continuous_const
    · refine ⟨1, ?_⟩
      show ψ (qd (umat (1 : UJ ε))) ≠ 0
      have h1 : umat (1 : UJ ε) = 1 := rfl
      rw [h1, qd_one, ψ.one_of_mem_closedBall (Metric.mem_closedBall_self ψ.rIn_pos.le)]
      exact one_ne_zero
  set c := ∫ h, Φ0 (umat h) ∂(muG ε) with hc
  refine ⟨fun x => ((Φ0 x / c : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ((ψ.contDiff.comp qd_contDiff).div_const c)
  · exact hcs.comp_left (g := fun t : ℝ => ((t / c : ℝ) : ℂ)) (by simp)
  · intro a ha m
    have hu1 : a * aᴴ = 1 := by
      have := Unitary.mul_star_self_of_mem ha.1
      rwa [Matrix.star_eq_conjTranspose] at this
    have hu2 : aᴴ * a = 1 := by
      have := Unitary.star_mul_self_of_mem ha.1
      rwa [Matrix.star_eq_conjTranspose] at this
    simp only [Φ0, qd_conj a m hu1 hu2]
  · intro w hw
    refine gv_sub_norm_le hτ (fun x => Φ0 x / c) (hΦ0c.div_const c)
      (fun x => div_nonneg ψ.nonneg hpos.le) (hint.div_const c)
      (by rw [integral_div, ← hc, div_self hpos.ne']) w (‖w‖ / 2) ?_
    intro h hz
    have hne : Φ0 (umat h) ≠ 0 := by
      intro h0
      apply hz
      show Φ0 (umat h) / c = 0
      rw [h0, zero_div]
    exact hclose _ (umat_mem_UJset h) (hsupp0 _ hne) w hw

end PI.KFinSmoothW
