import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfD

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix MeasureTheory

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

def dI (τ : ι) (b : Fin r) : UpI ι r := ⟨(τ, b, b), lt_irrefl b⟩

def jacU (y : UpI ι r → ℂ) : ℂ := ∏ i : Ix ι r, if i.2.2 < i.2.1 then y (dI i.1 i.2.2) else 1

def jacβ (β : ι → Matrix (Fin r) (Fin r) ℂ) : ℂ := ∏ i : Ix ι r, if i.2.2 < i.2.1 then β i.1 i.2.2 i.2.2 else 1

def Cy (ι : Type*) [Fintype ι] (r : ℕ) : Set (UpI ι r → ℂ) :=
  {y | ∀ i : UpI ι r, (i.1.2.1 = i.1.2.2 → 1 ≤ ‖y i‖ ∧ ‖y i‖ ≤ 2) ∧ (i.1.2.1 ≠ i.1.2.2 → ‖y i‖ ≤ 1)}

def K0 (ι : Type*) [Fintype ι] [DecidableEq ι] (r : ℕ) : ENNReal :=
  ∫⁻ y in Cy ι r, ENNReal.ofReal (Complex.normSq (jacU y))

/- English proof (translation)
Use `show (β τ * Umat y τ) b b = β τ b b * y (dI τ b)`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single b]`. Simplify using `[Umat, dI]`. Introduce `c _ hcb`. Break down `lt_or_gt_of_ne hcb with h | h` into its components or cases.

Rewrite using `[hβ τ h, zero_mul]`. Simplify using `[Umat, h]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ b) h`.
-/
lemma Lβ_diag (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id) (y : UpI ι r → ℂ)
    (τ : ι) (b : Fin r) : Lβ β y (dI τ b) = β τ b b * y (dI τ b) := by
  show (β τ * Umat y τ) b b = β τ b b * y (dI τ b)
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · simp [Umat, dI]
  · intro c _ hcb
    rcases lt_or_gt_of_ne hcb with h | h
    · rw [hβ τ h, zero_mul]
    · simp [Umat, h]
  · intro h
    exact absurd (Finset.mem_univ b) h

/- English proof (translation)
Unfold `jacU jacβ`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `Lβ_diag β hβ y i.1 i.2.2`.

Simplify using the standard rewrite rules.
-/
lemma jacU_Lβ (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id) (y : UpI ι r → ℂ) :
    jacU (Lβ β y) = jacβ β * jacU y := by
  unfold jacU jacβ
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · exact Lβ_diag β hβ y i.1 i.2.2
  · simp

/- English proof (translation)
Establish `h : Cy ι r = ⋂ i : UpI ι r, {y : UpI ι r → ℂ | (i.1.2.1 = i.1.2.2 → 1 ≤ ‖y i‖ ∧ ‖y i‖ ≤ 2) ∧ (i.1.2.1 ≠ i.1.2.2 → ‖y i‖ ≤ 1)}`. Use extensionality with `y`. Simplify using `[Cy]`. Use `IsClosed.measurableSet ?_` and prove the remaining obligations. Rewrite using `[h]`.

Use `isClosed_iInter fun i => ?_` and prove the remaining obligations. Establish `hc : Continuous fun y : UpI ι r → ℂ => ‖y i‖` using `(continuous_apply i).norm`. Distinguish the cases in `hi : i.1.2.1 = i.1.2.2`. Simplify using `only [hi, ne_eq, not_true_eq_false, false_implies, and_true, true_implies]`. Conclude with `(isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)`.

Simplify using `only [hi, ne_eq, not_false_eq_true, true_implies, false_implies, true_and]`. Conclude with `isClosed_le hc continuous_const`.
-/
lemma measurableSet_Cy : MeasurableSet (Cy ι r) := by
  have h : Cy ι r = ⋂ i : UpI ι r, {y : UpI ι r → ℂ | (i.1.2.1 = i.1.2.2 → 1 ≤ ‖y i‖ ∧ ‖y i‖ ≤ 2) ∧
      (i.1.2.1 ≠ i.1.2.2 → ‖y i‖ ≤ 1)} := by
    ext y
    simp [Cy]
  refine IsClosed.measurableSet ?_
  rw [h]
  refine isClosed_iInter fun i => ?_
  have hc : Continuous fun y : UpI ι r → ℂ => ‖y i‖ := (continuous_apply i).norm
  by_cases hi : i.1.2.1 = i.1.2.2
  · simp only [hi, ne_eq, not_true_eq_false, false_implies, and_true, true_implies]
    exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)
  · simp only [hi, ne_eq, not_false_eq_true, true_implies, false_implies, true_and]
    exact isClosed_le hc continuous_const

/- English proof (translation)
Distinguish the cases in `hi : i.1.2.1 = i.1.2.2`. Conclude with `((hy i).1 hi).2`. Conclude with `((hy i).2 hi).trans (by norm_num)`.
-/
lemma norm_le_of_Cy {y : UpI ι r → ℂ} (hy : y ∈ Cy ι r) (i : UpI ι r) : ‖y i‖ ≤ 2 := by
  by_cases hi : i.1.2.1 = i.1.2.2
  · exact ((hy i).1 hi).2
  · exact ((hy i).2 hi).trans (by norm_num)

/- English proof (translation)
Unfold `jacU`. Rewrite using `[map_prod]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ => ?_` and prove the remaining obligations. Use `split_ifs`.

Establish `h1` using `((hy (dI i.1 i.2.2)).1 rfl).1`. Rewrite using `[Complex.normSq_eq_norm_sq]`. Use the polynomial consequences of the given equalities and inequalities. Simplify using the standard rewrite rules.
-/
lemma one_le_normSq_jacU {y : UpI ι r → ℂ} (hy : y ∈ Cy ι r) : 1 ≤ Complex.normSq (jacU y) := by
  unfold jacU
  rw [map_prod]
  calc (1 : ℝ) = ∏ _i : Ix ι r, (1 : ℝ) := Finset.prod_const_one.symm
    _ ≤ _ := by
      refine Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ => ?_
      split_ifs
      · have h1 := ((hy (dI i.1 i.2.2)).1 rfl).1
        rw [Complex.normSq_eq_norm_sq]
        nlinarith
      · simp

/- English proof (translation)
Unfold `jacU`. Rewrite using `[map_prod]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_le_prod (fun _ _ => Complex.normSq_nonneg _) fun i _ => ?_` and prove the remaining obligations. Use `split_ifs`.

Establish `h1` using `norm_le_of_Cy hy (dI i.1 i.2.2)`. Rewrite using `[Complex.normSq_eq_norm_sq]`. Use polynomial arithmetic with `[norm_nonneg (y (dI i.1 i.2.2))]`. Simplify using the standard rewrite rules. Use `_ = 4 ^ Fintype.card (Ix ι r) := by rw [Finset.prod_const, Finset.card_univ]`.
-/
lemma normSq_jacU_le {y : UpI ι r → ℂ} (hy : y ∈ Cy ι r) :
    Complex.normSq (jacU y) ≤ 4 ^ Fintype.card (Ix ι r) := by
  unfold jacU
  rw [map_prod]
  calc _ ≤ ∏ _i : Ix ι r, (4 : ℝ) := by
        refine Finset.prod_le_prod (fun _ _ => Complex.normSq_nonneg _) fun i _ => ?_
        split_ifs
        · have h1 := norm_le_of_Cy hy (dI i.1 i.2.2)
          rw [Complex.normSq_eq_norm_sq]
          nlinarith [norm_nonneg (y (dI i.1 i.2.2))]
        · simp
    _ = 4 ^ Fintype.card (Ix ι r) := by rw [Finset.prod_const, Finset.card_univ]

/- English proof (translation)
Introduce `y hy` and use `mem_closedBall_zero_iff.2 ((pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => norm_le_of_Cy hy i)`.
-/
lemma Cy_subset_ball : Cy ι r ⊆ Metric.closedBall 0 2 := fun y hy =>
  mem_closedBall_zero_iff.2 ((pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => norm_le_of_Cy hy i)

/- English proof (translation)
Unfold `jacU`. Use `continuous_finset_prod _ fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : i.2.2 < i.2.1`. Simplify using `only [h, ↓reduceIte]`. Conclude with `continuous_apply _`.

Simplify using `only [h, ↓reduceIte]`. Conclude with `continuous_const`.
-/
lemma continuous_jacU : Continuous (jacU (ι := ι) (r := r)) := by
  unfold jacU
  refine continuous_finset_prod _ fun i _ => ?_
  by_cases h : i.2.2 < i.2.1
  · simp only [h, ↓reduceIte]
    exact continuous_apply _
  · simp only [h, ↓reduceIte]
    exact continuous_const

/- English proof (translation)
The claim follows from `(ENNReal.continuous_ofReal.comp (Complex.continuous_normSq.comp continuous_jacU)).measurable`.
-/
lemma measurable_normSq_jacU : Measurable fun y : UpI ι r → ℂ => ENNReal.ofReal (Complex.normSq (jacU y)) :=
  (ENNReal.continuous_ofReal.comp (Complex.continuous_normSq.comp continuous_jacU)).measurable

/- English proof (translation)
Unfold `K0`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma measureConstant_lt_top : K0 ι r < ⊤ := by
  unfold K0
  calc ∫⁻ y in Cy ι r, ENNReal.ofReal (Complex.normSq (jacU y))
      ≤ ∫⁻ _y in Cy ι r, ENNReal.ofReal (4 ^ Fintype.card (Ix ι r)) :=
        setLIntegral_mono measurable_const fun y hy => ENNReal.ofReal_le_ofReal (normSq_jacU_le hy)
    _ = ENNReal.ofReal (4 ^ Fintype.card (Ix ι r)) * volume (Cy ι r) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((measure_mono Cy_subset_ball).trans_lt measure_closedBall_lt_top)

/- English proof (translation)
Introduce `y hy i`. Establish `h` using `(dist_le_pi_dist y (fun i : UpI ι r => if i.1.2.1 = i.1.2.2 then (3 / 2 : ℂ) else 0) i).trans_lt (Metric.mem_ball.1 hy)`. Establish `h32 : ‖(3 / 2 : ℂ)‖ = 3 / 2`. Rewrite using `[show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs]`. Evaluate the numerical expressions.

Prove the components needed by the constructor for the conclusion. Introduce `hi`. Simplify using `only [hi, ↓reduceIte, Complex.dist_eq] at h`. Establish `h1` using `norm_sub_norm_le (y i) (3 / 2)`. Establish `h2` using `norm_sub_norm_le (3 / 2 : ℂ) (y i)`.

Rewrite `h2` using `[norm_sub_rev]`. Apply the tactic sequence `constructor <;> linarith`. Introduce `hi`. Simplify using `only [hi, ↓reduceIte, dist_zero_right] at h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma ball_subset_Cy : Metric.ball (fun i : UpI ι r => if i.1.2.1 = i.1.2.2 then (3 / 2 : ℂ) else 0) (1 / 2) ⊆ Cy ι r := by
  intro y hy i
  have h := (dist_le_pi_dist y (fun i : UpI ι r => if i.1.2.1 = i.1.2.2 then (3 / 2 : ℂ) else 0) i).trans_lt
    (Metric.mem_ball.1 hy)
  have h32 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by
    rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  constructor
  · intro hi
    simp only [hi, ↓reduceIte, Complex.dist_eq] at h
    have h1 := norm_sub_norm_le (y i) (3 / 2)
    have h2 := norm_sub_norm_le (3 / 2 : ℂ) (y i)
    rw [norm_sub_rev] at h2
    constructor <;> linarith
  · intro hi
    simp only [hi, ↓reduceIte, dist_zero_right] at h
    linarith

/- English proof (translation)
Unfold `K0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← ENNReal.ofReal_one]`. Conclude with `ENNReal.ofReal_le_ofReal (one_le_normSq_jacU hy)`.
-/
lemma finrank_maxUnramifiedSubfield_padicFinExt_pos : 0 < K0 ι r := by
  unfold K0
  calc (0 : ENNReal)
      < volume (Metric.ball (fun i : UpI ι r => if i.1.2.1 = i.1.2.2 then (3 / 2 : ℂ) else 0) (1 / 2)) :=
        Metric.measure_ball_pos _ _ (by norm_num)
    _ ≤ volume (Cy ι r) := measure_mono ball_subset_Cy
    _ = ∫⁻ _y in Cy ι r, 1 := (setLIntegral_one _).symm
    _ ≤ ∫⁻ y in Cy ι r, ENNReal.ofReal (Complex.normSq (jacU y)) :=
        setLIntegral_mono measurable_normSq_jacU fun y hy => by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (one_le_normSq_jacU hy)

/- English proof (translation)
Rewrite using `[det_Lβ β hβ]`. Conclude with `Finset.prod_ne_zero_iff.2 fun i _ => hd _ _`.
-/
lemma det_Lβ_ne (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id)
    (hd : ∀ τ b, β τ b b ≠ 0) : LinearMap.det (Lβ β) ≠ 0 := by
  rw [det_Lβ β hβ]
  exact Finset.prod_ne_zero_iff.2 fun i _ => hd _ _

/- English proof (translation)
Unfold `jacβ`. Use `Finset.prod_ne_zero_iff.2 fun i _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `hd _ _`. Conclude with `one_ne_zero`.
-/
lemma jacβ_ne (β : ι → Matrix (Fin r) (Fin r) ℂ) (hd : ∀ τ b, β τ b b ≠ 0) : jacβ β ≠ 0 := by
  unfold jacβ
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  split_ifs
  · exact hd _ _
  · exact one_ne_zero

/- English proof (translation)
Use `set LR : (UpI ι r → ℂ) →ₗ[ℝ] (UpI ι r → ℂ) := (Lβ β).restrictScalars ℝ with hLR_def`. Establish `hdet : LinearMap.det LR = Complex.normSq (LinearMap.det (Lβ β))`. Rewrite using `[hLR_def, LinearMap.det_restrictScalars, Algebra.norm_complex_apply]`. Establish `hdn` using `det_Lβ_ne β hβ hd`. Establish `hdR : LinearMap.det LR ≠ 0`.

Rewrite using `[hdet]`. Conclude with `(Complex.normSq_pos.2 hdn).ne'`. Establish `hjbp : 0 < Complex.normSq (jacβ β)` using `Complex.normSq_pos.2 (jacβ_ne β hd)`. Use `set G : (UpI ι r → ℂ) → ENNReal := fun z => ENNReal.ofReal (Complex.normSq (jacU z) / Complex.normSq (jacβ β)) * (Cy ι r).indicator 1 z with hG_def`. Establish `hG : Measurable G` using `(ENNReal.measurable_ofReal.comp ((Complex.continuous_normSq.comp continuous_jacU).measurable.div_const _)).mul (measurable_one.indicator measurableSet_Cy)`.

Establish `hLRm : Measurable LR` using `LR.continuous_of_finiteDimensional.measurable`. Establish `hpt : ∀ y, ENNReal.ofReal (Complex.normSq (jacU y)) * (Cy ι r).indicator 1 (Lβ β y) = G (LR y)`. Introduce `y`. Establish `e : LR y = Lβ β y` using `rfl`. Rewrite using `[hG_def]`.

Simplify using `only`. Rewrite using `[e, jacU_Lβ β hβ, map_mul, mul_div_cancel_left₀ _ hjbp.ne']`. Establish `hint : ∫⁻ z, G z = ENNReal.ofReal ((Complex.normSq (jacβ β))⁻¹) * K0 ι r`. Establish `e : ∀ z, G z = ENNReal.ofReal ((Complex.normSq (jacβ β))⁻¹) * (Cy ι r).indicator (fun z => ENNReal.ofReal (Complex.normSq (jacU z))) z`. Introduce `z`.

Rewrite using `[hG_def]`. Simplify using `only`. Distinguish the cases in `hz : z ∈ Cy ι r`. Rewrite using `[Set.indicator_of_mem hz, Set.indicator_of_mem hz, Pi.one_apply, mul_one, div_eq_mul_inv, ENNReal.ofReal_mul (Complex.normSq_nonneg _), mul_comm]`. Rewrite using `[Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero, mul_zero]`.

Rewrite using `[lintegral_congr e, lintegral_const_mul _ (measurable_normSq_jacU.indicator measurableSet_Cy), lintegral_indicator measurableSet_Cy]`. Both sides reduce to the same expression. Rewrite using `[lintegral_congr hpt, ← lintegral_map hG hLRm, Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdR, lintegral_smul_measure, hint, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), hdet, abs_of_nonneg (inv_nonneg.2 (Complex.normSq_nonneg _)), ← mul_inv]`.
-/
theorem lintegral_upper (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id)
    (hd : ∀ τ b, β τ b b ≠ 0) :
    ∫⁻ y, ENNReal.ofReal (Complex.normSq (jacU y)) * (Cy ι r).indicator 1 (Lβ β y) =
      ENNReal.ofReal ((Complex.normSq (LinearMap.det (Lβ β)) * Complex.normSq (jacβ β))⁻¹) * K0 ι r := by
  set LR : (UpI ι r → ℂ) →ₗ[ℝ] (UpI ι r → ℂ) := (Lβ β).restrictScalars ℝ with hLR_def
  have hdet : LinearMap.det LR = Complex.normSq (LinearMap.det (Lβ β)) := by
    rw [hLR_def, LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  have hdn := det_Lβ_ne β hβ hd
  have hdR : LinearMap.det LR ≠ 0 := by
    rw [hdet]
    exact (Complex.normSq_pos.2 hdn).ne'
  have hjbp : 0 < Complex.normSq (jacβ β) := Complex.normSq_pos.2 (jacβ_ne β hd)
  set G : (UpI ι r → ℂ) → ENNReal := fun z =>
    ENNReal.ofReal (Complex.normSq (jacU z) / Complex.normSq (jacβ β)) * (Cy ι r).indicator 1 z with hG_def
  have hG : Measurable G :=
    (ENNReal.measurable_ofReal.comp
      ((Complex.continuous_normSq.comp continuous_jacU).measurable.div_const _)).mul
      (measurable_one.indicator measurableSet_Cy)
  have hLRm : Measurable LR := LR.continuous_of_finiteDimensional.measurable
  have hpt : ∀ y, ENNReal.ofReal (Complex.normSq (jacU y)) * (Cy ι r).indicator 1 (Lβ β y) = G (LR y) := by
    intro y
    have e : LR y = Lβ β y := rfl
    rw [hG_def]
    dsimp only
    rw [e, jacU_Lβ β hβ, map_mul, mul_div_cancel_left₀ _ hjbp.ne']
  have hint : ∫⁻ z, G z = ENNReal.ofReal ((Complex.normSq (jacβ β))⁻¹) * K0 ι r := by
    have e : ∀ z, G z = ENNReal.ofReal ((Complex.normSq (jacβ β))⁻¹) *
        (Cy ι r).indicator (fun z => ENNReal.ofReal (Complex.normSq (jacU z))) z := by
      intro z
      rw [hG_def]
      dsimp only
      by_cases hz : z ∈ Cy ι r
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Pi.one_apply, mul_one, div_eq_mul_inv,
          ENNReal.ofReal_mul (Complex.normSq_nonneg _), mul_comm]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero, mul_zero]
    rw [lintegral_congr e, lintegral_const_mul _ (measurable_normSq_jacU.indicator measurableSet_Cy),
      lintegral_indicator measurableSet_Cy]
    rfl
  rw [lintegral_congr hpt, ← lintegral_map hG hLRm, Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdR,
    lintegral_smul_measure, hint, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), hdet,
    abs_of_nonneg (inv_nonneg.2 (Complex.normSq_nonneg _)), ← mul_inv]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
