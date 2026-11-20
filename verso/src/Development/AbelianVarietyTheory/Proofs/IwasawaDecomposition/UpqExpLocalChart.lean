import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMatExp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EntrySumMulLe
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.ExpBallSandwich

section Matrices
variable {n : Type} [Fintype n] [DecidableEq n]

noncomputable def sumAbs (M : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, ‖M i j‖

omit [DecidableEq n] in
/- English proof (translation)
Unfold `sumAbs`. Check the signs of the components of the expression.
-/
theorem sumAbs_nonneg (M : Matrix n n ℂ) : 0 ≤ sumAbs M := by
  unfold sumAbs; positivity

omit [DecidableEq n] in
/- English proof (translation)
Unfold `sumAbs`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_le_sum fun j _ => norm_add_le _ _`.
-/
theorem sumAbs_add_le (A B : Matrix n n ℂ) : sumAbs (A + B) ≤ sumAbs A + sumAbs B := by
  unfold sumAbs
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => norm_add_le _ _

omit [DecidableEq n] in
/- English proof (translation)
Simplify using `[sumAbs]`.
-/
theorem sumAbs_neg (A : Matrix n n ℂ) : sumAbs (-A) = sumAbs A := by
  simp [sumAbs]

omit [DecidableEq n] in
/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le`. Consider the case `exact _root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le`. Consider the case `(apply _root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le ..)`.
-/
theorem sumAbs_mul_le (A B : Matrix n n ℂ) : sumAbs (A * B) ≤ sumAbs A * sumAbs B := by
  first
  | exact @_root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le
  | exact _root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le
  | (apply _root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le ..)

section Op
open scoped Matrix.Norms.Operator

/- English proof (translation)
Rewrite using `[Matrix.linfty_opNorm_def]`. Use `Finset.le_sup (f := fun i : n => ∑ j, ‖M i j‖₊) (Finset.mem_univ i)` as an intermediate fact. Establish `h2 : ((∑ j, ‖M i j‖₊ : NNReal) : ℝ) ≤ _` using `NNReal.coe_le_coe.2 this`. Simplify using `using h2`.
-/
theorem row_le_op (M : Matrix n n ℂ) (i : n) : ∑ j, ‖M i j‖ ≤ ‖M‖ := by
  rw [Matrix.linfty_opNorm_def]
  have := Finset.le_sup (f := fun i : n => ∑ j, ‖M i j‖₊) (Finset.mem_univ i)
  have h2 : ((∑ j, ‖M i j‖₊ : NNReal) : ℝ) ≤ _ := NNReal.coe_le_coe.2 this
  simpa using h2

/- English proof (translation)
Rewrite using `[Matrix.linfty_opNorm_def]`. Establish `: (Finset.univ.sup fun i : n => ∑ j, ‖M i j‖₊) ≤ ∑ i, ∑ j, ‖M i j‖₊` using `Finset.sup_le fun i _ => Finset.single_le_sum (f := fun l => ∑ j, ‖M l j‖₊) (fun l _ => by positivity) (Finset.mem_univ i)`. Establish `h2` using `NNReal.coe_le_coe.2 this`. Simplify `h2` using `[sumAbs]`.
-/
theorem op_le_sumAbs (M : Matrix n n ℂ) : ‖M‖ ≤ sumAbs M := by
  rw [Matrix.linfty_opNorm_def]
  have : (Finset.univ.sup fun i : n => ∑ j, ‖M i j‖₊) ≤ ∑ i, ∑ j, ‖M i j‖₊ :=
    Finset.sup_le fun i _ => Finset.single_le_sum (f := fun l => ∑ j, ‖M l j‖₊)
          (fun l _ => by positivity) (Finset.mem_univ i)
  have h2 := NNReal.coe_le_coe.2 this
  simpa [sumAbs] using h2

/- English proof (translation)
Unfold `sumAbs`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sumAbs_le_op (M : Matrix n n ℂ) : sumAbs M ≤ (Fintype.card n : ℝ) * ‖M‖ := by
  unfold sumAbs
  calc _ ≤ ∑ _i : n, ‖M‖ := Finset.sum_le_sum fun i _ => row_le_op M i
    _ = _ := by simp

/- English proof (translation)
Establish `h` using `(hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := Matrix n n ℂ)).isLittleO`. Establish `hc : 0 < η / ((Fintype.card n : ℝ) + 1)` using `by positivity`. Establish `h2` using `h.def hc`. Rewrite `h2` using `[Metric.eventually_nhds_iff]`. Take `⟨ρ, hρ, h3⟩` from `h2`.

Use `⟨ρ, hρ, fun A B hA hB => ?_⟩` and prove the remaining obligations. Establish `h4` using `@h3 (A, B) (by`. Rewrite using `[Prod.dist_eq, dist_zero_right, dist_zero_right]`. Conclude with `max_lt ((op_le_sumAbs A).trans_lt hA) ((op_le_sumAbs B).trans_lt hB))`. Simplify using `only [ContinuousLinearMap.one_apply] at h4`.

Establish `h5` using `op_le_sumAbs (A - B)`. Establish `h6` using `sumAbs_nonneg (A - B)`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_left (h4.trans ?_) (by positivity)` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_left h5 hc.le`.

Use `_ ≤ ((Fintype.card n : ℝ) + 1) * (η / ((Fintype.card n : ℝ) + 1) * sumAbs (A - B)) := by gcongr; linarith`. Use `_ = _ := by field_simp`.
-/
theorem exp_strict (η : ℝ) (hη : 0 < η) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ A B : Matrix n n ℂ,
    sumAbs A < ρ → sumAbs B < ρ →
    sumAbs (NormedSpace.exp A - NormedSpace.exp B - (A - B)) ≤ η * sumAbs (A - B) := by
  have h := (hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := Matrix n n ℂ)).isLittleO
  have hc : 0 < η / ((Fintype.card n : ℝ) + 1) := by positivity
  have h2 := h.def hc
  rw [Metric.eventually_nhds_iff] at h2
  obtain ⟨ρ, hρ, h3⟩ := h2
  refine ⟨ρ, hρ, fun A B hA hB => ?_⟩
  have h4 := @h3 (A, B) (by
    rw [Prod.dist_eq, dist_zero_right, dist_zero_right]
    exact max_lt ((op_le_sumAbs A).trans_lt hA) ((op_le_sumAbs B).trans_lt hB))
  simp only [ContinuousLinearMap.one_apply] at h4
  have h5 := op_le_sumAbs (A - B)
  have h6 := sumAbs_nonneg (A - B)
  calc _ ≤ _ := sumAbs_le_op _
    _ ≤ (Fintype.card n : ℝ) * (η / ((Fintype.card n : ℝ) + 1) * sumAbs (A - B)) := by
        refine mul_le_mul_of_nonneg_left (h4.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left h5 hc.le
    _ ≤ ((Fintype.card n : ℝ) + 1) * (η / ((Fintype.card n : ℝ) + 1) * sumAbs (A - B)) := by
        gcongr; linarith
    _ = _ := by field_simp

end Op

/- English proof (translation)
Take `⟨ρ, hρ, h⟩` from `exp_strict (n := n) η hη`. Use `⟨min ρ (η / 2), by positivity, fun X Y Z hX hY hZ he => ?_⟩` and prove the remaining obligations. Rewrite `hX`, `hY`, `hZ` using `[lt_min_iff]`. Establish `h0 : sumAbs (0 : Matrix n n ℂ) < ρ` using `by simpa [sumAbs] using hρ`. Establish `key : ∀ W : Matrix n n ℂ, sumAbs W < ρ → sumAbs (NormedSpace.exp W - 1 - W) ≤ η * sumAbs W ∧ sumAbs (NormedSpace.exp W - 1) ≤ 2 * sumAbs W`.

Introduce `W hW`. Establish `h1` using `h W 0 hW h0`. Rewrite `h1` using `[NormedSpace.exp_zero, sub_zero]`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `h2` using `sumAbs_add_le (NormedSpace.exp W - 1 - W) W`.

Rewrite `h2` using `[sub_add_cancel]`. Use `sumAbs_nonneg W` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `e : Y - X - Z = -(NormedSpace.exp Y - NormedSpace.exp X - (Y - X)) + ((NormedSpace.exp Z - 1 - Z) + (NormedSpace.exp X - 1) * (NormedSpace.exp Z - 1))`. Rewrite using `[he]`.

Use `noncomm_ring`. Establish `a1` using `h Y X hY.1 hX.1`. Establish `a2` using `(key Z hZ.1).1`. Establish `a3` using `(key Z hZ.1).2`. Establish `a4 : sumAbs (NormedSpace.exp X - 1) ≤ η` using `by linarith [(key X hX.1).2, hX.2]`.

Establish `a5 : sumAbs ((NormedSpace.exp X - 1) * (NormedSpace.exp Z - 1)) ≤ η * (2 * sumAbs Z)` using `(sumAbs_mul_le _ _).trans (mul_le_mul a4 a3 (sumAbs_nonneg _) hη.le)`. Rewrite using `[e]`. Use `(sumAbs_add_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[sumAbs_neg]`. Establish `a6` using `sumAbs_add_le (NormedSpace.exp Z - 1 - Z) ((NormedSpace.exp X - 1) * (NormedSpace.exp Z - 1))`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem defect_le (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ X Y Z : Matrix n n ℂ,
    sumAbs X < ρ → sumAbs Y < ρ → sumAbs Z < ρ →
    NormedSpace.exp Y = NormedSpace.exp X * NormedSpace.exp Z →
    sumAbs (Y - X - Z) ≤ η * sumAbs (Y - X) + 3 * η * sumAbs Z := by
  obtain ⟨ρ, hρ, h⟩ := exp_strict (n := n) η hη
  refine ⟨min ρ (η / 2), by positivity, fun X Y Z hX hY hZ he => ?_⟩
  rw [lt_min_iff] at hX hY hZ
  have h0 : sumAbs (0 : Matrix n n ℂ) < ρ := by simpa [sumAbs] using hρ
  have key : ∀ W : Matrix n n ℂ, sumAbs W < ρ →
      sumAbs (NormedSpace.exp W - 1 - W) ≤ η * sumAbs W ∧
      sumAbs (NormedSpace.exp W - 1) ≤ 2 * sumAbs W := by
    intro W hW
    have h1 := h W 0 hW h0
    rw [NormedSpace.exp_zero, sub_zero] at h1
    refine ⟨h1, ?_⟩
    have h2 := sumAbs_add_le (NormedSpace.exp W - 1 - W) W
    rw [sub_add_cancel] at h2
    have := sumAbs_nonneg W
    nlinarith
  have e : Y - X - Z = -(NormedSpace.exp Y - NormedSpace.exp X - (Y - X)) +
      ((NormedSpace.exp Z - 1 - Z) + (NormedSpace.exp X - 1) * (NormedSpace.exp Z - 1)) := by
    rw [he]; noncomm_ring
  have a1 := h Y X hY.1 hX.1
  have a2 := (key Z hZ.1).1
  have a3 := (key Z hZ.1).2
  have a4 : sumAbs (NormedSpace.exp X - 1) ≤ η := by linarith [(key X hX.1).2, hX.2]
  have a5 : sumAbs ((NormedSpace.exp X - 1) * (NormedSpace.exp Z - 1)) ≤ η * (2 * sumAbs Z) :=
    (sumAbs_mul_le _ _).trans (mul_le_mul a4 a3 (sumAbs_nonneg _) hη.le)
  rw [e]
  refine (sumAbs_add_le _ _).trans ?_
  rw [sumAbs_neg]
  have a6 := sumAbs_add_le (NormedSpace.exp Z - 1 - Z)
    ((NormedSpace.exp X - 1) * (NormedSpace.exp Z - 1))
  linarith

end Matrices

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_mul {P Q : ℕ} (g h : UpqT P Q) : UpqT.mat (g * h) = UpqT.mat g * UpqT.mat h := rfl

end GlobalTheory.ExpBallSandwich
