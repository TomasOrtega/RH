import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix MatrixOrder

namespace GlobalTheory.HSAmp

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis.

Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sumSq_ball_eq_smul (ι : Type) [Fintype ι] (R : ℝ) (hR : 0 ≤ R) :
    {x : ι → ℝ | ∑ i, x i ^ 2 ≤ R ^ 2} = (fun x => R • x) '' {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hx
    rcases hR.eq_or_lt with h0 | h0
    · subst h0
      refine ⟨0, by simp, ?_⟩
      have h1 : ∑ i, x i ^ 2 = 0 :=
        le_antisymm (by simpa using hx) (Finset.sum_nonneg fun i _ => sq_nonneg _)
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)] at h1
      funext i
      have := h1 i (Finset.mem_univ _)
      simp [pow_eq_zero_iff] at this
      simp [this]
    · refine ⟨R⁻¹ • x, ?_, by simp [smul_smul, h0.ne']⟩
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, inv_pow]
      rw [inv_mul_le_iff₀ (by positivity)]
      simpa using hx
  · rintro ⟨y, hy, rfl⟩
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
    nlinarith [sq_nonneg R]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem volume_sumSq_ball_pos_lt_top (ι : Type) [Fintype ι] :
    0 < volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1} ∧ volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1} < ⊤ := by
  constructor
  · have ho : IsOpen {x : ι → ℝ | ∑ i, x i ^ 2 < 1} :=
      isOpen_lt (by fun_prop) continuous_const
    refine lt_of_lt_of_le (ho.measure_pos volume ⟨0, by simp⟩) (measure_mono ?_)
    intro x hx
    exact le_of_lt (a := ∑ i, x i ^ 2) hx
  · refine lt_of_le_of_lt (measure_mono ?_) (isCompact_closedBall (0 : ι → ℝ) 1).measure_lt_top
    intro x hx
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : x i ^ 2 ≤ ∑ i, x i ^ 2 :=
      Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : x i ^ 2 ≤ 1 := h1.trans hx
    rw [Real.norm_eq_abs]
    exact (sq_le_one_iff_abs_le_one _).1 h2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify using the standard rewrite rules. Use symmetry to reverse the relation. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem volume_ellipsoid : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ), A.PosDef → ∀ R : ℝ, 0 ≤ R → volume {x : ι → ℝ | ∑ i, ∑ j, A i j * x i * x j ≤ R ^ 2} = ENNReal.ofReal (R ^ Fintype.card ι / Real.sqrt A.det) * volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1} ∧ 0 < volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1} ∧ volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1} < ⊤ := by
  intro ι _ _ A hA R hR
  refine ⟨?_, volume_sumSq_ball_pos_lt_top ι⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix ι ι ℝ, A = Bᵀ * B := by
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hA.posSemidef.nonneg
    exact ⟨B, by simpa [Matrix.star_eq_conjTranspose] using hB⟩
  have hdet : A.det = B.det ^ 2 := by
    rw [hB, Matrix.det_mul, Matrix.det_transpose, sq]
  have hpos : 0 < A.det := hA.det_pos
  have hB0 : B.det ≠ 0 := by
    intro h; rw [hdet, h] at hpos; simp at hpos
  have hset : {x : ι → ℝ | ∑ i, ∑ j, A i j * x i * x j ≤ R ^ 2}
      = (Matrix.toLin' B) ⁻¹' {x : ι → ℝ | ∑ i, x i ^ 2 ≤ R ^ 2} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Matrix.toLin'_apply]
    have : ∑ i, ∑ j, A i j * x i * x j = ∑ i, (B *ᵥ x) i ^ 2 := by
      simp only [hB, Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, sq,
        Finset.sum_mul, Finset.mul_sum]
      symm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this]
  have hl : LinearMap.det (Matrix.toLin' B) ≠ 0 := by simpa using hB0
  rw [hset, Measure.addHaar_preimage_linearMap _ hl, sumSq_ball_eq_smul ι R hR, Set.image_smul,
    Measure.addHaar_smul_of_nonneg _ hR, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 2
  rw [hdet, Real.sqrt_sq_eq_abs, LinearMap.det_toLin', abs_inv, Module.finrank_fintype_fun_eq_card]
  ring

end GlobalTheory.HSAmp
