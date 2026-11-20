import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.ThetaDerivNe

noncomputable section

open Complex UpperHalfPlane ModularGroup
open scoped MatrixGroups Modular

namespace PI.SSE

/- English proof (translation)
Unfold `PI.lat2`. Rewrite using `[← zsmul_eq_mul, ← zsmul_eq_mul]`. Conclude with `AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by simp)) m) (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by simp)) n)`.
-/
lemma integer_combination_mem_lattice (x y : ℂ) (m n : ℤ) : (m : ℂ) * x + (n : ℂ) * y ∈ PI.lat2 x y := by
  unfold PI.lat2
  rw [← zsmul_eq_mul, ← zsmul_eq_mul]
  exact AddSubgroup.add_mem _
    (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by simp)) m)
    (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by simp)) n)

/- English proof (translation)
Unfold `PI.lat2 at *`. Rewrite using `[AddSubgroup.closure_le]`. Apply the tactic sequence `rintro z (rfl | rfl) <;> assumption`.
-/
lemma lattice_span_le (x y u v : ℂ) (hx : x ∈ PI.lat2 u v) (hy : y ∈ PI.lat2 u v) :
    PI.lat2 x y ≤ PI.lat2 u v := by
  unfold PI.lat2 at *
  rw [AddSubgroup.closure_le]
  rintro z (rfl | rfl) <;> assumption

/- English proof (translation)
Unfold `PI.lat2`. Rewrite using `[Set.pair_comm]`.
-/
lemma lattice_span_comm (x y : ℂ) : PI.lat2 x y = PI.lat2 y x := by
  unfold PI.lat2
  rw [Set.pair_comm]

/- English proof (translation)
Establish `hw1 : w₁ ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hw`. Establish `hN : 0 < Complex.normSq w₁` using `Complex.normSq_pos.mpr hw1`. Establish `him : 0 < (w₂ / w₁).im`.

Establish `e : (w₂ / w₁).im = ((starRingEnd ℂ) w₁ * w₂).im / Complex.normSq w₁`. Simplify using `only [Complex.div_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `div_pos hw hN`.

Set `τ : UpperHalfPlane` to `⟨w₂ / w₁, him⟩`. Establish `hτ : (τ : ℂ) = w₂ / w₁` using `rfl`. Take `⟨g, hg⟩` from `ModularGroup.exists_smul_mem_fd τ`. Establish `h3` using `ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg`. Establish `hcoe` using `UpperHalfPlane.coe_specialLinearGroup_apply g τ`.

Establish `hdet0` using `Matrix.SpecialLinearGroup.det_coe g`. Rewrite `hdet0` using `[Matrix.det_fin_two]`. Take `⟨a, ha⟩ : ∃ a : ℤ, a = (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0` from `⟨_, rfl⟩`. Take `⟨b, hb⟩ : ∃ b : ℤ, b = (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1` from `⟨_, rfl⟩`. Take `⟨c, hc⟩ : ∃ c : ℤ, c = (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0` from `⟨_, rfl⟩`.

Take `⟨d, hd⟩ : ∃ d : ℤ, d = (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1` from `⟨_, rfl⟩`. Rewrite `hdet0`, `hcoe` using `[← ha, ← hb, ← hc, ← hd]`. Simplify using `only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast] at hcoe`. Establish `hdetC : (a : ℂ) * d - b * c = 1` using `by exact_mod_cast hdet0`. Establish `hden : (c : ℂ) * (w₂ / w₁) + d ≠ 0`.

Introduce `h0`. Establish `e1 : ((c : ℂ) * (w₂ / w₁) + d).im = c * (w₂ / w₁).im` using `by simp`. Establish `e2 : ((c : ℂ) * (w₂ / w₁) + d).re = c * (w₂ / w₁).re + d` using `by simp`. Rewrite `e1`, `e2` using `[h0]`. Simplify using `only [Complex.zero_im, Complex.zero_re] at e1 e2`.

Establish `hc0 : (c : ℝ) = 0`. Break down `mul_eq_zero.mp e1.symm with h | h` into its components or cases. Conclude with `h`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hd0 : (d : ℝ) = 0`.

Rewrite `e2` using `[hc0, zero_mul, zero_add]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc0' : c = 0` using `by exact_mod_cast hc0`. Establish `hd0' : d = 0` using `by exact_mod_cast hd0`. Rewrite `hdet0` using `[hc0', hd0']`.

Simplify using `at hdet0`. Establish `hv1 : (c : ℂ) * w₂ + d * w₁ = w₁ * ((c : ℂ) * (w₂ / w₁) + d)`. Clear the denominators using the available nonvanishing facts. Establish `hv2 : (a : ℂ) * w₂ + b * w₁ = w₁ * ((a : ℂ) * (w₂ / w₁) + b)`. Clear the denominators using the available nonvanishing facts.

Establish `hv1ne : (c : ℂ) * w₂ + d * w₁ ≠ 0`. Rewrite using `[hv1]`. Conclude with `mul_ne_zero hw1 hden`. Establish `hq : ((a : ℂ) * w₂ + b * w₁) / ((c : ℂ) * w₂ + d * w₁) = ((g • τ : UpperHalfPlane) : ℂ)`. Rewrite using `[hcoe, hτ, hv1, hv2, mul_div_mul_left _ _ hw1]`.

Use `⟨(c : ℂ) * w₂ + d * w₁, (a : ℂ) * w₂ + b * w₁, hv1ne, le_antisymm ?_ ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `lattice_span_le` to reduce the goal to its premises. Use `integer_combination_mem_lattice w₁ w₂ d c` as an intermediate fact. Rewrite `this` using `[add_comm]`. Then use the resulting hypothesis. Use `integer_combination_mem_lattice w₁ w₂ b a` as an intermediate fact.

Rewrite `this` using `[add_comm]`. Then use the resulting hypothesis. Apply `lattice_span_le` to reduce the goal to its premises. Use `integer_combination_mem_lattice ((c : ℂ) * w₂ + d * w₁) ((a : ℂ) * w₂ + b * w₁) a (-c)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `push_cast`.

Take the linear combination `(-w₁) * hdetC`. Use `integer_combination_mem_lattice ((c : ℂ) * w₂ + d * w₁) ((a : ℂ) * w₂ + b * w₁) (-b) d` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Take the linear combination `(-w₂) * hdetC`.

Rewrite using `[hq, UpperHalfPlane.coe_im]`. Conclude with `UpperHalfPlane.im_pos _`. Rewrite using `[hq, UpperHalfPlane.coe_im]`. Conclude with `h3`.
-/
lemma reduce_pos (w₁ w₂ : ℂ) (hw : 0 < ((starRingEnd ℂ) w₁ * w₂).im) :
    ∃ v₁ v₂ : ℂ, v₁ ≠ 0 ∧ PI.lat2 v₁ v₂ = PI.lat2 w₁ w₂ ∧ 0 < (v₂ / v₁).im ∧
      3 ≤ 4 * (v₂ / v₁).im ^ 2 := by
  have hw1 : w₁ ≠ 0 := by
    rintro rfl
    simp at hw
  have hN : 0 < Complex.normSq w₁ := Complex.normSq_pos.mpr hw1
  have him : 0 < (w₂ / w₁).im := by
    have e : (w₂ / w₁).im = ((starRingEnd ℂ) w₁ * w₂).im / Complex.normSq w₁ := by
      simp only [Complex.div_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [e]
    exact div_pos hw hN
  let τ : UpperHalfPlane := ⟨w₂ / w₁, him⟩
  have hτ : (τ : ℂ) = w₂ / w₁ := rfl
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
  have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg
  have hcoe := UpperHalfPlane.coe_specialLinearGroup_apply g τ
  have hdet0 := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at hdet0
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, b = (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := ⟨_, rfl⟩
  rw [← ha, ← hb, ← hc, ← hd] at hdet0 hcoe
  simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast] at hcoe
  have hdetC : (a : ℂ) * d - b * c = 1 := by exact_mod_cast hdet0
  have hden : (c : ℂ) * (w₂ / w₁) + d ≠ 0 := by
    intro h0
    have e1 : ((c : ℂ) * (w₂ / w₁) + d).im = c * (w₂ / w₁).im := by simp
    have e2 : ((c : ℂ) * (w₂ / w₁) + d).re = c * (w₂ / w₁).re + d := by simp
    rw [h0] at e1 e2
    simp only [Complex.zero_im, Complex.zero_re] at e1 e2
    have hc0 : (c : ℝ) = 0 := by
      rcases mul_eq_zero.mp e1.symm with h | h
      · exact h
      · linarith
    have hd0 : (d : ℝ) = 0 := by
      rw [hc0, zero_mul, zero_add] at e2
      linarith
    have hc0' : c = 0 := by exact_mod_cast hc0
    have hd0' : d = 0 := by exact_mod_cast hd0
    rw [hc0', hd0'] at hdet0
    simp at hdet0
  have hv1 : (c : ℂ) * w₂ + d * w₁ = w₁ * ((c : ℂ) * (w₂ / w₁) + d) := by
    field_simp
  have hv2 : (a : ℂ) * w₂ + b * w₁ = w₁ * ((a : ℂ) * (w₂ / w₁) + b) := by
    field_simp
  have hv1ne : (c : ℂ) * w₂ + d * w₁ ≠ 0 := by
    rw [hv1]
    exact mul_ne_zero hw1 hden
  have hq : ((a : ℂ) * w₂ + b * w₁) / ((c : ℂ) * w₂ + d * w₁) = ((g • τ : UpperHalfPlane) : ℂ) := by
    rw [hcoe, hτ, hv1, hv2, mul_div_mul_left _ _ hw1]
  refine ⟨(c : ℂ) * w₂ + d * w₁, (a : ℂ) * w₂ + b * w₁, hv1ne, le_antisymm ?_ ?_, ?_, ?_⟩
  · apply lattice_span_le
    · have := integer_combination_mem_lattice w₁ w₂ d c
      rwa [add_comm] at this
    · have := integer_combination_mem_lattice w₁ w₂ b a
      rwa [add_comm] at this
  · apply lattice_span_le
    · have := integer_combination_mem_lattice ((c : ℂ) * w₂ + d * w₁) ((a : ℂ) * w₂ + b * w₁) a (-c)
      convert this using 1
      push_cast
      linear_combination (-w₁) * hdetC
    · have := integer_combination_mem_lattice ((c : ℂ) * w₂ + d * w₁) ((a : ℂ) * w₂ + b * w₁) (-b) d
      convert this using 1
      push_cast
      linear_combination (-w₂) * hdetC
  · rw [hq, UpperHalfPlane.coe_im]
    exact UpperHalfPlane.im_pos _
  · rw [hq, UpperHalfPlane.coe_im]
    exact h3

/- English proof (translation)
Introduce `w₁ w₂ hw`. Break down `lt_or_gt_of_ne hw with h | h` into its components or cases. Establish `h' : 0 < ((starRingEnd ℂ) w₂ * w₁).im`. Establish `e : ((starRingEnd ℂ) w₂ * w₁).im = -((starRingEnd ℂ) w₁ * w₂).im`. Simplify using `only [Complex.mul_im, Complex.conj_re, Complex.conj_im]`.

Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨v₁, v₂, h1, h2, h3, h4⟩` from `reduce_pos w₂ w₁ h'`. Conclude with `⟨v₁, v₂, h1, by rw [h2, lattice_span_comm], h3, h4⟩`. Conclude with `reduce_pos w₁ w₂ h`.
-/
theorem reduceBasis : ReduceBasis := by
  intro w₁ w₂ hw
  rcases lt_or_gt_of_ne hw with h | h
  · have h' : 0 < ((starRingEnd ℂ) w₂ * w₁).im := by
      have e : ((starRingEnd ℂ) w₂ * w₁).im = -((starRingEnd ℂ) w₁ * w₂).im := by
        simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
        ring
      linarith
    obtain ⟨v₁, v₂, h1, h2, h3, h4⟩ := reduce_pos w₂ w₁ h'
    exact ⟨v₁, v₂, h1, by rw [h2, lattice_span_comm], h3, h4⟩
  · exact reduce_pos w₁ w₂ h

end PI.SSE

end
