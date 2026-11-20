import Mathlib

namespace GroundTheory.Global

open MeasureTheory Module Set Filter Topology
open scoped RealInnerProductSpace FourierTransform SchwartzMap

noncomputable section

section DualLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun x hx => inner_self_eq_zero.mp (hx x), fun y hy => inner_self_eq_zero.mp (hy y)⟩`.
-/
theorem innerₗ_nondegenerate : (innerₗ E : LinearMap.BilinForm ℝ E).Nondegenerate :=
  ⟨fun x hx => inner_self_eq_zero.mp (hx x), fun y hy => inner_self_eq_zero.mp (hy y)⟩

def dualLattice (L : Submodule ℤ E) : Submodule ℤ E :=
  LinearMap.BilinForm.dualSubmodule (innerₗ E) L

/- English proof (translation)
Simplify using `only [dualLattice, LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one, innerₗ_apply_apply, algebraMap_int_eq, eq_intCast]`. Conclude with `forall₂_congr fun ℓ _ => exists_congr fun k => eq_comm`.
-/
theorem mem_dualLattice {L : Submodule ℤ E} {μ : E} :
    μ ∈ dualLattice L ↔ ∀ ℓ ∈ L, ∃ k : ℤ, ⟪μ, ℓ⟫ = k := by
  simp only [dualLattice, LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one,
    innerₗ_apply_apply, algebraMap_int_eq, eq_intCast]
  exact forall₂_congr fun ℓ _ => exists_congr fun k => eq_comm

/- English proof (translation)
The claim follows from `LinearMap.BilinForm.dualSubmodule_span_of_basis _ _ b`.
-/
theorem dualLattice_span_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) :
    dualLattice (Submodule.span ℤ (Set.range b)) = Submodule.span ℤ
      (Set.range (LinearMap.BilinForm.dualBasis (innerₗ E) innerₗ_nondegenerate b)) :=
  LinearMap.BilinForm.dualSubmodule_span_of_basis _ _ b

variable [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/- English proof (translation)
Use `conv_lhs => rw [← (Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ]`. Conclude with `dualLattice_span_eq _`.
-/
theorem dualLattice_eq_span : dualLattice L = Submodule.span ℤ
    (Set.range (LinearMap.BilinForm.dualBasis (innerₗ E) innerₗ_nondegenerate
      ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L))) := by
  classical
  conv_lhs => rw [← (Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ]
  exact dualLattice_span_eq _

instance : DiscreteTopology (dualLattice L) := by
  rw [dualLattice_eq_span L]; infer_instance

instance : IsZLattice ℝ (dualLattice L) :=
  ⟨by rw [dualLattice_eq_span L]; exact ZSpan.span_top _⟩

end DualLattice

section Summability

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] in

/- English proof (translation)
Use `⟨2 ^ k * (SchwartzMap.seminorm ℝ 0 0 g + SchwartzMap.seminorm ℝ k 0 g), by positivity, fun x => ?_⟩` and prove the remaining obligations. Establish `h1 : ‖g x‖ ≤ SchwartzMap.seminorm ℝ 0 0 g`. Simplify using `using g.norm_pow_mul_le_seminorm ℝ 0 x`. Establish `h2 : ‖x‖ ^ (0 + k) * ‖g x‖ ≤ SchwartzMap.seminorm ℝ k 0 g`. Simplify using `using g.norm_pow_mul_le_seminorm ℝ k x`.

Use `pow_mul_le_of_le_of_pow_mul_le (norm_nonneg x) (norm_nonneg _) h1 h2` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_norm_le_inv_one_add_pow (g : 𝓢(E, F)) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖g x‖ ≤ C * ((1 + ‖x‖) ^ k)⁻¹ := by
  refine ⟨2 ^ k * (SchwartzMap.seminorm ℝ 0 0 g + SchwartzMap.seminorm ℝ k 0 g), by positivity,
    fun x => ?_⟩
  have h1 : ‖g x‖ ≤ SchwartzMap.seminorm ℝ 0 0 g := by
    simpa using g.norm_pow_mul_le_seminorm ℝ 0 x
  have h2 : ‖x‖ ^ (0 + k) * ‖g x‖ ≤ SchwartzMap.seminorm ℝ k 0 g := by
    simpa using g.norm_pow_mul_le_seminorm ℝ k x
  have := pow_mul_le_of_le_of_pow_mul_le (norm_nonneg x) (norm_nonneg _) h1 h2
  simpa using this

/- English proof (translation)
Use `set k := finrank ℤ Λ + 1`. Take `⟨C, hC, hg⟩` from `exists_norm_le_inv_one_add_pow g k`. Use `set R' := max R 0`. Use `⟨fun ℓ => C * (1 + R') ^ k * ((1 + ‖ℓ‖) ^ k)⁻¹, ?_, ?_⟩` and prove the remaining obligations. Apply `Summable.mul_left` to reduce the goal to its premises.

Establish `hs` using `ZLattice.summable_norm_pow_inv (L := Λ) k (by omega)`. Use `Summable.of_norm_bounded_eventually hs ?_` and prove the remaining obligations. Use `filter_upwards [(Set.finite_singleton (0 : Λ)).compl_mem_cofinite] with ℓ hℓ`. Establish `hpos : 0 < ‖ℓ‖` using `norm_pos_iff.mpr hℓ`. Rewrite using `[Real.norm_of_nonneg (by positivity), inv_pow]`.

Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `ℓ x hx`. Establish `hR : ‖x‖ ≤ R'` using `hx.trans (le_max_left _ _)`. Establish `hR0 : 0 ≤ R'` using `le_max_right _ _`.

Establish `key : 1 + ‖ℓ‖ ≤ (1 + R') * (1 + ‖x + ℓ‖)`. Establish `: ‖(ℓ : E)‖ ≤ ‖x + ℓ‖ + ‖x‖`. Combine the equalities or inequalities in the displayed calculation. Establish `h' : ‖ℓ‖ ≤ ‖x + ℓ‖ + ‖x‖` using `this`. Use polynomial arithmetic with `[norm_nonneg (x + ℓ)]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow, mul_inv, ← mul_assoc ((1 + R') ^ k), mul_inv_cancel₀ (by positivity), one_mul]`. Use `_ ≤ C * ((1 + R') ^ k * ((1 + ‖ℓ‖) ^ k)⁻¹) := by gcongr`. Use `_ = C * (1 + R') ^ k * ((1 + ‖ℓ‖) ^ k)⁻¹ := by ring`.
-/
theorem exists_summable_bound_comp_add (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (g : 𝓢(E, F)) (R : ℝ) :
    ∃ u : Λ → ℝ, Summable u ∧ ∀ ℓ : Λ, ∀ x : E, ‖x‖ ≤ R → ‖g (x + ℓ)‖ ≤ u ℓ := by
  set k := finrank ℤ Λ + 1
  obtain ⟨C, hC, hg⟩ := exists_norm_le_inv_one_add_pow g k
  set R' := max R 0
  refine ⟨fun ℓ => C * (1 + R') ^ k * ((1 + ‖ℓ‖) ^ k)⁻¹, ?_, ?_⟩
  · apply Summable.mul_left
    have hs := ZLattice.summable_norm_pow_inv (L := Λ) k (by omega)
    refine Summable.of_norm_bounded_eventually hs ?_
    filter_upwards [(Set.finite_singleton (0 : Λ)).compl_mem_cofinite] with ℓ hℓ
    have hpos : 0 < ‖ℓ‖ := norm_pos_iff.mpr hℓ
    rw [Real.norm_of_nonneg (by positivity), inv_pow]
    gcongr
    linarith
  · intro ℓ x hx
    have hR : ‖x‖ ≤ R' := hx.trans (le_max_left _ _)
    have hR0 : 0 ≤ R' := le_max_right _ _
    have key : 1 + ‖ℓ‖ ≤ (1 + R') * (1 + ‖x + ℓ‖) := by
      have : ‖(ℓ : E)‖ ≤ ‖x + ℓ‖ + ‖x‖ := by
        calc ‖(ℓ : E)‖ = ‖(x + ℓ) - x‖ := by simp
          _ ≤ ‖x + ℓ‖ + ‖x‖ := norm_sub_le _ _
      have h' : ‖ℓ‖ ≤ ‖x + ℓ‖ + ‖x‖ := this
      nlinarith [norm_nonneg (x + ℓ)]
    calc ‖g (x + ℓ)‖ ≤ C * ((1 + ‖x + ℓ‖) ^ k)⁻¹ := hg _
      _ = C * ((1 + R') ^ k * (((1 + R') * (1 + ‖x + ℓ‖)) ^ k)⁻¹) := by
          rw [mul_pow, mul_inv, ← mul_assoc ((1 + R') ^ k), mul_inv_cancel₀ (by positivity), one_mul]
      _ ≤ C * ((1 + R') ^ k * ((1 + ‖ℓ‖) ^ k)⁻¹) := by
          gcongr
      _ = C * (1 + R') ^ k * ((1 + ‖ℓ‖) ^ k)⁻¹ := by ring

/- English proof (translation)
Take `⟨u, hu, hb⟩` from `exists_summable_bound_comp_add Λ g ‖x‖`. Conclude with `hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ℓ => hb ℓ x le_rfl)`.
-/
theorem summable_norm_comp_add (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (g : 𝓢(E, F)) (x : E) : Summable fun ℓ : Λ => ‖g (x + ℓ)‖ := by
  obtain ⟨u, hu, hb⟩ := exists_summable_bound_comp_add Λ g ‖x‖
  exact hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ℓ => hb ℓ x le_rfl)

/- English proof (translation)
Use `continuous_iff_continuousAt.mpr fun x₀ => ?_` and prove the remaining obligations. Take `⟨u, hu, hb⟩` from `exists_summable_bound_comp_add Λ g (‖x₀‖ + 1)`. Establish `hc : ContinuousOn (fun x => ∑' ℓ : Λ, g (x + ℓ)) (Metric.closedBall 0 (‖x₀‖ + 1))` using `continuousOn_tsum (fun ℓ => (g.continuous.comp (continuous_id.add continuous_const)).continuousOn) hu (fun ℓ x hx => hb ℓ x (by simpa using hx))`. Conclude with `hc.continuousAt (Metric.closedBall_mem_nhds_of_mem (by simp))`.
-/
theorem continuous_tsum_comp_add [CompleteSpace F] (Λ : Submodule ℤ E)
    [DiscreteTopology Λ] (g : 𝓢(E, F)) : Continuous fun x => ∑' ℓ : Λ, g (x + ℓ) := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  obtain ⟨u, hu, hb⟩ := exists_summable_bound_comp_add Λ g (‖x₀‖ + 1)
  have hc : ContinuousOn (fun x => ∑' ℓ : Λ, g (x + ℓ)) (Metric.closedBall 0 (‖x₀‖ + 1)) :=
    continuousOn_tsum (fun ℓ => (g.continuous.comp (continuous_id.add continuous_const)).continuousOn)
      hu (fun ℓ x hx => hb ℓ x (by simpa using hx))
  exact hc.continuousAt (Metric.closedBall_mem_nhds_of_mem (by simp))

end Summability

end

end GroundTheory.Global
