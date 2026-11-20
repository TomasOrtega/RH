import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.DivisionNearS
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.DivisionDimOne
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.DivisionDimOneQuot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

/- English proof (translation)
Establish `hpos : 0 < ‖a‖ ^ 2` using `by positivity`. Rewrite using `[Real.rpow_neg hpos.le, Real.rpow_natCast, norm_mul, norm_pow]`. Establish `: (‖a‖ ^ 2) ^ n ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem normSq_pow_mul_rpow_neg (a b : ℂ) (ha : a ≠ 0) (n : ℕ) :
    ‖a ^ n * b‖ ^ 2 * (‖a‖ ^ 2) ^ (-(n : ℝ)) = ‖b‖ ^ 2 := by
  have hpos : 0 < ‖a‖ ^ 2 := by positivity
  rw [Real.rpow_neg hpos.le, Real.rpow_natCast, norm_mul, norm_pow]
  have : (‖a‖ ^ 2) ^ n ≠ 0 := by positivity
  field_simp
  ring

/- English proof (translation)
Use `show ∀ i, Z.s i (chartIdx X.A x) x = 0`. Introduce `i`. Rewrite using `[Subsingleton.elim i 0]`. Establish `hc : x ∈ (X.A.chart (chartIdx X.A x)).source` using `Classical.choose_spec (X.A.cover x)`. Establish `hmem : Z.s 0 ∈ X.L.sections 1` using `by show lin X.e (Z.c 0) ∈ X.L.sections 1`.

Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (X.e_mem k)`. Establish `key` using `hmem.2.1 j (chartIdx X.A x) x ⟨hx, hc⟩`. Rewrite `key` using `[h0, pow_one]`. Conclude with `(mul_eq_zero.mp key.symm).resolve_left (X.L.ne_zero _ _ x ⟨hx, hc⟩)`.
-/
theorem mem_S_of_s_eq_zero {X : EmbDatum 1} (Z : ZeroDatum X) {j : Fin X.A.n} {x : X.U}
    (hx : x ∈ (X.A.chart j).source) (h0 : Z.s 0 j x = 0) : x ∈ Z.S := by
  show ∀ i, Z.s i (chartIdx X.A x) x = 0
  intro i
  rw [Subsingleton.elim i 0]
  have hc : x ∈ (X.A.chart (chartIdx X.A x)).source := Classical.choose_spec (X.A.cover x)
  have hmem : Z.s 0 ∈ X.L.sections 1 := by
    show lin X.e (Z.c 0) ∈ X.L.sections 1
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (X.e_mem k)
  have key := hmem.2.1 j (chartIdx X.A x) x ⟨hx, hc⟩
  rw [h0, pow_one] at key
  exact (mul_eq_zero.mp key.symm).resolve_left (X.L.ne_zero _ _ x ⟨hx, hc⟩)

/- English proof (translation)
Introduce `T X Z φA hT F hF hfil`. Take `⟨h, hh, rfl⟩` from `hQuot T X Z hT _ hF.1 hfil`. Use `⟨h, ⟨hh, ?_⟩, rfl⟩` and prove the remaining obligations. Establish `hN` using `hNear 1 T X Z φA le_rfl hT _ hF hfil ((T : ℝ) - 2) (by linarith)`. Use `lt_of_le_of_lt ?_ hN` and prove the remaining obligations.

Establish `he1 : (T : ℝ) - 1 - ((T : ℝ) - 2) = 1` using `by ring`. Establish `he2 : -((T : ℝ) - 2 + 1) = -((T - 1 : ℕ) : ℝ)` using `by push_cast [Nat.cast_sub hT]; ring`. Unfold `topNormSq skodaNormSq chartIntegral`. Use `Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations. Use `lintegral_mono_ae ?_` and prove the remaining obligations.

Establish `hsub : volume.restrict (piece X.A j) ≪ volume.restrict (X.A.chart j).target` using `Measure.absolutelyContinuous_of_le (Measure.restrict_mono (fun y hy => hy.1) le_rfl)`. Use `hsub.ae_le ?_` and prove the remaining obligations. Use `(ae_restrict_iff' (X.A.chart j).open_target.measurableSet).mpr ?_` and prove the remaining obligations. Establish `hfin : ((X.A.chart j) '' Z.S).Finite` using `Z.finite.image _`. Use `filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hfin.measure_zero volume)] with y hy hyt`.

Establish `hxs : (X.A.chart j).symm y ∈ (X.A.chart j).source` using `(X.A.chart j).map_target hyt`. Establish `hs0 : Z.s 0 j ((X.A.chart j).symm y) ≠ 0` using `fun h0 => hy ⟨_, mem_S_of_s_eq_zero Z hxs h0, (X.A.chart j).right_inv hyt⟩`. Apply `le_of_eq` to reduce the goal to its premises. Use `congr 1`. Simplify using `only [Fin.sum_univ_one, Pi.mul_apply, Pi.pow_apply, he1, he2, Nat.cast_one, one_mul]`.

Rewrite using `[← normSq_pow_mul_rpow_neg _ (h j ((X.A.chart j).symm y)) hs0 (T - 1)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem DivisionDimOne.proof (hNear : DivisionNearS.Statement)
    (hQuot : DivisionDimOneQuot.Statement) : DivisionDimOne.Statement := by
  intro T X Z φA hT F hF hfil
  obtain ⟨h, hh, rfl⟩ := hQuot T X Z hT _ hF.1 hfil
  refine ⟨h, ⟨hh, ?_⟩, rfl⟩
  have hN := hNear 1 T X Z φA le_rfl hT _ hF hfil ((T : ℝ) - 2) (by linarith)
  refine lt_of_le_of_lt ?_ hN
  have he1 : (T : ℝ) - 1 - ((T : ℝ) - 2) = 1 := by ring
  have he2 : -((T : ℝ) - 2 + 1) = -((T - 1 : ℕ) : ℝ) := by push_cast [Nat.cast_sub hT]; ring
  unfold topNormSq skodaNormSq chartIntegral
  refine Finset.sum_le_sum fun j _ => ?_
  refine lintegral_mono_ae ?_
  have hsub : volume.restrict (piece X.A j) ≪ volume.restrict (X.A.chart j).target :=
    Measure.absolutelyContinuous_of_le (Measure.restrict_mono (fun y hy => hy.1) le_rfl)
  refine hsub.ae_le ?_
  refine (ae_restrict_iff' (X.A.chart j).open_target.measurableSet).mpr ?_
  have hfin : ((X.A.chart j) '' Z.S).Finite := Z.finite.image _
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hfin.measure_zero volume)] with y hy hyt
  have hxs : (X.A.chart j).symm y ∈ (X.A.chart j).source := (X.A.chart j).map_target hyt
  have hs0 : Z.s 0 j ((X.A.chart j).symm y) ≠ 0 := fun h0 =>
    hy ⟨_, mem_S_of_s_eq_zero Z hxs h0, (X.A.chart j).right_inv hyt⟩
  apply le_of_eq
  congr 1
  simp only [Fin.sum_univ_one, Pi.mul_apply, Pi.pow_apply, he1, he2, Nat.cast_one, one_mul]
  rw [← normSq_pow_mul_rpow_neg _ (h j ((X.A.chart j).symm y)) hs0 (T - 1)]
  ring

end

end GroundTheory.Heights₂.Heights.EffectiveHS
