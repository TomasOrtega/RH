import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCriticalImageNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

noncomputable section

section Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def shrinkAlong (i0 : ι) (k : ι → ℝ) (δ : ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.id - (1 - δ) • (LinearMap.proj i0 : (ι → ℝ) →ₗ[ℝ] ℝ).smulRight k

omit [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Simplify using `[shrinkAlong, smul_smul]`.
-/
theorem shrinkAlong_apply (i0 : ι) (k : ι → ℝ) (δ : ℝ) (z : ι → ℝ) :
    shrinkAlong i0 k δ z = z - ((1 - δ) * z i0) • k := by
  simp [shrinkAlong, smul_smul]

/- English proof (translation)
Rewrite using `[← LinearMap.det_toMatrix']`. Establish `hM : LinearMap.toMatrix' (shrinkAlong i0 k δ) = 1 + Matrix.replicateCol Unit (-(1 - δ) • k) * Matrix.replicateRow Unit (Pi.single i0 (1 : ℝ))`. Use extensionality with `i j`. Simplify using `only [LinearMap.toMatrix'_apply, shrinkAlong_apply, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.univ_unique, Finset.sum_singleton, Pi.single_apply]`. Apply the tactic sequence `by_cases hij : i = j <;> by_cases hj : j = i0 <;> simp [hij, hj, eq_comm (a := i0)] <;> ring`.

Rewrite using `[hM, Matrix.det_one_add_replicateCol_mul_replicateRow]`. Simplify using `[dotProduct, Pi.single_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_shrinkAlong (i0 : ι) (k : ι → ℝ) (δ : ℝ) :
    LinearMap.det (shrinkAlong i0 k δ) = 1 - (1 - δ) * k i0 := by
  rw [← LinearMap.det_toMatrix']
  have hM : LinearMap.toMatrix' (shrinkAlong i0 k δ) =
      1 + Matrix.replicateCol Unit (-(1 - δ) • k) * Matrix.replicateRow Unit (Pi.single i0 (1 : ℝ)) := by
    ext i j
    simp only [LinearMap.toMatrix'_apply, shrinkAlong_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Finset.univ_unique, Finset.sum_singleton, Pi.single_apply]
    by_cases hij : i = j <;> by_cases hj : j = i0 <;> simp [hij, hj, eq_comm (a := i0)] <;> ring
  rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct, Pi.single_apply]
  ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Establish `hδ0' : (0 : ℝ) < δ` using `by exact_mod_cast hδ0`. Establish `hδ1' : (δ : ℝ) ≤ 1` using `by exact_mod_cast hδ1`. Use `set T := shrinkAlong i0 k (δ : ℝ) with hTdef`. Establish `hT : ∀ z, T z = z - ((1 - (δ : ℝ)) * z i0) • k` using `shrinkAlong_apply i0 k _`. Establish `hTi : ∀ z, T z i0 = δ * z i0`.

Introduce `z`. Rewrite using `[hT]`. Simplify using `[hki]`. Expand and normalize the polynomial expressions, which then agree. Set `S : (ι → ℝ) → (ι → ℝ)` to `fun w => w + (((δ : ℝ)⁻¹ - 1) * w i0) • k`.

Establish `hST : ∀ x, S (T x) = x`. Introduce `x`. Simplify using `only [S, hTi]`. Establish `hδne : (δ : ℝ) ≠ 0` using `hδ0'.ne'`. Establish `: ((δ : ℝ)⁻¹ - 1) * (δ * x i0) = (1 - δ) * x i0` using `by field_simp`.

Rewrite using `[this, hT, sub_add_cancel]`. Establish `himg : f '' t = (f ∘ S) '' (T '' t)`. Rewrite using `[image_image]`. Simplify using `[hST]`. Establish `hlip : LipschitzOnWith (Real.toNNReal (‖A‖ + 1 + ‖k‖)) (f ∘ S) (T '' t)`.

Use `LipschitzOnWith.of_dist_le' ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩`. Simplify using `only [Function.comp_apply, hST, dist_eq_norm]`. Rewrite using `[← map_sub]`. Use `set v := x - y with hv`.

Establish `hAv : A v = A (T v)`. Rewrite using `[hT, map_sub A v, map_smul, hk, smul_zero, sub_zero]`. Establish `hsplit : (δ : ℝ) • v = (δ : ℝ) • T v + ((1 - δ) * T v i0) • k`. Rewrite using `[hTi, hT]`. Use extensionality with `j`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `hδv : (δ : ℝ) * ‖v‖ ≤ ‖T v‖ + ‖T v‖ * ‖k‖`. Establish `h1 : ‖(δ : ℝ) • T v‖ ≤ ‖T v‖`. Rewrite using `[norm_smul, Real.norm_of_nonneg hδ0'.le]`.

Conclude with `mul_le_of_le_one_left (norm_nonneg _) hδ1'`. Establish `h2 : ‖((1 - (δ : ℝ)) * T v i0) • k‖ ≤ ‖T v‖ * ‖k‖`. Rewrite using `[norm_smul, norm_mul, Real.norm_of_nonneg (by linarith)]`. Establish `h3 : ‖T v i0‖ ≤ ‖T v‖` using `norm_le_pi_norm _ _`. Establish `h4 : (1 - (δ : ℝ)) * ‖T v i0‖ ≤ ‖T v‖`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `mul_le_mul_of_nonneg_right h4 (norm_nonneg _)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hsplit]`. Conclude with `norm_add_le _ _`.

Use `_ ≤ ‖T v‖ + ‖T v‖ * ‖k‖ := add_le_add h1 h2`. Establish `happ` using `ht x hx y hy`. Establish `hAT : ‖A (T v)‖ ≤ ‖A‖ * ‖T v‖` using `A.le_opNorm _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[himg]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hausdorffMeasure_pi_real, Measure.addHaar_image_linearMap, hTdef, det_shrinkAlong, hki]`. Use `congr 3`. Rewrite using `[abs_of_pos (by linarith)]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = _ := by rw [mul_assoc]`.
-/
theorem hausdorffMeasure_image_le_of_approximatesLinearOn_of_mem_ker {f : (ι → ℝ) → F}
    {A : (ι → ℝ) →L[ℝ] F} {k : ι → ℝ} {i0 : ι} (hk : A k = 0) (hki : k i0 = 1) {δ : ℝ≥0}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {t : Set (ι → ℝ)} (ht : ApproximatesLinearOn f A t δ) :
    μH[Fintype.card ι] (f '' t) ≤
      ((Real.toNNReal (‖A‖ + 1 + ‖k‖) : ℝ≥0∞)) ^ (Fintype.card ι : ℝ) * ENNReal.ofReal δ *
        volume t := by
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hδ1' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  set T := shrinkAlong i0 k (δ : ℝ) with hTdef
  have hT : ∀ z, T z = z - ((1 - (δ : ℝ)) * z i0) • k := shrinkAlong_apply i0 k _
  have hTi : ∀ z, T z i0 = δ * z i0 := by
    intro z; rw [hT]; simp [hki]; ring
  let S : (ι → ℝ) → (ι → ℝ) := fun w => w + (((δ : ℝ)⁻¹ - 1) * w i0) • k
  have hST : ∀ x, S (T x) = x := by
    intro x
    simp only [S, hTi]
    have hδne : (δ : ℝ) ≠ 0 := hδ0'.ne'
    have : ((δ : ℝ)⁻¹ - 1) * (δ * x i0) = (1 - δ) * x i0 := by field_simp
    rw [this, hT, sub_add_cancel]
  have himg : f '' t = (f ∘ S) '' (T '' t) := by
    rw [image_image]; simp [hST]
  have hlip : LipschitzOnWith (Real.toNNReal (‖A‖ + 1 + ‖k‖)) (f ∘ S) (T '' t) := by
    refine LipschitzOnWith.of_dist_le' ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, hST, dist_eq_norm]
    rw [← map_sub]
    set v := x - y with hv
    have hAv : A v = A (T v) := by
      rw [hT, map_sub A v, map_smul, hk, smul_zero, sub_zero]
    have hsplit : (δ : ℝ) • v = (δ : ℝ) • T v + ((1 - δ) * T v i0) • k := by
      rw [hTi, hT]; ext j; simp; ring
    have hδv : (δ : ℝ) * ‖v‖ ≤ ‖T v‖ + ‖T v‖ * ‖k‖ := by
      have h1 : ‖(δ : ℝ) • T v‖ ≤ ‖T v‖ := by
        rw [norm_smul, Real.norm_of_nonneg hδ0'.le]
        exact mul_le_of_le_one_left (norm_nonneg _) hδ1'
      have h2 : ‖((1 - (δ : ℝ)) * T v i0) • k‖ ≤ ‖T v‖ * ‖k‖ := by
        rw [norm_smul, norm_mul, Real.norm_of_nonneg (by linarith)]
        have h3 : ‖T v i0‖ ≤ ‖T v‖ := norm_le_pi_norm _ _
        have h4 : (1 - (δ : ℝ)) * ‖T v i0‖ ≤ ‖T v‖ := by
          calc (1 - (δ : ℝ)) * ‖T v i0‖ ≤ 1 * ‖T v‖ :=
                mul_le_mul (by linarith) h3 (norm_nonneg _) zero_le_one
            _ = ‖T v‖ := one_mul _
        exact mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
      calc (δ : ℝ) * ‖v‖ = ‖(δ : ℝ) • v‖ := by rw [norm_smul, Real.norm_of_nonneg hδ0'.le]
        _ ≤ ‖(δ : ℝ) • T v‖ + ‖((1 - (δ : ℝ)) * T v i0) • k‖ := by
          rw [hsplit]; exact norm_add_le _ _
        _ ≤ ‖T v‖ + ‖T v‖ * ‖k‖ := add_le_add h1 h2
    have happ := ht x hx y hy
    have hAT : ‖A (T v)‖ ≤ ‖A‖ * ‖T v‖ := A.le_opNorm _
    calc ‖f x - f y‖ = ‖(f x - f y - A v) + A v‖ := by rw [sub_add_cancel]
      _ ≤ ‖f x - f y - A v‖ + ‖A v‖ := norm_add_le _ _
      _ ≤ (δ : ℝ) * ‖v‖ + ‖A‖ * ‖T v‖ := by rw [hAv] at happ ⊢; exact add_le_add happ hAT
      _ ≤ (‖A‖ + 1 + ‖k‖) * ‖T v‖ := by nlinarith [hδv]
  rw [himg]
  calc μH[Fintype.card ι] ((f ∘ S) '' (T '' t))
      ≤ ((Real.toNNReal (‖A‖ + 1 + ‖k‖) : ℝ≥0∞)) ^ (Fintype.card ι : ℝ) *
          μH[Fintype.card ι] (T '' t) := hlip.hausdorffMeasure_image_le (by positivity)
    _ = ((Real.toNNReal (‖A‖ + 1 + ‖k‖) : ℝ≥0∞)) ^ (Fintype.card ι : ℝ) *
          (ENNReal.ofReal δ * volume t) := by
      rw [hausdorffMeasure_pi_real, Measure.addHaar_image_linearMap, hTdef, det_shrinkAlong, hki]
      congr 3
      rw [abs_of_pos (by linarith)]
      ring
    _ = _ := by rw [mul_assoc]

end Real

section Global

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨a, b, hab, hne⟩ : ∃ a b, A a = A b ∧ a ≠ b := by`. Simplify `hA` using `[Function.Injective, not_forall]`. Establish `hk0 : a - b ≠ 0` using `sub_ne_zero.mpr hne`. Choose the witnesses or unpack the hypotheses as in `⟨i0, hi0⟩ : ∃ i0, (a - b) i0 ≠ 0 := by`. Simplify using `using Function.ne_iff.mp hk0`.

Use `set k : ι → ℝ := ((a - b) i0)⁻¹ • (a - b) with hkdef`. Establish `hk : A k = 0` using `by rw [hkdef, map_smul, map_sub, hab, sub_self, smul_zero]`. Establish `hki : k i0 = 1`. Rewrite using `[hkdef, Pi.smul_apply, smul_eq_mul]`. Conclude with `inv_mul_cancel₀ hi0`.

Use `set K : ℝ≥0 := Real.toNNReal (‖A‖ + 1 + ‖k‖)`. Use `set δ : ℝ≥0 := min 1 (ε / (K ^ Fintype.card ι + 1))`. Establish `hδ0 : 0 < δ` using `lt_min one_pos (div_pos hε (by positivity))`. Use `⟨δ, hδ0, fun t ht => ?_⟩` and prove the remaining obligations. Establish `key` using `hausdorffMeasure_image_le_of_approximatesLinearOn_of_mem_ker hk hki hδ0 (min_le_left _ _) ht`.

Use `key.trans ?_` and prove the remaining obligations. Establish `hKδ : K ^ Fintype.card ι * δ ≤ ε`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_self_add`. Conclude with `min_le_right _ _`.

Use `_ = ε := by`. Rewrite using `[mul_div_assoc']`. Conclude with `mul_div_cancel_left₀ ε (by positivity)`. Establish `hcoe : (K : ℝ≥0∞) ^ (Fintype.card ι : ℝ) * ENNReal.ofReal δ = ((K ^ Fintype.card ι * δ : ℝ≥0) : ℝ≥0∞)`. Rewrite using `[ENNReal.rpow_natCast, ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul, ENNReal.coe_pow]`.

Rewrite using `[hcoe]`. Use `gcongr`.
-/
theorem exists_pos_hausdorffMeasure_image_le_of_not_injective (f : (ι → ℝ) → F)
    (A : (ι → ℝ) →L[ℝ] F) (hA : ¬ Function.Injective A) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ t : Set (ι → ℝ), ApproximatesLinearOn f A t δ →
      μH[Fintype.card ι] (f '' t) ≤ ε * volume t := by
  obtain ⟨a, b, hab, hne⟩ : ∃ a b, A a = A b ∧ a ≠ b := by
    simpa [Function.Injective, not_forall] using hA
  have hk0 : a - b ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨i0, hi0⟩ : ∃ i0, (a - b) i0 ≠ 0 := by
    simpa using Function.ne_iff.mp hk0
  set k : ι → ℝ := ((a - b) i0)⁻¹ • (a - b) with hkdef
  have hk : A k = 0 := by rw [hkdef, map_smul, map_sub, hab, sub_self, smul_zero]
  have hki : k i0 = 1 := by
    rw [hkdef, Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hi0
  set K : ℝ≥0 := Real.toNNReal (‖A‖ + 1 + ‖k‖)
  set δ : ℝ≥0 := min 1 (ε / (K ^ Fintype.card ι + 1))
  have hδ0 : 0 < δ := lt_min one_pos (div_pos hε (by positivity))
  refine ⟨δ, hδ0, fun t ht => ?_⟩
  have key :=
    hausdorffMeasure_image_le_of_approximatesLinearOn_of_mem_ker hk hki hδ0 (min_le_left _ _) ht
  refine key.trans ?_
  have hKδ : K ^ Fintype.card ι * δ ≤ ε := by
    calc K ^ Fintype.card ι * δ ≤ (K ^ Fintype.card ι + 1) * (ε / (K ^ Fintype.card ι + 1)) := by
          gcongr
          · exact le_self_add
          · exact min_le_right _ _
      _ = ε := by
        rw [mul_div_assoc']
        exact mul_div_cancel_left₀ ε (by positivity)
  have hcoe : (K : ℝ≥0∞) ^ (Fintype.card ι : ℝ) * ENNReal.ofReal δ =
      ((K ^ Fintype.card ι * δ : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.rpow_natCast, ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul, ENNReal.coe_pow]
  rw [hcoe]
  gcongr

variable [SecondCountableTopology F]

/- English proof (translation)
Break down `eq_empty_or_nonempty s with (rfl | h's)` into its components or cases. Simplify using the standard rewrite rules. Establish `: ∀ A : (ι → ℝ) →L[ℝ] F, ∃ δ : ℝ≥0, 0 < δ ∧ (¬ Function.Injective A → ∀ t : Set (ι → ℝ), ApproximatesLinearOn f A t δ → μH[Fintype.card ι] (f '' t) ≤ ε * volume t)`. Introduce `A`. Distinguish the cases in `hA : Function.Injective A`.

Conclude with `⟨1, one_pos, fun h => absurd hA h⟩`. Take `⟨δ, hδ, h⟩` from `exists_pos_hausdorffMeasure_image_le_of_not_injective f A hA εpos`. Conclude with `⟨δ, hδ, fun _ => h⟩`. Use `choose δ hδ using this`. Take `⟨t, A, t_disj, t_meas, t_cover, ht, Af'⟩` from `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ fun A => (hδ A).1.ne'`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← image_iUnion, ← inter_iUnion]`. Use `gcongr`. Conclude with `subset_inter Subset.rfl t_cover`. Use `_ ≤ ∑' n, μH[Fintype.card ι] (f '' (s ∩ t n)) := measure_iUnion_le _`.

Use `_ ≤ ∑' n, (ε : ℝ≥0∞) * volume (s ∩ t n) := by gcongr with n`. Take `⟨y, ys, hy⟩` from `Af' h's n`. Conclude with `(hδ (A n)).2 (by rw [hy]; exact hinj y ys) _ (ht n)`. Use `_ ≤ ε * ∑' n, volume (closedBall (0 : ι → ℝ) R ∩ t n) := by`. Rewrite using `[ENNReal.tsum_mul_left]`.

Use `gcongr`. Use `_ = ε * volume (⋃ n, closedBall (0 : ι → ℝ) R ∩ t n) := by`. Rewrite using `[measure_iUnion]`. Conclude with `pairwise_disjoint_mono t_disj fun n => inter_subset_right`. Introduce `n`.

Conclude with `measurableSet_closedBall.inter (t_meas n)`. Use `_ ≤ ε * volume (closedBall (0 : ι → ℝ) R) := by grw [← inter_iUnion, inter_subset_left]`.
-/
theorem hausdorffMeasure_image_le_of_not_injective_ball {f : (ι → ℝ) → F} {s : Set (ι → ℝ)}
    {f' : (ι → ℝ) → (ι → ℝ) →L[ℝ] F} (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hinj : ∀ x ∈ s, ¬ Function.Injective (f' x)) (R : ℝ) (hs : s ⊆ closedBall 0 R)
    (ε : ℝ≥0) (εpos : 0 < ε) :
    μH[Fintype.card ι] (f '' s) ≤ ε * volume (closedBall (0 : ι → ℝ) R) := by
  rcases eq_empty_or_nonempty s with (rfl | h's)
  · simp
  have : ∀ A : (ι → ℝ) →L[ℝ] F, ∃ δ : ℝ≥0, 0 < δ ∧ (¬ Function.Injective A →
      ∀ t : Set (ι → ℝ), ApproximatesLinearOn f A t δ →
        μH[Fintype.card ι] (f '' t) ≤ ε * volume t) := by
    intro A
    by_cases hA : Function.Injective A
    · exact ⟨1, one_pos, fun h => absurd hA h⟩
    · obtain ⟨δ, hδ, h⟩ := exists_pos_hausdorffMeasure_image_le_of_not_injective f A hA εpos
      exact ⟨δ, hδ, fun _ => h⟩
  choose δ hδ using this
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, Af'⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ
      fun A => (hδ A).1.ne'
  calc
    μH[Fintype.card ι] (f '' s) ≤ μH[Fintype.card ι] (⋃ n, f '' (s ∩ t n)) := by
      rw [← image_iUnion, ← inter_iUnion]
      gcongr
      exact subset_inter Subset.rfl t_cover
    _ ≤ ∑' n, μH[Fintype.card ι] (f '' (s ∩ t n)) := measure_iUnion_le _
    _ ≤ ∑' n, (ε : ℝ≥0∞) * volume (s ∩ t n) := by
      gcongr with n
      obtain ⟨y, ys, hy⟩ := Af' h's n
      exact (hδ (A n)).2 (by rw [hy]; exact hinj y ys) _ (ht n)
    _ ≤ ε * ∑' n, volume (closedBall (0 : ι → ℝ) R ∩ t n) := by
      rw [ENNReal.tsum_mul_left]
      gcongr
    _ = ε * volume (⋃ n, closedBall (0 : ι → ℝ) R ∩ t n) := by
      rw [measure_iUnion]
      · exact pairwise_disjoint_mono t_disj fun n => inter_subset_right
      · intro n
        exact measurableSet_closedBall.inter (t_meas n)
    _ ≤ ε * volume (closedBall (0 : ι → ℝ) R) := by grw [← inter_iUnion, inter_subset_left]

/- English proof (translation)
It suffices to establish `H : ∀ R, μH[Fintype.card ι] (f '' (s ∩ closedBall 0 R)) = 0 by`. Rewrite using `[← nonpos_iff_eq_zero, ← iUnion_inter_closedBall_nat s 0]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[image_iUnion]`. Conclude with `measure_iUnion_le _`.

Use `_ ≤ 0 := by simp only [H, tsum_zero, le_refl]`. Introduce `R`. Establish `hA : ∀ ε : ℝ≥0, 0 < ε → μH[Fintype.card ι] (f '' (s ∩ closedBall 0 R)) ≤ ε * volume (closedBall (0 : ι → ℝ) R)` using `fun ε εpos => hausdorffMeasure_image_le_of_not_injective_ball (fun x hx => (hf' x hx.1).mono inter_subset_left) (fun x hx => hinj x hx.1) R inter_subset_right ε εpos`. Establish `hB : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * volume (closedBall (0 : ι → ℝ) R)) (𝓝[>] 0) (𝓝 0)`. Establish `: Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * volume (closedBall (0 : ι → ℝ) R)) (𝓝 0) (𝓝 (((0 : ℝ≥0) : ℝ≥0∞) * volume (closedBall (0 : ι → ℝ) R)))` using `ENNReal.Tendsto.mul_const (ENNReal.tendsto_coe.2 tendsto_id) (Or.inr measure_closedBall_lt_top.ne)`.

Simplify using `only [zero_mul, ENNReal.coe_zero] at this`. Conclude with `Tendsto.mono_left this nhdsWithin_le_nhds`. Rewrite using `[← nonpos_iff_eq_zero]`. Apply `ge_of_tendsto hB` to reduce the goal to its premises. Use `filter_upwards [self_mem_nhdsWithin]`.

Conclude with `hA`.
-/
theorem hausdorffMeasure_image_eq_zero_of_not_injective {f : (ι → ℝ) → F} {s : Set (ι → ℝ)}
    {f' : (ι → ℝ) → (ι → ℝ) →L[ℝ] F} (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hinj : ∀ x ∈ s, ¬ Function.Injective (f' x)) :
    μH[Fintype.card ι] (f '' s) = 0 := by
  suffices H : ∀ R, μH[Fintype.card ι] (f '' (s ∩ closedBall 0 R)) = 0 by
    rw [← nonpos_iff_eq_zero, ← iUnion_inter_closedBall_nat s 0]
    calc
      μH[Fintype.card ι] (f '' ⋃ n : ℕ, s ∩ closedBall 0 n)
          ≤ ∑' n : ℕ, μH[Fintype.card ι] (f '' (s ∩ closedBall 0 n)) := by
        rw [image_iUnion]; exact measure_iUnion_le _
      _ ≤ 0 := by simp only [H, tsum_zero, le_refl]
  intro R
  have hA : ∀ ε : ℝ≥0, 0 < ε →
      μH[Fintype.card ι] (f '' (s ∩ closedBall 0 R)) ≤ ε * volume (closedBall (0 : ι → ℝ) R) :=
    fun ε εpos => hausdorffMeasure_image_le_of_not_injective_ball
      (fun x hx => (hf' x hx.1).mono inter_subset_left) (fun x hx => hinj x hx.1) R
      inter_subset_right ε εpos
  have hB : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * volume (closedBall (0 : ι → ℝ) R)) (𝓝[>] 0)
      (𝓝 0) := by
    have : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * volume (closedBall (0 : ι → ℝ) R)) (𝓝 0)
        (𝓝 (((0 : ℝ≥0) : ℝ≥0∞) * volume (closedBall (0 : ι → ℝ) R))) :=
      ENNReal.Tendsto.mul_const (ENNReal.tendsto_coe.2 tendsto_id)
        (Or.inr measure_closedBall_lt_top.ne)
    simp only [zero_mul, ENNReal.coe_zero] at this
    exact Tendsto.mono_left this nhdsWithin_le_nhds
  rw [← nonpos_iff_eq_zero]
  apply ge_of_tendsto hB
  filter_upwards [self_mem_nhdsWithin]
  exact hA

end Global

/- English proof (translation)
Introduce `d n U f hU hf`. Set `b` to `Pi.basis (fun _ : Fin d => Complex.basisOneI)`. Set `e : ((Σ _ : Fin d, Fin 2) → ℝ) ≃L[ℝ] (Fin d → ℂ)` to `b.equivFun.symm.toContinuousLinearEquiv`. Establish `hcard : Fintype.card (Σ _ : Fin d, Fin 2) = 2 * d`. Simplify using `[Fintype.card_sigma, mul_comm]`.

Use `set C := {s | s ∈ U ∧ ¬ Function.Injective (fderiv ℂ f s)} with hC`. Establish `himg : f '' C = (f ∘ e) '' (e ⁻¹' C)`. Rewrite using `[image_comp, image_preimage_eq _ e.surjective]`. Establish `key` using `hausdorffMeasure_image_eq_zero_of_not_injective (f := f ∘ e) (s := e ⁻¹' C) (f' := fun x => ((fderiv ℂ f (e x)).restrictScalars ℝ).comp (e : _ →L[ℝ] _)) ?_ ?_`. Rewrite using `[himg, ← hcard]`.

Conclude with `key`. Introduce `x hx`. Establish `hU' : U ∈ 𝓝 (e x)` using `hU.mem_nhds hx.1`. Establish `h1 : HasFDerivAt f (fderiv ℂ f (e x)) (e x)` using `(hf.differentiableAt hU').hasFDerivAt`. Conclude with `((h1.restrictScalars ℝ).comp x e.hasFDerivAt).hasFDerivWithinAt`.

Introduce `x hx hinj`. Apply `hx.2` to reduce the goal to its premises. Introduce `a c hac`. Establish `h2` using `@hinj (e.symm a) (e.symm c) (by simpa using hac)`. Simplify using `using congrArg e h2`.
-/
theorem CriticalImageNull.proof : CriticalImageNull.Statement := by
  intro d n U f hU hf
  let b := Pi.basis (fun _ : Fin d => Complex.basisOneI)
  let e : ((Σ _ : Fin d, Fin 2) → ℝ) ≃L[ℝ] (Fin d → ℂ) :=
    b.equivFun.symm.toContinuousLinearEquiv
  have hcard : Fintype.card (Σ _ : Fin d, Fin 2) = 2 * d := by
    simp [Fintype.card_sigma, mul_comm]
  set C := {s | s ∈ U ∧ ¬ Function.Injective (fderiv ℂ f s)} with hC
  have himg : f '' C = (f ∘ e) '' (e ⁻¹' C) := by
    rw [image_comp, image_preimage_eq _ e.surjective]
  have key := hausdorffMeasure_image_eq_zero_of_not_injective (f := f ∘ e) (s := e ⁻¹' C)
    (f' := fun x => ((fderiv ℂ f (e x)).restrictScalars ℝ).comp (e : _ →L[ℝ] _)) ?_ ?_
  · rw [himg, ← hcard]
    exact key
  · intro x hx
    have hU' : U ∈ 𝓝 (e x) := hU.mem_nhds hx.1
    have h1 : HasFDerivAt f (fderiv ℂ f (e x)) (e x) := (hf.differentiableAt hU').hasFDerivAt
    exact ((h1.restrictScalars ℝ).comp x e.hasFDerivAt).hasFDerivWithinAt
  · intro x hx hinj
    apply hx.2
    intro a c hac
    have h2 := @hinj (e.symm a) (e.symm c) (by simpa using hac)
    simpa using congrArg e h2

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
