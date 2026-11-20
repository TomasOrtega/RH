import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Metric

namespace PGaussPacking

/- English proof (translation)
Introduce `x hx y hy hxy`. Apply `ball_disjoint_ball` to reduce the goal to its premises. Rewrite using `[dist_eq_norm]`. Combine the linear relations using `[hsep x hx y hy hxy]`.
-/
theorem pairwiseDisjoint_balls {n : ℕ} (s : Finset (EuclideanSpace ℝ (Fin n))) {δ : ℝ}
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ ‖x - y‖) :
    (s : Set (EuclideanSpace ℝ (Fin n))).PairwiseDisjoint (fun x => ball x (δ / 2)) := by
  intro x hx y hy hxy
  apply ball_disjoint_ball
  rw [dist_eq_norm]
  linarith [hsep x hx y hy hxy]

/- English proof (translation)
Introduce `z hz`. Simplify using `only [Set.mem_iUnion] at hz`. Take `⟨x, hx, hz⟩` from `hz`. Rewrite `hz`, the goal using `[mem_ball, dist_eq_norm]`. Rewrite using `[sub_zero]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem biUnion_balls_subset {n : ℕ} (s : Finset (EuclideanSpace ℝ (Fin n))) {δ r : ℝ}
    (hs : ∀ x ∈ s, ‖x‖ ≤ r) :
    (⋃ x ∈ s, ball x (δ / 2)) ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) (r + δ / 2) := by
  intro z hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨x, hx, hz⟩ := hz
  rw [mem_ball, dist_eq_norm] at hz ⊢
  rw [sub_zero]
  calc ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
    _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
    _ < δ / 2 + r := by linarith [hs x hx]
    _ = r + δ / 2 := by ring

end PGaussPacking

open PGaussPacking in

/- English proof (translation)
Introduce `n s δ r hδ hr hsep hs`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Establish `h1 : s.card ≤ 1` using `Finset.card_le_one.2 (fun a _ b _ => Subsingleton.elim a b)`. Establish `h1' : (s.card : ℝ) ≤ 1` using `by exact_mod_cast h1`. Simplify using `using h1'`.

Establish `: Nontrivial (EuclideanSpace ℝ (Fin n))` using `Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hn)`. Establish `hδ2 : 0 < δ / 2` using `by positivity`. Establish `hR : 0 ≤ r + δ / 2` using `by positivity`. Establish `hmeas : ∑ x ∈ s, (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball x (δ / 2)) ≤ volume (ball (0 : EuclideanSpace ℝ (Fin n)) (r + δ / 2))`. Rewrite using `[← measure_biUnion_finset (pairwiseDisjoint_balls s hsep) (fun x _ => measurableSet_ball)]`.

Conclude with `measure_mono (biUnion_balls_subset s hs)`. Simplify using `only [Measure.addHaar_ball _ _ hδ2.le, Measure.addHaar_ball _ _ hR, finrank_euclideanSpace_fin, Finset.sum_const, nsmul_eq_mul] at hmeas`. Establish `hc0 : (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) ≠ 0` using `(measure_ball_pos _ _ one_pos).ne'`. Establish `hct : (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) ≠ ⊤` using `measure_ball_lt_top.ne`. Rewrite `hmeas` using `[← mul_assoc]`.

Establish `h2` using `(ENNReal.mul_le_mul_iff_left hc0 hct).1 hmeas`. Rewrite `h2` using `[← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)]`. Establish `hp : 0 < (δ / 2) ^ n` using `pow_pos hδ2 n`. Establish `key : (1 + 2 * r / δ) ^ n = (r + δ / 2) ^ n / (δ / 2) ^ n`. Rewrite using `[← div_pow]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, le_div_iff₀ hp]`. Conclude with `h2`.
-/
theorem GaussPacking.proof : GaussPacking.Statement := by
  intro n s δ r hδ hr hsep hs
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : s.card ≤ 1 := Finset.card_le_one.2 (fun a _ b _ => Subsingleton.elim a b)
    have h1' : (s.card : ℝ) ≤ 1 := by exact_mod_cast h1
    simpa using h1'
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hn)
  have hδ2 : 0 < δ / 2 := by positivity
  have hR : 0 ≤ r + δ / 2 := by positivity
  have hmeas : ∑ x ∈ s, (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball x (δ / 2)) ≤
      volume (ball (0 : EuclideanSpace ℝ (Fin n)) (r + δ / 2)) := by
    rw [← measure_biUnion_finset (pairwiseDisjoint_balls s hsep) (fun x _ => measurableSet_ball)]
    exact measure_mono (biUnion_balls_subset s hs)
  simp only [Measure.addHaar_ball _ _ hδ2.le, Measure.addHaar_ball _ _ hR,
    finrank_euclideanSpace_fin, Finset.sum_const, nsmul_eq_mul] at hmeas
  have hc0 : (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) ≠ 0 :=
    (measure_ball_pos _ _ one_pos).ne'
  have hct : (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  rw [← mul_assoc] at hmeas
  have h2 := (ENNReal.mul_le_mul_iff_left hc0 hct).1 hmeas
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  have hp : 0 < (δ / 2) ^ n := pow_pos hδ2 n
  have key : (1 + 2 * r / δ) ^ n = (r + δ / 2) ^ n / (δ / 2) ^ n := by
    rw [← div_pow]
    congr 1
    field_simp
    ring
  rw [key, le_div_iff₀ hp]
  exact h2

end GroundTheory.Heights₂.Heights
