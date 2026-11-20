import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSmallSetBallCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSmallSetTubeVolume
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets Metric

noncomputable section

/- English proof (translation)
Rewrite using `[ball_pi c hρ, volume_pi_pi]`. Simplify using `only [Complex.volume_ball, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hρ.le, mul_comm, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]`.
-/
theorem volume_ball_pi_complex {n : ℕ} (c : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    volume (ball c ρ) = ENNReal.ofReal ((Real.pi * ρ ^ 2) ^ n) := by
  rw [ball_pi c hρ, volume_pi_pi]
  simp only [Complex.volume_ball, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hρ.le,
    mul_comm, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]

/- English proof (translation)
Use `set δ : NNReal := ⟨r / 4, by positivity⟩`. Establish `hδ : (δ : ℝ) = r / 4` using `rfl`. Establish `hpack : packingNumber (2 * δ) A ≠ ⊤`. Take `⟨N, -, hNfin, hN⟩` from `exists_finite_isCover_of_isCompact (ε := δ) (by rw [ne_eq, ← NNReal.coe_eq_zero, hδ]; positivity) hA`. Conclude with `ne_top_of_le_ne_top (Set.encard_ne_top_iff.2 hNfin) ((packingNumber_two_mul_le_externalCoveringNumber δ A).trans hN.externalCoveringNumber_le_encard)`.

Use `set S := maximalSeparatedSet (2 * δ) A`. Establish `hSfin : S.Finite` using `Set.encard_ne_top_iff.1 (by rw [encard_maximalSeparatedSet hpack]; exact hpack)`. Use `⟨hSfin.toFinset, by simpa using maximalSeparatedSet_subset, ?_, ?_⟩` and prove the remaining obligations. Use `((isCover_maximalSeparatedSet hpack).subset_iUnion_closedBall).trans ?_` and prove the remaining obligations. Use `Set.iUnion₂_subset fun c hc => ?_` and prove the remaining obligations.

Use `(closedBall_subset_ball ?_).trans (Set.subset_biUnion_of_mem (u := fun c => ball c r) ?_)` and prove the remaining obligations. Simplify using `only [NNReal.coe_mul, NNReal.coe_ofNat, hδ]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `using hc`. Establish `hsep` using `isSeparated_maximalSeparatedSet (ε := 2 * δ) (A := A)`.

Establish `hdisj : (↑hSfin.toFinset : Set (Fin n → ℂ)).PairwiseDisjoint (fun c => ball c (r / 4))`. Introduce `x hx y hy hxy`. Apply `ball_disjoint_ball` to reduce the goal to its premises. Establish `h1 : ((2 * δ : NNReal) : ENNReal) < edist x y` using `hsep (by simpa using hx) (by simpa using hy) hxy`. Rewrite `h1` using `[edist_dist, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)]`.

Simplify using `only [NNReal.coe_mul, NNReal.coe_ofNat, hδ] at h1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsub : (⋃ c ∈ hSfin.toFinset, ball c (r / 4)) ⊆ thickening r A`. Use `Set.iUnion₂_subset fun c hc => ?_` and prove the remaining obligations. Conclude with `(ball_subset_thickening (maximalSeparatedSet_subset (by simpa using hc)) _).trans (thickening_mono (by linarith) A)`.

Establish `hvol` using `measure_mono (μ := volume) hsub`. Rewrite `hvol` using `[measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]`. Simplify using `only [volume_ball_pi_complex _ (by positivity : (0 : ℝ) < r / 4), Finset.sum_const, nsmul_eq_mul] at hvol`. Establish `hfin : volume (thickening r A) ≠ ⊤` using `(hA.isBounded.thickening).measure_lt_top.ne`. Use `ENNReal.toReal_mono hfin hvol` as an intermediate fact.

Rewrite `this` using `[ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)]`. Then use the resulting hypothesis.
-/
theorem exists_cover_le_volume_thickening {n : ℕ} {A : Set (Fin n → ℂ)} (hA : IsCompact A) {r : ℝ}
    (hr : 0 < r) : ∃ T : Finset (Fin n → ℂ), (↑T : Set (Fin n → ℂ)) ⊆ A ∧ A ⊆ ⋃ c ∈ T, ball c r ∧
      (T.card : ℝ) * (Real.pi * (r / 4) ^ 2) ^ n ≤ (volume (thickening r A)).toReal := by
  set δ : NNReal := ⟨r / 4, by positivity⟩
  have hδ : (δ : ℝ) = r / 4 := rfl
  have hpack : packingNumber (2 * δ) A ≠ ⊤ := by
    obtain ⟨N, -, hNfin, hN⟩ := exists_finite_isCover_of_isCompact (ε := δ)
      (by rw [ne_eq, ← NNReal.coe_eq_zero, hδ]; positivity) hA
    exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.2 hNfin)
      ((packingNumber_two_mul_le_externalCoveringNumber δ A).trans hN.externalCoveringNumber_le_encard)
  set S := maximalSeparatedSet (2 * δ) A
  have hSfin : S.Finite := Set.encard_ne_top_iff.1 (by rw [encard_maximalSeparatedSet hpack]; exact hpack)
  refine ⟨hSfin.toFinset, by simpa using maximalSeparatedSet_subset, ?_, ?_⟩
  · refine ((isCover_maximalSeparatedSet hpack).subset_iUnion_closedBall).trans ?_
    refine Set.iUnion₂_subset fun c hc => ?_
    refine (closedBall_subset_ball ?_).trans (Set.subset_biUnion_of_mem (u := fun c => ball c r) ?_)
    · simp only [NNReal.coe_mul, NNReal.coe_ofNat, hδ]; linarith
    · simpa using hc
  · have hsep := isSeparated_maximalSeparatedSet (ε := 2 * δ) (A := A)
    have hdisj : (↑hSfin.toFinset : Set (Fin n → ℂ)).PairwiseDisjoint (fun c => ball c (r / 4)) := by
      intro x hx y hy hxy
      apply ball_disjoint_ball
      have h1 : ((2 * δ : NNReal) : ENNReal) < edist x y := hsep (by simpa using hx) (by simpa using hy) hxy
      rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)] at h1
      simp only [NNReal.coe_mul, NNReal.coe_ofNat, hδ] at h1
      linarith
    have hsub : (⋃ c ∈ hSfin.toFinset, ball c (r / 4)) ⊆ thickening r A := by
      refine Set.iUnion₂_subset fun c hc => ?_
      exact (ball_subset_thickening (maximalSeparatedSet_subset (by simpa using hc)) _).trans
        (thickening_mono (by linarith) A)
    have hvol := measure_mono (μ := volume) hsub
    rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)] at hvol
    simp only [volume_ball_pi_complex _ (by positivity : (0 : ℝ) < r / 4), Finset.sum_const,
      nsmul_eq_mul] at hvol
    have hfin : volume (thickening r A) ≠ ⊤ := (hA.isBounded.thickening).measure_lt_top.ne
    have := ENNReal.toReal_mono hfin hvol
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)] at this

/- English proof (translation)
Introduce `n d I K hdim hK`. Take `⟨C, hC0, hC⟩` from `h n d I K hdim hK`. Use `⟨C * (16 / Real.pi) ^ n, by positivity, fun r hr => ?_⟩` and prove the remaining obligations. Establish `hr0` using `hr.1`. Establish `hZ : IsClosed (zeroSet I)`.

Establish `: zeroSet I = ⋂ q ∈ I, {x : Fin n → ℂ | eval x q = 0}` using `by ext x; simp [zeroSet]`. Rewrite using `[this]`. Conclude with `isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const`. Establish `hA : IsCompact (zeroSet I ∩ K)` using `hK.inter_left hZ`. Take `⟨T, hTA, hcov, hcount⟩` from `exists_cover_le_volume_thickening hA hr0`.

Use `⟨T, hTA, hcov, ?_⟩` and prove the remaining obligations. Establish `hV` using `ENNReal.toReal_le_of_le_ofReal (by positivity) (hC r hr)`. Establish `hz : r ^ ((2 * n + 2 : ℤ) - 2 * d) * r ^ (2 * d) = r ^ (2 * n) * r ^ 2`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hr0.ne', ← zpow_add₀ hr0.ne']`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hP : 0 < (Real.pi / 16) ^ n * r ^ (2 * n)` using `by positivity`. Establish `he : (16 / Real.pi) ^ n * (Real.pi / 16) ^ n = 1`. Rewrite using `[← mul_pow, div_mul_div_comm, mul_comm 16, div_self (by positivity), one_pow]`.

Establish `hball : (Real.pi * (r / 4) ^ 2) ^ n = (Real.pi / 16) ^ n * r ^ (2 * n)`. Rewrite using `[pow_mul, ← mul_pow]`. Put the polynomial expressions in normal form. Use `le_of_mul_le_mul_right ?_ hP` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_assoc, hz]`. Take the linear combination `(-(C * r ^ (2 * n) * r ^ 2)) * he`.
-/
theorem SmallSetBallCover.proof (h : SmallSetTubeVolume.Statement) : SmallSetBallCover.Statement := by
  intro n d I K hdim hK
  obtain ⟨C, hC0, hC⟩ := h n d I K hdim hK
  refine ⟨C * (16 / Real.pi) ^ n, by positivity, fun r hr => ?_⟩
  have hr0 := hr.1
  have hZ : IsClosed (zeroSet I) := by
    have : zeroSet I = ⋂ q ∈ I, {x : Fin n → ℂ | eval x q = 0} := by ext x; simp [zeroSet]
    rw [this]
    exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
  have hA : IsCompact (zeroSet I ∩ K) := hK.inter_left hZ
  obtain ⟨T, hTA, hcov, hcount⟩ := exists_cover_le_volume_thickening hA hr0
  refine ⟨T, hTA, hcov, ?_⟩
  have hV := ENNReal.toReal_le_of_le_ofReal (by positivity) (hC r hr)
  have hz : r ^ ((2 * n + 2 : ℤ) - 2 * d) * r ^ (2 * d) = r ^ (2 * n) * r ^ 2 := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hr0.ne', ← zpow_add₀ hr0.ne']
    congr 1; push_cast; ring
  have hP : 0 < (Real.pi / 16) ^ n * r ^ (2 * n) := by positivity
  have he : (16 / Real.pi) ^ n * (Real.pi / 16) ^ n = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm 16, div_self (by positivity), one_pow]
  have hball : (Real.pi * (r / 4) ^ 2) ^ n = (Real.pi / 16) ^ n * r ^ (2 * n) := by
    rw [pow_mul, ← mul_pow]; ring_nf
  refine le_of_mul_le_mul_right ?_ hP
  calc (T.card : ℝ) * r ^ (2 * d) * ((Real.pi / 16) ^ n * r ^ (2 * n))
      = ((T.card : ℝ) * (Real.pi * (r / 4) ^ 2) ^ n) * r ^ (2 * d) := by rw [hball]; ring
    _ ≤ (C * r ^ ((2 * n + 2 : ℤ) - 2 * d)) * r ^ (2 * d) := mul_le_mul_of_nonneg_right (hcount.trans hV) (by positivity)
    _ = C * (16 / Real.pi) ^ n * r ^ 2 * ((Real.pi / 16) ^ n * r ^ (2 * n)) := by
      rw [mul_assoc, hz]
      linear_combination (-(C * r ^ (2 * n) * r ^ 2)) * he

end

end GroundTheory.Heights₂.Heights
