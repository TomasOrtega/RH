import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Metric Module

noncomputable section

/- English proof (translation)
Set `_ : MeasurableSpace W` to `borel W`. Establish `: BorelSpace W` using `⟨rfl⟩`. Use `set μ : Measure W := (Module.finBasis ℝ W).addHaar with hμ`. Establish `hl2 : 0 < lam / 2` using `half_pos hlam`. Establish `hdisj : Set.PairwiseDisjoint (s : Set W) fun w => ball w (lam / 2)`.

Introduce `w hw w' hw' hne`. Apply `ball_disjoint_ball` to reduce the goal to its premises. Rewrite using `[add_halves, dist_eq_norm]`. Conclude with `hsep w hw w' hw' hne`. Establish `hsubset : (⋃ w ∈ s, ball w (lam / 2)) ⊆ ball (0 : W) (r + lam / 2)`.

Introduce `x hx`. Simplify using `only [Set.mem_iUnion] at hx`. Take `⟨w, hw, hxw⟩` from `hx`. Rewrite using `[mem_ball_zero_iff]`. Rewrite `hxw` using `[mem_ball, dist_eq_norm]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hmeas` using `measure_biUnion_finset (μ := μ) hdisj fun w _ => measurableSet_ball`. Establish `hle` using `measure_mono (μ := μ) hsubset`. Rewrite `hle` using `[hmeas]`. Simplify using `only [Measure.addHaar_ball_of_pos μ _ hl2, Finset.sum_const, nsmul_eq_mul] at hle`.

Rewrite `hle` using `[Measure.addHaar_ball_of_pos μ _ (by linarith : 0 < r + lam / 2)]`. Establish `hc0 : μ (ball 0 1) ≠ 0` using `(measure_ball_pos μ 0 one_pos).ne'`. Establish `hct : μ (ball 0 1) ≠ ⊤` using `measure_ball_lt_top.ne`. Rewrite `hle` using `[← mul_assoc]`. Establish `hle'` using `(ENNReal.mul_le_mul_iff_left hc0 hct).1 hle`.

Rewrite `hle'` using `[show ((s.card : ℕ) : ENNReal) = ENNReal.ofReal (s.card : ℝ) by simp, ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (pow_nonneg (by linarith) _)]`. Establish `hpos : 0 < (lam / 2) ^ finrank ℝ W` using `by positivity`. Establish `key : (1 + 2 * r / lam) ^ finrank ℝ W = ((r + lam / 2) / (lam / 2)) ^ finrank ℝ W`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, div_pow, le_div_iff₀ hpos]`. Conclude with `hle'`.
-/
theorem card_le_of_separated_of_norm_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (s : Finset W) {lam r : ℝ} (hlam : 0 < lam) (hr : 0 ≤ r)
    (hs : ∀ x ∈ s, ‖x‖ ≤ r) (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → lam ≤ ‖x - y‖) :
    (s.card : ℝ) ≤ (1 + 2 * r / lam) ^ finrank ℝ W := by
  classical
  let _ : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  set μ : Measure W := (Module.finBasis ℝ W).addHaar with hμ
  have hl2 : 0 < lam / 2 := half_pos hlam
  have hdisj : Set.PairwiseDisjoint (s : Set W) fun w => ball w (lam / 2) := by
    intro w hw w' hw' hne
    apply ball_disjoint_ball
    rw [add_halves, dist_eq_norm]
    exact hsep w hw w' hw' hne
  have hsubset : (⋃ w ∈ s, ball w (lam / 2)) ⊆ ball (0 : W) (r + lam / 2) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨w, hw, hxw⟩ := hx
    rw [mem_ball_zero_iff]
    rw [mem_ball, dist_eq_norm] at hxw
    calc ‖x‖ = ‖w + (x - w)‖ := by rw [add_sub_cancel]
      _ ≤ ‖w‖ + ‖x - w‖ := norm_add_le _ _
      _ < r + lam / 2 := by linarith [hs w hw]
  have hmeas := measure_biUnion_finset (μ := μ) hdisj fun w _ => measurableSet_ball
  have hle := measure_mono (μ := μ) hsubset
  rw [hmeas] at hle
  simp only [Measure.addHaar_ball_of_pos μ _ hl2, Finset.sum_const, nsmul_eq_mul] at hle
  rw [Measure.addHaar_ball_of_pos μ _ (by linarith : 0 < r + lam / 2)] at hle
  have hc0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hct : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [← mul_assoc] at hle
  have hle' := (ENNReal.mul_le_mul_iff_left hc0 hct).1 hle
  rw [show ((s.card : ℕ) : ENNReal) = ENNReal.ofReal (s.card : ℝ) by simp,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (pow_nonneg (by linarith) _)] at hle'
  have hpos : 0 < (lam / 2) ^ finrank ℝ W := by positivity
  have key : (1 + 2 * r / lam) ^ finrank ℝ W = ((r + lam / 2) / (lam / 2)) ^ finrank ℝ W := by
    congr 1
    field_simp
    ring
  rw [key, div_pow, le_div_iff₀ hpos]
  exact hle'

/- English proof (translation)
Establish `: IsAddTorsionFree V` using `IsAddTorsionFree.of_isTorsionFree ℝ V`. Establish `: Module.IsTorsionFree ℤ La` using `inferInstance`. Establish `: Module.Free ℤ La` using `Module.free_of_finite_type_torsion_free'`. Set `B` to `Module.Free.chooseBasis ℤ La`. Set `f : Module.Free.ChooseBasisIndex ℤ La → V` to `fun i => (B i : V)`.

Establish `hspan : Submodule.span ℝ (La : Set V) = Submodule.span ℝ (Set.range f)`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Establish `hx'' : x = ∑ i, B.repr ⟨x, hx⟩ i • f i` using `by conv_lhs => rw [show x = ((⟨x, hx⟩ : La) : V) from rfl, ← B.sum_repr ⟨x, hx⟩]`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, f]`. Rewrite using `[SetLike.mem_coe, hx'']`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Int.cast_smul_eq_zsmul ℝ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `Submodule.subset_span (B i).2`. Use `⟨Submodule.subset_span, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hspan]`.

Conclude with `FiniteDimensional.span_of_finite ℝ (Set.finite_range f)`. Rewrite using `[hspan, finrank_eq_card_basis B]`. Conclude with `finrank_range_le_card f`.
-/
theorem finrank_span_le_finrank_int {V : Type*} [AddCommGroup V] [Module ℝ V]
    (La : Submodule ℤ V) [Module.Finite ℤ La] :
    (La : Set V) ⊆ Submodule.span ℝ (La : Set V) ∧
      FiniteDimensional ℝ (Submodule.span ℝ (La : Set V)) ∧
      finrank ℝ (Submodule.span ℝ (La : Set V)) ≤ finrank ℤ La := by
  classical
  have : IsAddTorsionFree V := IsAddTorsionFree.of_isTorsionFree ℝ V
  have : Module.IsTorsionFree ℤ La := inferInstance
  have : Module.Free ℤ La := Module.free_of_finite_type_torsion_free'
  let B := Module.Free.chooseBasis ℤ La
  let f : Module.Free.ChooseBasisIndex ℤ La → V := fun i => (B i : V)
  have hspan : Submodule.span ℝ (La : Set V) = Submodule.span ℝ (Set.range f) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      have hx'' : x = ∑ i, B.repr ⟨x, hx⟩ i • f i := by
        conv_lhs => rw [show x = ((⟨x, hx⟩ : La) : V) from rfl, ← B.sum_repr ⟨x, hx⟩]
        simp only [Submodule.coe_sum, Submodule.coe_smul, f]
      rw [SetLike.mem_coe, hx'']
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℝ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span (B i).2
  refine ⟨Submodule.subset_span, ?_, ?_⟩
  · rw [hspan]; exact FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
  · rw [hspan, finrank_eq_card_basis B]
    exact finrank_range_le_card f

/- English proof (translation)
Introduce `V _ _ La _ S b hb hmem hnorm hsep`. Take `⟨hsub, hfd, hdim⟩` from `finrank_span_le_finrank_int La`. Use `set W := Submodule.span ℝ (La : Set V) with hW`. Establish `hR0 : (0 : ℝ) ≤ Module.finrank ℤ La * (b + Real.log 3)`. Establish `: 0 ≤ Real.log 3` using `Real.log_nonneg (by norm_num)`.

Check the signs of the components of the expression. Break down `Nat.eq_zero_or_pos S.card with h0 | hpos` into its components or cases. Rewrite using `[h0, Nat.cast_zero, Real.log_zero]`. Conclude with `hR0`. Set `T : Finset W` to `S.subtype (· ∈ W)`.

Establish `hTcard : T.card = S.card`. Rewrite using `[Finset.card_subtype, Finset.filter_true_of_mem]`. Conclude with `fun s hs => hsub (hmem s hs)`. Establish `hδ : 0 < Real.exp (-b)` using `Real.exp_pos _`. Establish `hbound` using `card_le_of_separated_of_norm_le T hδ zero_le_one (fun x hx => by`.

Rewrite `hx` using `[Finset.mem_subtype]`. Rewrite using `[Submodule.coe_norm]`. Conclude with `hnorm _ hx)`. Use the proof step `(fun x hx y hy hxy => by`. Rewrite `hx`, `hy` using `[Finset.mem_subtype]`.

Rewrite using `[Submodule.coe_norm, Submodule.coe_sub]`. Conclude with `hsep _ hx _ hy (fun h => hxy (Subtype.ext h)))`. Rewrite `hbound` using `[hTcard]`. Establish `hq : 1 + 2 * 1 / Real.exp (-b) ≤ 3 * Real.exp b`. Establish `h1 : 1 ≤ Real.exp b` using `Real.one_le_exp hb`.

Rewrite using `[Real.exp_neg, mul_one, div_inv_eq_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : 1 ≤ 3 * Real.exp b`. Establish `h1 : 1 ≤ Real.exp b` using `Real.one_le_exp hb`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hcard : (S.card : ℝ) ≤ (3 * Real.exp b) ^ Module.finrank ℤ La` using `hbound.trans ((pow_le_pow_left₀ (by positivity) hq _).trans (pow_le_pow_right₀ h3 hdim))`. Establish `hSpos : (0 : ℝ) < S.card` using `by exact_mod_cast hpos`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.log_pow, Real.log_mul (by norm_num) (Real.exp_pos b).ne', Real.log_exp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Packing.proof : Packing.Statement := by
  classical
  intro V _ _ La _ S b hb hmem hnorm hsep
  obtain ⟨hsub, hfd, hdim⟩ := finrank_span_le_finrank_int La
  set W := Submodule.span ℝ (La : Set V) with hW
  have hR0 : (0 : ℝ) ≤ Module.finrank ℤ La * (b + Real.log 3) := by
    have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]; exact hR0
  let T : Finset W := S.subtype (· ∈ W)
  have hTcard : T.card = S.card := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem]
    exact fun s hs => hsub (hmem s hs)
  have hδ : 0 < Real.exp (-b) := Real.exp_pos _
  have hbound := card_le_of_separated_of_norm_le T hδ zero_le_one
    (fun x hx => by
      rw [Finset.mem_subtype] at hx
      rw [Submodule.coe_norm]; exact hnorm _ hx)
    (fun x hx y hy hxy => by
      rw [Finset.mem_subtype] at hx hy
      rw [Submodule.coe_norm, Submodule.coe_sub]
      exact hsep _ hx _ hy (fun h => hxy (Subtype.ext h)))
  rw [hTcard] at hbound
  have hq : 1 + 2 * 1 / Real.exp (-b) ≤ 3 * Real.exp b := by
    have h1 : 1 ≤ Real.exp b := Real.one_le_exp hb
    rw [Real.exp_neg, mul_one, div_inv_eq_mul]
    linarith
  have h3 : 1 ≤ 3 * Real.exp b := by
    have h1 : 1 ≤ Real.exp b := Real.one_le_exp hb
    linarith
  have hcard : (S.card : ℝ) ≤ (3 * Real.exp b) ^ Module.finrank ℤ La :=
    hbound.trans ((pow_le_pow_left₀ (by positivity) hq _).trans (pow_le_pow_right₀ h3 hdim))
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hpos
  calc Real.log S.card ≤ Real.log ((3 * Real.exp b) ^ Module.finrank ℤ La) :=
        Real.log_le_log hSpos hcard
    _ = Module.finrank ℤ La * (b + Real.log 3) := by
        rw [Real.log_pow, Real.log_mul (by norm_num) (Real.exp_pos b).ne', Real.log_exp]
        ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
