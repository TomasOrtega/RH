import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MultiplicityDescent.JKFinA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IdThmA

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

/- English proof (translation)
Establish `hint : ∀ (a : C(K, ℂ)) i, Integrable (fun k => a k • F i k) μ` using `fun a i => integrableOn_univ.mp ((a.continuous.smul (hF i)).continuousOn.integrableOn_compact isCompact_univ)`. Use `set U : Set K := ⋂ i, {k | ‖F i k - F i 1‖ < δ / 3}`. Establish `hU : IsOpen U` using `isOpen_iInter_of_finite fun i => isOpen_lt ((hF i).sub continuous_const).norm continuous_const`. Establish `h1U : (1 : K) ∈ U` using `mem_iInter.2 fun i => by simp [hδ]`. Take `⟨f, hf0, hf1, hf01⟩` from `exists_continuous_zero_one_of_isClosed (isClosed_singleton (x := (1 : K))) hU.isClosed_compl (disjoint_singleton_left.2 fun h => h h1U)`.

Use `set b : K → ℝ := fun k => 1 - f k`. Establish `hbc : Continuous b` using `continuous_const.sub f.continuous`. Establish `hb0 : ∀ k, 0 ≤ b k` using `fun k => by simp only [b]; linarith [(hf01 k).2]`. Establish `hb1 : b 1 = 1` using `by simp only [b]; rw [hf0 (mem_singleton 1)]; simp`. Establish `hbU : ∀ k, k ∉ U → b k = 0` using `fun k hk => by simp only [b]; rw [hf1 hk]; simp`.

Establish `hbcs : HasCompactSupport b` using `isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)`. Establish `hcpos : 0 < ∫ k, b k ∂μ` using `hbc.integral_pos_of_hasCompactSupport_nonneg_nonzero hbcs hb0 (by rw [hb1]; exact one_ne_zero)`. Use `set c := ∫ k, b k ∂μ`. Establish `hbint : Integrable b μ` using `integrableOn_univ.mp (hbc.continuousOn.integrableOn_compact isCompact_univ)`. Use `set β : C(K, ℂ) := ⟨fun k => ((b k / c : ℝ) : ℂ), Complex.continuous_ofReal.comp (hbc.div_const c)⟩`.

Establish `hβ : ∀ i, ‖∫ k, β k • F i k ∂μ - F i 1‖ ≤ δ / 3`. Introduce `i`. Establish `hβ1 : ∫ k, β k • F i 1 ∂μ = F i 1`. Rewrite using `[integral_smul_const]`. Establish `: ∫ k, β k ∂μ = 1` using `by show ∫ k, ((b k / c : ℝ) : ℂ) ∂μ = 1`.

Rewrite using `[integral_complex_ofReal, integral_div]`. Rewrite using `[show ∫ k, b k ∂μ = c from rfl, div_self hcpos.ne', Complex.ofReal_one]`. Rewrite using `[this, one_smul]`. Establish `hc : Integrable (fun k => β k • F i 1) μ` using `integrableOn_univ.mp ((β.continuous.smul continuous_const).continuousOn.integrableOn_compact isCompact_univ)`. Rewrite using `[← hβ1, ← integral_sub (hint β i) hc]`.

Combine the equalities or inequalities in the displayed calculation. Use `norm_integral_le_of_norm_le ((hbint.div_const c).mul_const _) (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Rewrite using `[← smul_sub, norm_smul]`. Distinguish the cases in `hk : k ∈ U`. Use `(mem_iInter.1 hk) i` as an intermediate fact.

Simplify using `only [mem_ofPred_eq] at this`. Establish `hn : ‖β k‖ = b k / c` using `by show ‖((b k / c : ℝ) : ℂ)‖ = _`. Rewrite using `[Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hb0 k) hcpos.le)]`. Rewrite using `[hn]`. Conclude with `mul_le_mul_of_nonneg_left this.le (div_nonneg (hb0 k) hcpos.le)`.

Establish `hn : β k = 0` using `by show ((b k / c : ℝ) : ℂ) = 0; rw [hbU k hk]; simp`. Rewrite using `[hn, norm_zero, zero_mul, hbU k hk, zero_div, zero_mul]`. Use `_ = δ / 3 := by`. Rewrite using `[integral_mul_const, integral_div]`. Rewrite using `[show (∫ k, b k ∂μ) = c from rfl, div_self hcpos.ne', one_mul]`.

Take `⟨M, hM⟩` from `isCompact_univ.exists_bound_of_continuousOn (continuous_finsetSum Finset.univ fun i _ => (hF i).norm).continuousOn`. Establish `hMi : ∀ i k, ‖F i k‖ ≤ M` using `fun i k => by`. Use `hM k (mem_univ k)` as an intermediate fact. Rewrite `this` using `[Real.norm_eq_abs]`. Use `le_trans ?_ ((le_abs_self _).trans this)` and prove the remaining obligations.

Conclude with `Finset.single_le_sum (f := fun i => ‖F i k‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)`. Use `set R := |M| * μ.real univ + 1`. Establish `hR : 0 < R` using `by positivity`. Establish `hη : 0 < δ / 3 / R` using `by positivity`. Establish `hmem : β ∈ closure ((Mult1.Down.KF.finAlg K : StarSubalgebra ℂ C(K, ℂ)) : Set C(K, ℂ))`.

Establish `htop` using `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep`. Establish `: β ∈ (Mult1.Down.KF.finAlg K).topologicalClosure` using `by rw [htop]; trivial`. Conclude with `this`. Take `⟨α, hα, hαβ⟩` from `Metric.mem_closure_iff.1 hmem _ hη`. Use `⟨α, hα, fun i => ?_⟩` and prove the remaining obligations.

Establish `hdiff : ‖∫ k, α k • F i k ∂μ - ∫ k, β k • F i k ∂μ‖ ≤ δ / 3 / R * |M| * μ.real univ`. Rewrite using `[← integral_sub (hint α i) (hint β i)]`. Use `norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Rewrite using `[← sub_smul, norm_smul]`. Establish `h1 : ‖α k - β k‖ ≤ δ / 3 / R`.

Use `(β - α).norm_coe_le_norm k` as an intermediate fact. Rewrite `hαβ` using `[dist_eq_norm]`. Rewrite using `[norm_sub_rev]`. Conclude with `this.trans hαβ.le`. Conclude with `mul_le_mul h1 ((hMi i k).trans (le_abs_self M)) (norm_nonneg _) hη.le`.

Establish `hsmall : δ / 3 / R * |M| * μ.real univ < δ / 3`. Rewrite using `[mul_assoc, div_mul_eq_mul_div, div_lt_iff₀ hR]`. Establish `: |M| * μ.real univ < R` using `by simp [R]`. Use polynomial arithmetic with `[measureReal_nonneg (μ := μ) (s := univ), abs_nonneg M]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem approx_id {K : Type} [Group K] [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (hsep : (Mult1.Down.KF.finAlg K).SeparatesPoints) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] (F : ι → K → E) (hF : ∀ i, Continuous (F i)) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ α : C(K, ℂ), Mult1.Down.KF.Fin2 α ∧ ∀ i, ‖∫ k, α k • F i k ∂μ - F i 1‖ < δ := by
  classical
  have hint : ∀ (a : C(K, ℂ)) i, Integrable (fun k => a k • F i k) μ := fun a i =>
    integrableOn_univ.mp ((a.continuous.smul (hF i)).continuousOn.integrableOn_compact isCompact_univ)

  set U : Set K := ⋂ i, {k | ‖F i k - F i 1‖ < δ / 3}
  have hU : IsOpen U := isOpen_iInter_of_finite fun i =>
    isOpen_lt ((hF i).sub continuous_const).norm continuous_const
  have h1U : (1 : K) ∈ U := mem_iInter.2 fun i => by simp [hδ]

  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed (isClosed_singleton (x := (1 : K)))
    hU.isClosed_compl (disjoint_singleton_left.2 fun h => h h1U)
  set b : K → ℝ := fun k => 1 - f k
  have hbc : Continuous b := continuous_const.sub f.continuous
  have hb0 : ∀ k, 0 ≤ b k := fun k => by simp only [b]; linarith [(hf01 k).2]
  have hb1 : b 1 = 1 := by simp only [b]; rw [hf0 (mem_singleton 1)]; simp
  have hbU : ∀ k, k ∉ U → b k = 0 := fun k hk => by simp only [b]; rw [hf1 hk]; simp
  have hbcs : HasCompactSupport b := isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)
  have hcpos : 0 < ∫ k, b k ∂μ :=
    hbc.integral_pos_of_hasCompactSupport_nonneg_nonzero hbcs hb0 (by rw [hb1]; exact one_ne_zero)
  set c := ∫ k, b k ∂μ
  have hbint : Integrable b μ := integrableOn_univ.mp (hbc.continuousOn.integrableOn_compact isCompact_univ)
  set β : C(K, ℂ) := ⟨fun k => ((b k / c : ℝ) : ℂ), Complex.continuous_ofReal.comp (hbc.div_const c)⟩
  have hβ : ∀ i, ‖∫ k, β k • F i k ∂μ - F i 1‖ ≤ δ / 3 := by
    intro i
    have hβ1 : ∫ k, β k • F i 1 ∂μ = F i 1 := by
      rw [integral_smul_const]
      have : ∫ k, β k ∂μ = 1 := by
        show ∫ k, ((b k / c : ℝ) : ℂ) ∂μ = 1
        rw [integral_complex_ofReal, integral_div]
        rw [show ∫ k, b k ∂μ = c from rfl, div_self hcpos.ne', Complex.ofReal_one]
      rw [this, one_smul]
    have hc : Integrable (fun k => β k • F i 1) μ :=
      integrableOn_univ.mp ((β.continuous.smul continuous_const).continuousOn.integrableOn_compact isCompact_univ)
    rw [← hβ1, ← integral_sub (hint β i) hc]
    calc ‖∫ k, (β k • F i k - β k • F i 1) ∂μ‖ ≤ ∫ k, b k / c * (δ / 3) ∂μ := by
          refine norm_integral_le_of_norm_le ((hbint.div_const c).mul_const _) (Filter.Eventually.of_forall fun k => ?_)
          rw [← smul_sub, norm_smul]
          by_cases hk : k ∈ U
          · have := (mem_iInter.1 hk) i
            simp only [mem_ofPred_eq] at this
            have hn : ‖β k‖ = b k / c := by
              show ‖((b k / c : ℝ) : ℂ)‖ = _
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hb0 k) hcpos.le)]
            rw [hn]
            exact mul_le_mul_of_nonneg_left this.le (div_nonneg (hb0 k) hcpos.le)
          · have hn : β k = 0 := by show ((b k / c : ℝ) : ℂ) = 0; rw [hbU k hk]; simp
            rw [hn, norm_zero, zero_mul, hbU k hk, zero_div, zero_mul]
      _ = δ / 3 := by
          rw [integral_mul_const, integral_div]
          rw [show (∫ k, b k ∂μ) = c from rfl, div_self hcpos.ne', one_mul]

  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_finsetSum Finset.univ fun i _ => (hF i).norm).continuousOn
  have hMi : ∀ i k, ‖F i k‖ ≤ M := fun i k => by
    have := hM k (mem_univ k)
    rw [Real.norm_eq_abs] at this
    refine le_trans ?_ ((le_abs_self _).trans this)
    exact Finset.single_le_sum (f := fun i => ‖F i k‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  set R := |M| * μ.real univ + 1
  have hR : 0 < R := by positivity
  have hη : 0 < δ / 3 / R := by positivity
  have hmem : β ∈ closure ((Mult1.Down.KF.finAlg K : StarSubalgebra ℂ C(K, ℂ)) : Set C(K, ℂ)) := by
    have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
    have : β ∈ (Mult1.Down.KF.finAlg K).topologicalClosure := by rw [htop]; trivial
    exact this
  obtain ⟨α, hα, hαβ⟩ := Metric.mem_closure_iff.1 hmem _ hη
  refine ⟨α, hα, fun i => ?_⟩
  have hdiff : ‖∫ k, α k • F i k ∂μ - ∫ k, β k • F i k ∂μ‖ ≤ δ / 3 / R * |M| * μ.real univ := by
    rw [← integral_sub (hint α i) (hint β i)]
    refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k => ?_)
    rw [← sub_smul, norm_smul]
    have h1 : ‖α k - β k‖ ≤ δ / 3 / R := by
      have := (β - α).norm_coe_le_norm k
      rw [dist_eq_norm] at hαβ
      rw [norm_sub_rev]
      exact this.trans hαβ.le
    exact mul_le_mul h1 ((hMi i k).trans (le_abs_self M)) (norm_nonneg _) hη.le
  have hsmall : δ / 3 / R * |M| * μ.real univ < δ / 3 := by
    rw [mul_assoc, div_mul_eq_mul_div, div_lt_iff₀ hR]
    have : |M| * μ.real univ < R := by simp [R]
    nlinarith [measureReal_nonneg (μ := μ) (s := univ), abs_nonneg M]
  calc ‖∫ k, α k • F i k ∂μ - F i 1‖
      ≤ ‖∫ k, α k • F i k ∂μ - ∫ k, β k • F i k ∂μ‖ + ‖∫ k, β k • F i k ∂μ - F i 1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < δ / 3 + δ / 3 := add_lt_add_of_lt_of_le (hdiff.trans_lt hsmall) (hβ i)
    _ < δ := by linarith

/- English proof (translation)
Introduce `k k' hne`. Establish `hne' : S7.toMK k ≠ S7.toMK k'` using `fun h => hne (Subtype.ext (Subtype.ext (Units.ext h)))`. Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij⟩ : ∃ i j, S7.toMK k i j ≠ S7.toMK k' i j := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Conclude with `hne' (Matrix.ext hc)`. Establish `hcont : ∀ a b : Fin n, Continuous fun κ : S7.KG ε => S7.toMK κ a b` using `fun a b => (continuous_apply b).comp ((continuous_apply a).comp S7.IdA.continuous_toMK)`. Use `⟨_, ⟨⟨fun κ => S7.toMK κ i j, hcont i j⟩, ?_, rfl⟩, hij⟩` and prove the remaining obligations. Use `⟨Fin n, inferInstance, fun l k₀ => S7.toMK k₀ i l, fun l => ⟨fun κ => S7.toMK κ l j, hcont l j⟩, fun k₀ κ => ?_⟩` and prove the remaining obligations. Use `show (S7.toMK k₀ * S7.toMK κ) i j = _`.

Rewrite using `[Matrix.mul_apply]`. Both sides reduce to the same expression.
-/
theorem finAlg_sep_KG {n : ℕ} (ε : Fin n → Bool) : (Mult1.Down.KF.finAlg (S7.KG ε)).SeparatesPoints := by
  intro k k' hne
  have hne' : S7.toMK k ≠ S7.toMK k' := fun h => hne (Subtype.ext (Subtype.ext (Units.ext h)))
  obtain ⟨i, j, hij⟩ : ∃ i j, S7.toMK k i j ≠ S7.toMK k' i j := by
    by_contra hc
    push Not at hc
    exact hne' (Matrix.ext hc)
  have hcont : ∀ a b : Fin n, Continuous fun κ : S7.KG ε => S7.toMK κ a b := fun a b =>
    (continuous_apply b).comp ((continuous_apply a).comp S7.IdA.continuous_toMK)
  refine ⟨_, ⟨⟨fun κ => S7.toMK κ i j, hcont i j⟩, ?_, rfl⟩, hij⟩
  refine ⟨Fin n, inferInstance, fun l k₀ => S7.toMK k₀ i l, fun l => ⟨fun κ => S7.toMK κ l j, hcont l j⟩,
    fun k₀ κ => ?_⟩
  show (S7.toMK k₀ * S7.toMK κ) i j = _
  rw [Matrix.mul_apply]
  rfl

end ReciprocityTheory.ChartRestriction.DS.DecInf
