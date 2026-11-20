import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLintegralSobolevPointwiseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormPowMulLeSqrtWeightedSqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivIteratedFDerivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIteratedFDerivTendstoZeroCocompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableSqPowMulIteratedFDerivSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzWeightedSobolevOfFinrankZeroStatement

open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ _ _ μ _ k n`. Choose the witnesses or unpack the hypotheses as in `hd | ⟨m, hm⟩ : finrank ℝ E = 0 ∨ ∃ m, finrank ℝ E = m + 1 := by`. Break down `Nat.eq_zero_or_pos (finrank ℝ E) with h | h` into its components or cases. Conclude with `Or.inl h`. Conclude with `Or.inr ⟨finrank ℝ E - 1, by omega⟩`.

Conclude with `GlobalTheory.T.schwartz_weighted_sobolev_bound_of_finrank_eq_zero μ hd k n`. Take `⟨C5, hC5, h5⟩` from `GlobalTheory.T.ofReal_norm_pow_mul_le_lintegral_iteratedFDeriv μ m hm`. Take `⟨C6, hC6, h6⟩` from `GlobalTheory.T.exists_lintegral_norm_pow_mul_le_sqrt_weighted_sq (F := ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => E) (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ)) μ`. Use `⟨max (n + (m + 1)) (k + finrank ℝ E + 1), (C5 * C6).toReal, ENNReal.toReal_nonneg, ?_⟩` and prove the remaining obligations. Introduce `f x`.

Use `set G : E → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ := iteratedFDeriv ℝ n f with hGdef`. Establish `hG : ContDiff ℝ (⊤ : ℕ∞) G` using `(f.smooth ⊤).iteratedFDeriv_right (by first`. Consider the case `(rw [← WithTop.coe_natCast, ← WithTop.coe_add, top_add])`. Consider the case `exact le_of_eq (by simp)`. Consider the case `(norm_cast))`.

Establish `hdec : ∀ j ≤ m, Tendsto (iteratedFDeriv ℝ j G) (cocompact E) (𝓝 0)`. Introduce `j _`. Rewrite using `[tendsto_zero_iff_norm_tendsto_zero]`. Use `tendsto_zero_iff_norm_tendsto_zero.1 (GlobalTheory.T.schwartz_iteratedFDeriv_tendsto_zero_cocompact' f (n + j))` as an intermediate fact. Simplify `this` using `[G, GlobalTheory.T.norm_iteratedFDeriv_iteratedFDeriv']`.

Establish `hcont : Continuous (iteratedFDeriv ℝ (m + 1) G)` using `hG.continuous_iteratedFDeriv (by exact_mod_cast le_top)`. Establish `hn : ∀ z, ‖iteratedFDeriv ℝ (m + 1) G z‖ = ‖iteratedFDeriv ℝ (n + (m + 1)) f z‖` using `fun z => GlobalTheory.T.norm_iteratedFDeriv_iteratedFDeriv' _ _ _ z`. Establish `e1` using `h5 G hG hdec k x`. Establish `e2` using `h6 _ hcont k`. Simplify using `only [hn] at e1 e2`.

Use `set a := ∫ z, (‖z‖ ^ k * ‖iteratedFDeriv ℝ (n + (m + 1)) f z‖) ^ 2 ∂μ`. Use `set b := ∫ z, (‖z‖ ^ (k + finrank ℝ E + 1) * ‖iteratedFDeriv ℝ (n + (m + 1)) f z‖) ^ 2 ∂μ`. Establish `ha : ∫⁻ z, ENNReal.ofReal ((‖z‖ ^ k * ‖iteratedFDeriv ℝ (n + (m + 1)) f z‖) ^ 2) ∂μ = ENNReal.ofReal a` using `(ofReal_integral_eq_lintegral_ofReal (GlobalTheory.T.integrable_sq_norm_pow_mul_iteratedFDeriv_schwartz μ f _ _) (Eventually.of_forall fun z => sq_nonneg _)).symm`. Establish `hb : ∫⁻ z, ENNReal.ofReal ((‖z‖ ^ (k + finrank ℝ E + 1) * ‖iteratedFDeriv ℝ (n + (m + 1)) f z‖) ^ 2) ∂μ = ENNReal.ofReal b` using `(ofReal_integral_eq_lintegral_ofReal (GlobalTheory.T.integrable_sq_norm_pow_mul_iteratedFDeriv_schwartz μ f _ _) (Eventually.of_forall fun z => sq_nonneg _)).symm`. Establish `ha0 : 0 ≤ a` using `integral_nonneg fun z => sq_nonneg _`.

Establish `hb0 : 0 ≤ b` using `integral_nonneg fun z => sq_nonneg _`. Rewrite `e2` using `[ha, hb, ← ENNReal.ofReal_add ha0 hb0, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]`. Establish `e3 : ENNReal.ofReal (‖x‖ ^ k * ‖G x‖) ≤ C5 * C6 * ENNReal.ofReal ((a + b) ^ (1 / 2 : ℝ))`. Combine the equalities or inequalities in the displayed calculation. Establish `e4` using `ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top hC5 hC6) ENNReal.ofReal_ne_top) e3`.

Rewrite `e4` using `[ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ← Real.sqrt_eq_rpow]`. Use `e4.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) ENNReal.toReal_nonneg)` and prove the remaining obligations. Use `set T : ℕ → ℕ → ℝ := fun i j => ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ`. Establish `hT : ∀ i j, 0 ≤ T i j` using `fun i j => integral_nonneg fun z => sq_nonneg _`. Use `set N := max (n + (m + 1)) (k + finrank ℝ E + 1)`.

Establish `hj : n + (m + 1) ∈ Finset.range (N + 1)` using `Finset.mem_range.2 (by omega)`. Establish `hrow : ∀ i, T i (n + (m + 1)) ≤ ∑ j ∈ Finset.range (N + 1), T i j` using `fun i => Finset.single_le_sum (fun j _ => hT i j) hj`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem schwartz_pow_mul_iteratedFDeriv_le_sqrt_sum_weighted_sq :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure] (k n : ℕ), ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (f : SchwartzMap E ℂ) (x : E), ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤
        C * Real.sqrt (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
          ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ) := by
  intro E _ _ _ _ _ μ _ k n
  obtain hd | ⟨m, hm⟩ : finrank ℝ E = 0 ∨ ∃ m, finrank ℝ E = m + 1 := by
    rcases Nat.eq_zero_or_pos (finrank ℝ E) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨finrank ℝ E - 1, by omega⟩
  · exact GlobalTheory.T.schwartz_weighted_sobolev_bound_of_finrank_eq_zero μ hd k n
  obtain ⟨C5, hC5, h5⟩ := GlobalTheory.T.ofReal_norm_pow_mul_le_lintegral_iteratedFDeriv μ m hm
  obtain ⟨C6, hC6, h6⟩ := GlobalTheory.T.exists_lintegral_norm_pow_mul_le_sqrt_weighted_sq (F := ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => E) (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ)) μ
  refine ⟨max (n + (m + 1)) (k + finrank ℝ E + 1), (C5 * C6).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro f x
  set G : E → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ := iteratedFDeriv ℝ n f with hGdef
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := (f.smooth ⊤).iteratedFDeriv_right (by
    first
    | (rw [← WithTop.coe_natCast, ← WithTop.coe_add, top_add])
    | exact le_of_eq (by simp)
    | (norm_cast))
  have hdec : ∀ j ≤ m, Tendsto (iteratedFDeriv ℝ j G) (cocompact E) (𝓝 0) := by
    intro j _
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := tendsto_zero_iff_norm_tendsto_zero.1 (GlobalTheory.T.schwartz_iteratedFDeriv_tendsto_zero_cocompact' f (n + j))
    simpa [G, GlobalTheory.T.norm_iteratedFDeriv_iteratedFDeriv'] using this
  have hcont : Continuous (iteratedFDeriv ℝ (m + 1) G) :=
    hG.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hn : ∀ z, ‖iteratedFDeriv ℝ (m + 1) G z‖ = ‖iteratedFDeriv ℝ (n + (m + 1)) f z‖ :=
    fun z => GlobalTheory.T.norm_iteratedFDeriv_iteratedFDeriv' _ _ _ z
  have e1 := h5 G hG hdec k x
  have e2 := h6 _ hcont k
  simp only [hn] at e1 e2
  set a := ∫ z, (‖z‖ ^ k * ‖iteratedFDeriv ℝ (n + (m + 1)) f z‖) ^ 2 ∂μ
  set b := ∫ z, (‖z‖ ^ (k + finrank ℝ E + 1) * ‖iteratedFDeriv ℝ (n + (m + 1)) f z‖) ^ 2 ∂μ
  have ha : ∫⁻ z, ENNReal.ofReal ((‖z‖ ^ k * ‖iteratedFDeriv ℝ (n + (m + 1)) f z‖) ^ 2) ∂μ
      = ENNReal.ofReal a :=
    (ofReal_integral_eq_lintegral_ofReal (GlobalTheory.T.integrable_sq_norm_pow_mul_iteratedFDeriv_schwartz μ f _ _) (Eventually.of_forall fun z => sq_nonneg _)).symm
  have hb : ∫⁻ z, ENNReal.ofReal ((‖z‖ ^ (k + finrank ℝ E + 1) * ‖iteratedFDeriv ℝ (n + (m + 1)) f z‖) ^ 2) ∂μ
      = ENNReal.ofReal b :=
    (ofReal_integral_eq_lintegral_ofReal (GlobalTheory.T.integrable_sq_norm_pow_mul_iteratedFDeriv_schwartz μ f _ _) (Eventually.of_forall fun z => sq_nonneg _)).symm
  have ha0 : 0 ≤ a := integral_nonneg fun z => sq_nonneg _
  have hb0 : 0 ≤ b := integral_nonneg fun z => sq_nonneg _
  rw [ha, hb, ← ENNReal.ofReal_add ha0 hb0, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)] at e2
  have e3 : ENNReal.ofReal (‖x‖ ^ k * ‖G x‖) ≤ C5 * C6 * ENNReal.ofReal ((a + b) ^ (1 / 2 : ℝ)) := by
    calc _ ≤ _ := e1
      _ ≤ C5 * (C6 * ENNReal.ofReal ((a + b) ^ (1 / 2 : ℝ))) := by gcongr
      _ = _ := (mul_assoc _ _ _).symm
  have e4 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top hC5 hC6) ENNReal.ofReal_ne_top) e3
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ← Real.sqrt_eq_rpow] at e4
  refine e4.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) ENNReal.toReal_nonneg)

  set T : ℕ → ℕ → ℝ := fun i j => ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ
  have hT : ∀ i j, 0 ≤ T i j := fun i j => integral_nonneg fun z => sq_nonneg _
  set N := max (n + (m + 1)) (k + finrank ℝ E + 1)
  have hj : n + (m + 1) ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
  have hrow : ∀ i, T i (n + (m + 1)) ≤ ∑ j ∈ Finset.range (N + 1), T i j := fun i =>
    Finset.single_le_sum (fun j _ => hT i j) hj
  calc a + b = T k (n + (m + 1)) + T (k + finrank ℝ E + 1) (n + (m + 1)) := rfl
    _ ≤ (∑ j ∈ Finset.range (N + 1), T k j) + ∑ j ∈ Finset.range (N + 1), T (k + finrank ℝ E + 1) j :=
        add_le_add (hrow _) (hrow _)
    _ ≤ ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), T i j :=
        Finset.add_le_sum (fun i _ => Finset.sum_nonneg fun j _ => hT i j)
          (Finset.mem_range.2 (by omega)) (Finset.mem_range.2 (by omega)) (by omega)

end GlobalTheory
