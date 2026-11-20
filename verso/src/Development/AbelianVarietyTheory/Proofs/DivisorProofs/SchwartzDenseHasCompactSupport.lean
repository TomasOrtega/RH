import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBounded

open Filter Topology
open scoped ContDiff

namespace GlobalTheory

/- English proof (translation)
Introduce `V _ _ _`. Take `⟨χ, -, hχc, hχs, -, hχ0⟩` from `exists_contDiff_tsupport_subset (n := ⊤) (Filter.univ_mem (f := 𝓝 (0 : V)))`. Use `set L : ℝ → V →L[ℝ] V := fun r => r • ContinuousLinearMap.id ℝ V with hL`. Establish `hLx : ∀ r x, L r x = r • x` using `fun r x => by simp [hL]`. Establish `hLn : ∀ r, ‖L r‖ ≤ |r|` using `fun r => by`.

Use `(norm_smul_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs]`. Conclude with `mul_le_of_le_one_right (abs_nonneg r) ContinuousLinearMap.norm_id_le`. Use `set g : ℝ → V → ℂ := fun r => Complex.ofRealLI ∘ (χ ∘ L r) with hg`. Establish `hgx : ∀ r x, g r x = ((χ (r • x) : ℝ) : ℂ)` using `fun r x => by simp [hg, hLx]`.

Establish `hχL : ∀ r, ContDiff ℝ ∞ (χ ∘ L r)` using `fun r => hχs.comp (L r).contDiff`. Establish `hgs : ∀ r, ContDiff ℝ ∞ (g r)` using `fun r => Complex.ofRealLI.contDiff.comp (hχL r)`. Establish `hM : ∀ i : ℕ, ∃ M, ∀ y, ‖iteratedFDeriv ℝ i χ y‖ ≤ M` using `fun i => (hχs.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support (hχc.iteratedFDeriv i)`. Use `choose M hM using hM`. Establish `hgb : ∀ i : ℕ, ∀ r x, ‖iteratedFDeriv ℝ i (g r) x‖ ≤ M i * ‖L r‖ ^ i`.

Introduce `i r x`. Rewrite using `[hg, Complex.ofRealLI.norm_iteratedFDeriv_comp_left (hχL r).contDiffAt (mod_cast le_top), ContinuousLinearMap.iteratedFDeriv_comp_right (L r) hχs x (mod_cast le_top)]`. Use `(ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Conclude with `mul_le_mul_of_nonneg_right (hM i _) (by positivity)`.

Establish `htg : ∀ r, (g r).HasTemperateGrowth` using `fun r => ⟨hgs r, fun n => ⟨0, M n * ‖L r‖ ^ n, fun x => by simpa using hgb n r x⟩⟩`. Introduce `f`. Use `set F : ℝ → SchwartzMap V ℂ := fun r => SchwartzMap.smulLeftCLM ℂ (g r) f with hF`. Establish `hFx : ∀ r, (F r : V → ℂ) = fun y => g r y * f y` using `fun r => by`. Use extensionality with `y`.

Simplify using `[hF, SchwartzMap.smulLeftCLM_apply_apply (htg r)]`. Establish `hF0 : F 0 = f`. Use extensionality with `y`. Rewrite using `[hFx]`. Simplify using `[hgx, hχ0]`.

Establish `hcont : ContinuousAt F 0`. Use `schwartz_continuousAt_of_pointwise_of_bounded F 0 (fun v => ?_) (fun k n => ?_)` and prove the remaining obligations. Simplify using `only [hFx, hgx]`. Conclude with `((Complex.continuous_ofReal.comp (hχs.continuous.comp (continuous_id.smul continuous_const))).mul continuous_const).continuousAt`. Use `⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |M i| * SchwartzMap.seminorm ℂ k (n - i) f, ?_⟩ filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with r hr v` and prove the remaining obligations.

Establish `hr1 : |r| ≤ 1` using `by simpa [Real.dist_0_eq_abs] using hr`. Rewrite using `[hFx]`. Use `(mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le (N := ∞) (hgs r) (f.smooth ⊤) v (mod_cast le_top)) (by positivity)).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations.

Establish `h1 : ‖iteratedFDeriv ℝ i (g r) v‖ ≤ |M i|`. Use `(hgb i r v).trans ?_` and prove the remaining obligations. Use `(mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans ?_` and prove the remaining obligations. Conclude with `mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (norm_nonneg _) ((hLn r).trans hr1))`. Establish `h2` using `SchwartzMap.le_seminorm ℂ k (n - i) f v`.

Combine the equalities or inequalities in the displayed calculation. Establish `ht : Tendsto F (𝓝[≠] 0) (𝓝 f)`. Rewrite using `[← hF0]`. Conclude with `hcont.tendsto.mono_left nhdsWithin_le_nhds`. Use `mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun r hr => ?_)` and prove the remaining obligations.

Establish `hr0 : r ≠ 0` using `hr`. Use `show HasCompactSupport (F r : V → ℂ)`. Rewrite using `[hFx]`. Establish `hgc : HasCompactSupport (g r)`. Establish `: g r = fun x => ((χ (r • x) : ℝ) : ℂ)` using `funext (hgx r)`.

Rewrite using `[this]`. Conclude with `(hχc.comp_smul hr0).comp_left Complex.ofReal_zero`. Conclude with `hgc.mul_right`.
-/
theorem schwartz_dense_hasCompactSupport :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    Dense {f : SchwartzMap V ℂ | HasCompactSupport (f : V → ℂ)} := by
  intro V _ _ _
  obtain ⟨χ, -, hχc, hχs, -, hχ0⟩ := exists_contDiff_tsupport_subset (n := ⊤) (Filter.univ_mem (f := 𝓝 (0 : V)))
  set L : ℝ → V →L[ℝ] V := fun r => r • ContinuousLinearMap.id ℝ V with hL
  have hLx : ∀ r x, L r x = r • x := fun r x => by simp [hL]
  have hLn : ∀ r, ‖L r‖ ≤ |r| := fun r => by
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg r) ContinuousLinearMap.norm_id_le
  set g : ℝ → V → ℂ := fun r => Complex.ofRealLI ∘ (χ ∘ L r) with hg
  have hgx : ∀ r x, g r x = ((χ (r • x) : ℝ) : ℂ) := fun r x => by simp [hg, hLx]
  have hχL : ∀ r, ContDiff ℝ ∞ (χ ∘ L r) := fun r => hχs.comp (L r).contDiff
  have hgs : ∀ r, ContDiff ℝ ∞ (g r) := fun r => Complex.ofRealLI.contDiff.comp (hχL r)
  have hM : ∀ i : ℕ, ∃ M, ∀ y, ‖iteratedFDeriv ℝ i χ y‖ ≤ M := fun i =>
    (hχs.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (hχc.iteratedFDeriv i)
  choose M hM using hM
  have hgb : ∀ i : ℕ, ∀ r x, ‖iteratedFDeriv ℝ i (g r) x‖ ≤ M i * ‖L r‖ ^ i := by
    intro i r x
    rw [hg, Complex.ofRealLI.norm_iteratedFDeriv_comp_left (hχL r).contDiffAt (mod_cast le_top),
      ContinuousLinearMap.iteratedFDeriv_comp_right (L r) hχs x (mod_cast le_top)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul_of_nonneg_right (hM i _) (by positivity)
  have htg : ∀ r, (g r).HasTemperateGrowth := fun r =>
    ⟨hgs r, fun n => ⟨0, M n * ‖L r‖ ^ n, fun x => by simpa using hgb n r x⟩⟩
  intro f
  set F : ℝ → SchwartzMap V ℂ := fun r => SchwartzMap.smulLeftCLM ℂ (g r) f with hF
  have hFx : ∀ r, (F r : V → ℂ) = fun y => g r y * f y := fun r => by
    ext y; simp [hF, SchwartzMap.smulLeftCLM_apply_apply (htg r)]
  have hF0 : F 0 = f := by
    ext y; rw [hFx]; simp [hgx, hχ0]
  have hcont : ContinuousAt F 0 := by
    refine schwartz_continuousAt_of_pointwise_of_bounded F 0 (fun v => ?_) (fun k n => ?_)
    · simp only [hFx, hgx]
      exact ((Complex.continuous_ofReal.comp (hχs.continuous.comp
        (continuous_id.smul continuous_const))).mul continuous_const).continuousAt
    · refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |M i| * SchwartzMap.seminorm ℂ k (n - i) f, ?_⟩
      filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with r hr v
      have hr1 : |r| ≤ 1 := by simpa [Real.dist_0_eq_abs] using hr
      rw [hFx]
      refine (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le (N := ∞) (hgs r) (f.smooth ⊤) v
        (mod_cast le_top)) (by positivity)).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 : ‖iteratedFDeriv ℝ i (g r) v‖ ≤ |M i| := by
        refine (hgb i r v).trans ?_
        refine (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans ?_
        exact mul_le_of_le_one_right (abs_nonneg _)
          (pow_le_one₀ (norm_nonneg _) ((hLn r).trans hr1))
      have h2 := SchwartzMap.le_seminorm ℂ k (n - i) f v
      calc ‖v‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (g r) v‖ * ‖iteratedFDeriv ℝ (n - i) (⇑f) v‖)
          = (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (g r) v‖ * (‖v‖ ^ k * ‖iteratedFDeriv ℝ (n - i) (⇑f) v‖) := by ring
        _ ≤ (n.choose i : ℝ) * |M i| * SchwartzMap.seminorm ℂ k (n - i) f :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (by positivity) (by positivity)
  have ht : Tendsto F (𝓝[≠] 0) (𝓝 f) := by
    rw [← hF0]; exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun r hr => ?_)
  have hr0 : r ≠ 0 := hr
  show HasCompactSupport (F r : V → ℂ)
  rw [hFx]
  have hgc : HasCompactSupport (g r) := by
    have : g r = fun x => ((χ (r • x) : ℝ) : ℂ) := funext (hgx r)
    rw [this]
    exact (hχc.comp_smul hr0).comp_left Complex.ofReal_zero
  exact hgc.mul_right

end GlobalTheory
