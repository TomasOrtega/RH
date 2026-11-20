import Mathlib
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqMulIntegralBallLeOfCircleInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnComplexHessianOfContDiffOnTwoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHessianPosSemidefOfLeviFormNonnegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformTaylorBoundLeviPluriharmonicSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedGaussianIntegralUniformPosSemidefStatement

open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]`. Establish `key : (fun w => (ball (0 : V n) δ).indicator (fun w => F (z + w)) w) = fun w => (ball z δ).indicator F (z + w)`. Use function extensionality and compare the values at `w`. Establish `hiff : w ∈ ball (0 : V n) δ ↔ z + w ∈ ball z δ`. Simplify using `[mem_ball, dist_eq_norm]`.

Distinguish the cases in `hw : w ∈ ball (0 : V n) δ`. Simplify using `[Set.indicator, hw, hiff.1 hw]`. Simplify using `[Set.indicator, hw, (not_congr hiff).1 hw]`. Rewrite using `[key]`. Conclude with `integral_add_left_eq_self (fun w => (ball z δ).indicator F w) z`.
-/
theorem integral_ball_translate {n : ℕ} (z : V n) (δ : ℝ) (F : V n → ℝ) :
    ∫ w in ball (0 : V n) δ, F (z + w) = ∫ w in ball z δ, F w := by
  rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]
  have key : (fun w => (ball (0 : V n) δ).indicator (fun w => F (z + w)) w) =
      fun w => (ball z δ).indicator F (z + w) := by
    funext w
    have hiff : w ∈ ball (0 : V n) δ ↔ z + w ∈ ball z δ := by
      simp [mem_ball, dist_eq_norm]
    by_cases hw : w ∈ ball (0 : V n) δ
    · simp [Set.indicator, hw, hiff.1 hw]
    · simp [Set.indicator, hw, (not_congr hiff).1 hw]
  rw [key]
  exact integral_add_left_eq_self (fun w => (ball z δ).indicator F w) z

/- English proof (translation)
Introduce `n U K φ g ε hU hK hKU hφ hlevi hg hgpos hε`. Establish `hcont : ∀ j l, ContinuousOn (fun z => cHess n (fun v => (φ v : ℂ)) z j l) U` using `GlobalTheory.T.continuousOn_complex_hessian_of_contDiffOn_two n U φ hU hφ`. Choose the witnesses or unpack the hypotheses as in `⟨C, hC⟩ : ∃ C, ∀ z ∈ K, ∀ j l, ‖cHess n (fun v => (φ v : ℂ)) z j l‖ ≤ C := by`. Establish `hc : ContinuousOn (fun z => ∑ j, ∑ l, ‖cHess n (fun v => (φ v : ℂ)) z j l‖) K` using `continuousOn_finset_sum _ fun j _ => continuousOn_finset_sum _ fun l _ => ((hcont j l).mono hKU).norm`. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn hc`.

Use `⟨C, fun z hz j l => ?_⟩` and prove the remaining obligations. Establish `h1` using `hC z hz`. Rewrite `h1` using `[Real.norm_of_nonneg (by positivity)]`. Use `le_trans ?_ h1` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Choose the witnesses or unpack the hypotheses as in `⟨D, hD0, hD⟩ : ∃ D, 0 ≤ D ∧ ∀ z ∈ K, (cHess n (fun v => (φ v : ℂ)) z).det.re / Real.pi ^ n ≤ D := by`. Establish `hHc : ContinuousOn (fun z => cHess n (fun v => (φ v : ℂ)) z) U` using `continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => hcont j l`. Establish `hc : ContinuousOn (fun z => (cHess n (fun v => (φ v : ℂ)) z).det.re / Real.pi ^ n) K` using `((Complex.continuous_re.comp (continuous_id.matrix_det)).comp_continuousOn (hHc.mono hKU)).div_const _`. Take `⟨D, hD⟩` from `hK.exists_bound_of_continuousOn hc`. Conclude with `⟨max D 0, le_max_right _ _, fun z hz => ((le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hD z hz)).trans (le_max_left _ _)⟩`.

Use `set τ : ℝ := ε / (2 * (D + ε)) with hτ`. Establish `hτ0 : 0 < τ` using `by positivity`. Establish `hτ1 : τ < 1`. Rewrite using `[hτ, div_lt_one (by positivity)]; linarith`. Establish `hτd : ∀ d, 0 ≤ d → d ≤ D → d + ε / 2 ≤ (1 - τ) * (d + ε)`.

Introduce `d hd hdD`. Establish `: τ * (d + ε) ≤ ε / 2`. Rewrite using `[hτ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities.

Take `⟨r, hr, hrU⟩` from `hK.exists_cthickening_subset_open hU hKU`. Establish `hS : IsCompact (cthickening r K)` using `hK.cthickening`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc0, hcK⟩ : ∃ c, 0 < c ∧ ∀ z ∈ K, c ≤ g z := by`. Break down `K.eq_empty_or_nonempty with hK0 | hKne` into its components or cases. Conclude with `⟨1, one_pos, by simp [hK0]⟩`.

Take `⟨x, hx, hmin⟩` from `hK.exists_isMinOn hKne (hg.mono hKU)`. Conclude with `⟨g x, hgpos x (hKU hx), fun z hz => hmin hz⟩`. Take `⟨δ₂, hδ₂, huc⟩` from `Metric.uniformContinuousOn_iff.1 (hS.uniformContinuousOn_of_continuous (hg.mono hrU)) (τ * c) (by positivity)`. Use `set δ₃ : ℝ := min r (δ₂ / 2) with hδ₃`. Establish `hδ₃0 : 0 < δ₃` using `by positivity`.

Establish `hgw : ∀ z ∈ K, ∀ w : V n, ‖w‖ ≤ δ₃ → (1 - τ) * g z ≤ g (z + w)`. Introduce `z hz w hw`. Establish `hzS : z ∈ cthickening r K` using `self_subset_cthickening K hz`. Establish `hdist : dist (z + w) z = ‖w‖` using `by simp [dist_eq_norm]`. Establish `hzwS : z + w ∈ cthickening r K` using `mem_cthickening_of_dist_le _ z r K hz (by rw [hdist]; exact hw.trans (min_le_left _ _))`.

Establish `h1` using `huc (z + w) hzwS z hzS (by rw [hdist]; linarith [min_le_right r (δ₂ / 2)])`. Rewrite `h1` using `[Real.dist_eq, abs_lt]`. Use `hcK z hz` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Take `⟨η, hη, htr⟩` from `GlobalTheory.T.truncatedGaussianIntegral_uniform_posSemidef n C (ε / 2) (by positivity)`.

Take `⟨δ₁, hδ₁, hty⟩` from `GlobalTheory.T.uniform_taylor_bound_levi_pluriharmonic_split n U K φ η hU hK hKU hφ hη`. Use `⟨min δ₁ δ₃, lt_min hδ₁ hδ₃0, fun z hz => (closedBall_subset_closedBall (min_le_left _ _)).trans (hty z hz).1, ?_⟩` and prove the remaining obligations. Use `set δ : ℝ := min δ₁ δ₃ with hδ`. Establish `hδ0 : 0 < δ` using `lt_min hδ₁ hδ₃0`. Use `filter_upwards [htr δ hδ0] with m hm`.

Introduce `z hz f hf`. Take `⟨hzU, h, hh, hh0, hbd⟩` from `hty z hz`. Use `set H := cHess n (fun v => (φ v : ℂ)) z with hH`. Establish `hpsd : H.PosSemidef` using `GlobalTheory.T.complexHessian_posSemidef_of_leviForm_nonneg n φ z (hφ.contDiffAt (hU.mem_nhds (hKU hz))) (hlevi z (hKU hz))`. Establish `hT` using `hm H hpsd (hC z hz)`.

Use `set d := H.det.re / Real.pi ^ n with hd`. Establish `hd0 : 0 ≤ d`. Establish `h1` using `hpsd.det_nonneg`. Establish `h2 : 0 ≤ H.det.re` using `(Complex.le_def.1 h1).1`. Check the signs of the components of the expression.

Establish `hdD : d ≤ D` using `hD z hz`. Use `set Wf : V n → ℝ := fun w => Real.exp (-(m * ((∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re + η * ‖w‖ ^ 2))) with hWf`. Use `set F : V n → ℂ := fun w => f (z + w) * Complex.exp (-((m : ℂ) * h w)) with hF`. Use `set U' : Set (V n) := (fun w => z + w) ⁻¹' U with hU'`. Establish `hU'o : IsOpen U'` using `hU.preimage (continuous_const.add continuous_id)`.

Establish `hballU : ∀ w ∈ closedBall (0 : V n) δ, z + w ∈ closedBall z δ`. Introduce `w hw`. Simplify `hw` using `[mem_closedBall, dist_eq_norm]`. Establish `hball' : closedBall (0 : V n) δ ⊆ U'` using `fun w hw => (closedBall_subset_closedBall (min_le_left _ _)).trans hzU (hballU w hw)`. Establish `hFd : DifferentiableOn ℂ F U'`.

Establish `h1 : DifferentiableOn ℂ (fun w => f (z + w)) U'` using `hf.comp ((differentiable_const z).add differentiable_id).differentiableOn (fun w hw => hw)`. Conclude with `h1.mul ((hh.const_mul (m : ℂ)).neg.cexp.differentiableOn)`. Establish `hWc : Continuous Wf`. Simplify using `only [hWf]`. Use `fun_prop`.

Establish `hW0 : ∀ w, 0 ≤ Wf w` using `fun w => (Real.exp_pos _).le`. Establish `hWinv : ∀ (θ : ℂ) (w : V n), ‖θ‖ = 1 → Wf (θ • w) = Wf w`. Introduce `θ w hθ`. Establish `hθ' : θ * (starRingEnd ℂ) θ = 1`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hθ]`.

Simplify using the standard rewrite rules. Establish `hsum : (∑ j, ∑ l, H j l * (θ • w) j * (starRingEnd ℂ) ((θ • w) l)) = ∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `e1 : (θ • w) j = θ * w j` using `by simp`. Establish `e2 : (θ • w) l = θ * w l` using `by simp`.

Rewrite using `[e1, e2, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hWf, hsum, norm_smul, hθ, one_mul]`. Establish `hcirc` using `GlobalTheory.T.norm_sq_mul_integral_ball_le_of_circle_invariant' n δ U' F Wf hδ0 hU'o hball' hFd hWc.continuousOn hW0 hWinv`. Establish `hF0 : F 0 = f z` using `by simp [hF, hh0]`.

Rewrite `hcirc` using `[hF0]`. Establish `hmaps : Set.MapsTo (fun w => z + w) (closedBall (0 : V n) δ) U` using `fun w hw => hball' hw`. Establish `hfc : ContinuousOn (fun w => f (z + w)) (closedBall (0 : V n) δ)` using `hf.continuousOn.comp (continuous_const.add continuous_id).continuousOn hmaps`. Establish `hφc : ContinuousOn (fun w => φ (z + w)) (closedBall (0 : V n) δ)` using `hφ.continuousOn.comp (continuous_const.add continuous_id).continuousOn hmaps`. Establish `hgc : ContinuousOn (fun w => g (z + w)) (closedBall (0 : V n) δ)` using `hg.comp (continuous_const.add continuous_id).continuousOn hmaps`.

Establish `hFc : ContinuousOn F (closedBall (0 : V n) δ)` using `hFd.continuousOn.mono hball'`. Use `set G : V n → ℝ := fun w => ‖f w‖ ^ 2 * Real.exp (-(m * φ w)) * g w with hG`. Establish `hGc : ContinuousOn (fun w => G (z + w)) (closedBall (0 : V n) δ)`. Simplify using `only [hG]`. Conclude with `((hfc.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn ((continuousOn_const.mul hφc).neg))).mul hgc`.

Use `set k : ℝ := Real.exp (-(m * φ z)) * g z * (1 - τ) with hk`. Establish `hk0 : 0 ≤ k`. Use `hgpos z (hKU hz)` as an intermediate fact. Establish `: 0 < 1 - τ` using `by linarith`. Check the signs of the components of the expression.

Establish `hpt : ∀ w ∈ ball (0 : V n) δ, k * (‖F w‖ ^ 2 * Wf w) ≤ G (z + w)`. Introduce `w hw`. Establish `hw' : ‖w‖ < δ` using `by simpa using hw`. Establish `hw1 : w ∈ closedBall (0 : V n) δ₁`. Simplify using `only [mem_closedBall, dist_zero_right]`.

Combine the linear relations using `[min_le_left δ₁ δ₃]`. Establish `hb` using `hbd w hw1`. Establish `hq : (∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re = (leviV n (fun v => (φ v : ℂ)) z fun j => w j).re`. Simplify using `[hH, leviV, cHess]`. Establish `hgzw` using `hgw z hz w (by linarith [min_le_right δ₁ δ₃])`.

Establish `hFn : ‖F w‖ ^ 2 = ‖f (z + w)‖ ^ 2 * Real.exp (-(m * (h w).re)) ^ 2`. Simplify using `[hF, norm_mul, Complex.norm_exp, mul_pow]`. Establish `hE : Real.exp (-(m * φ z)) * (Real.exp (-(m * (h w).re)) ^ 2 * Wf w) ≤ Real.exp (-(m * φ (z + w)))`. Simplify using `only [hWf]`. Rewrite using `[sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]`.

Establish `hm0 : (0 : ℝ) ≤ m` using `Nat.cast_nonneg m`. Use `mul_le_mul_of_nonneg_left hb hm0` as an intermediate fact. Rewrite using `[hq]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hP : 0 ≤ ‖f (z + w)‖ ^ 2` using `by positivity`.

Establish `hgz : 0 ≤ (1 - τ) * g z`. Use `hgpos z (hKU hz); have : 0 < 1 - τ := by linarith` as an intermediate fact. Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hFn, hk]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ g (z + w) * (‖f (z + w)‖ ^ 2 * Real.exp (-(m * φ (z + w)))) := by`. Apply `mul_le_mul hgzw (mul_le_mul_of_nonneg_left hE hP)` to reduce the goal to its premises. Use `hW0 w` as an intermediate fact. Check the signs of the components of the expression.

Conclude with `(hgpos _ (hmaps (ball_subset_closedBall hw))).le`. Use `_ = G (z + w) := by simp only [hG]; ring`. Establish `hint1 : IntegrableOn (fun w => k * (‖F w‖ ^ 2 * Wf w)) (ball (0 : V n) δ)` using `(ContinuousOn.integrableOn_compact (isCompact_closedBall 0 δ) (continuousOn_const.mul ((hFc.norm.pow 2).mul hWc.continuousOn))).mono_set ball_subset_closedBall`. Establish `hint2 : IntegrableOn (fun w => G (z + w)) (ball (0 : V n) δ)` using `(ContinuousOn.integrableOn_compact (isCompact_closedBall 0 δ) hGc).mono_set ball_subset_closedBall`. Establish `hmono` using `setIntegral_mono_on hint1 hint2 measurableSet_ball hpt`.

Rewrite `hmono` using `[integral_const_mul, integral_ball_translate z δ G]`. Use `set J := ∫ w in ball (0 : V n) δ, Wf w with hJ`. Use `set I := ∫ w in ball z δ, G w with hI`. Establish `hJ0 : 0 ≤ J` using `setIntegral_nonneg measurableSet_ball fun w _ => hW0 w`. Use `set A := ‖f z‖ ^ 2 * Real.exp (-(m * φ z)) * g z with hA`.

Establish `hA0 : 0 ≤ A` using `by have := hgpos z (hKU hz); positivity`. Establish `hAJ : (1 - τ) * (A * J) ≤ I`. Establish `h1` using `mul_le_mul_of_nonneg_left hcirc hk0`. Combine the equalities or inequalities in the displayed calculation. Establish `hmn : 0 ≤ (m : ℝ) ^ n` using `by positivity`.

Establish `hkey` using `hτd d hd0 hdD`. Express the relevant statement in the definitionally equal form `A ≤ (d + ε) * (m : ℝ) ^ n * I`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_left _ hA0` to reduce the goal to its premises. Use `mul_nonneg hmn hJ0` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Use `_ = (d + ε) * (m : ℝ) ^ n * ((1 - τ) * (A * J)) := by ring`. Use `_ ≤ (d + ε) * (m : ℝ) ^ n * I := by`. Apply `mul_le_mul_of_nonneg_left hAJ` to reduce the goal to its premises. Establish `: 0 ≤ d + ε` using `by linarith`.

Check the signs of the components of the expression.
-/
theorem morse_local : ∀ (n : ℕ) (U K : Set (V n)) (φ g : V n → ℝ) (ε : ℝ), IsOpen U → IsCompact K →
    K ⊆ U → ContDiffOn ℝ 2 φ U →
    (∀ z ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => (φ v : ℂ)) z ξ).re) → ContinuousOn g U →
    (∀ z ∈ U, 0 < g z) → 0 < ε → ∃ δ : ℝ, 0 < δ ∧ (∀ z ∈ K, closedBall z δ ⊆ U) ∧
    ∀ᶠ m : ℕ in atTop, ∀ z ∈ K, ∀ f : V n → ℂ, DifferentiableOn ℂ f U →
      ‖f z‖ ^ 2 * Real.exp (-(m * φ z)) * g z ≤
        ((cHess n (fun v => (φ v : ℂ)) z).det.re / Real.pi ^ n + ε) * (m : ℝ) ^ n *
          ∫ w in ball z δ, ‖f w‖ ^ 2 * Real.exp (-(m * φ w)) * g w := by
  intro n U K φ g ε hU hK hKU hφ hlevi hg hgpos hε
  have hcont : ∀ j l, ContinuousOn (fun z => cHess n (fun v => (φ v : ℂ)) z j l) U :=
    GlobalTheory.T.continuousOn_complex_hessian_of_contDiffOn_two n U φ hU hφ

  obtain ⟨C, hC⟩ : ∃ C, ∀ z ∈ K, ∀ j l, ‖cHess n (fun v => (φ v : ℂ)) z j l‖ ≤ C := by
    have hc : ContinuousOn (fun z => ∑ j, ∑ l, ‖cHess n (fun v => (φ v : ℂ)) z j l‖) K :=
      continuousOn_finset_sum _ fun j _ => continuousOn_finset_sum _ fun l _ =>
        ((hcont j l).mono hKU).norm
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
    refine ⟨C, fun z hz j l => ?_⟩
    have h1 := hC z hz
    rw [Real.norm_of_nonneg (by positivity)] at h1
    refine le_trans ?_ h1
    calc ‖cHess n (fun v => (φ v : ℂ)) z j l‖
        ≤ ∑ l, ‖cHess n (fun v => (φ v : ℂ)) z j l‖ :=
          Finset.single_le_sum (f := fun l => ‖cHess n (fun v => (φ v : ℂ)) z j l‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ l)
      _ ≤ ∑ j, ∑ l, ‖cHess n (fun v => (φ v : ℂ)) z j l‖ :=
          Finset.single_le_sum (f := fun j => ∑ l, ‖cHess n (fun v => (φ v : ℂ)) z j l‖)
            (fun _ _ => by positivity) (Finset.mem_univ j)

  obtain ⟨D, hD0, hD⟩ : ∃ D, 0 ≤ D ∧
      ∀ z ∈ K, (cHess n (fun v => (φ v : ℂ)) z).det.re / Real.pi ^ n ≤ D := by
    have hHc : ContinuousOn (fun z => cHess n (fun v => (φ v : ℂ)) z) U :=
      continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => hcont j l
    have hc : ContinuousOn (fun z => (cHess n (fun v => (φ v : ℂ)) z).det.re / Real.pi ^ n) K :=
      ((Complex.continuous_re.comp (continuous_id.matrix_det)).comp_continuousOn
        (hHc.mono hKU)).div_const _
    obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hc
    exact ⟨max D 0, le_max_right _ _, fun z hz =>
      ((le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hD z hz)).trans (le_max_left _ _)⟩

  set τ : ℝ := ε / (2 * (D + ε)) with hτ
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ < 1 := by
    rw [hτ, div_lt_one (by positivity)]; linarith
  have hτd : ∀ d, 0 ≤ d → d ≤ D → d + ε / 2 ≤ (1 - τ) * (d + ε) := by
    intro d hd hdD
    have : τ * (d + ε) ≤ ε / 2 := by
      rw [hτ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith

  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hS : IsCompact (cthickening r K) := hK.cthickening
  obtain ⟨c, hc0, hcK⟩ : ∃ c, 0 < c ∧ ∀ z ∈ K, c ≤ g z := by
    rcases K.eq_empty_or_nonempty with hK0 | hKne
    · exact ⟨1, one_pos, by simp [hK0]⟩
    · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hKne (hg.mono hKU)
      exact ⟨g x, hgpos x (hKU hx), fun z hz => hmin hz⟩
  obtain ⟨δ₂, hδ₂, huc⟩ := Metric.uniformContinuousOn_iff.1
    (hS.uniformContinuousOn_of_continuous (hg.mono hrU)) (τ * c) (by positivity)
  set δ₃ : ℝ := min r (δ₂ / 2) with hδ₃
  have hδ₃0 : 0 < δ₃ := by positivity
  have hgw : ∀ z ∈ K, ∀ w : V n, ‖w‖ ≤ δ₃ → (1 - τ) * g z ≤ g (z + w) := by
    intro z hz w hw
    have hzS : z ∈ cthickening r K := self_subset_cthickening K hz
    have hdist : dist (z + w) z = ‖w‖ := by simp [dist_eq_norm]
    have hzwS : z + w ∈ cthickening r K :=
      mem_cthickening_of_dist_le _ z r K hz (by rw [hdist]; exact hw.trans (min_le_left _ _))
    have h1 := huc (z + w) hzwS z hzS (by rw [hdist]; linarith [min_le_right r (δ₂ / 2)])
    rw [Real.dist_eq, abs_lt] at h1
    have := hcK z hz
    nlinarith

  obtain ⟨η, hη, htr⟩ := GlobalTheory.T.truncatedGaussianIntegral_uniform_posSemidef n C (ε / 2) (by positivity)
  obtain ⟨δ₁, hδ₁, hty⟩ := GlobalTheory.T.uniform_taylor_bound_levi_pluriharmonic_split n U K φ η hU hK hKU hφ hη
  refine ⟨min δ₁ δ₃, lt_min hδ₁ hδ₃0, fun z hz =>
    (closedBall_subset_closedBall (min_le_left _ _)).trans (hty z hz).1, ?_⟩
  set δ : ℝ := min δ₁ δ₃ with hδ
  have hδ0 : 0 < δ := lt_min hδ₁ hδ₃0
  filter_upwards [htr δ hδ0] with m hm
  intro z hz f hf
  obtain ⟨hzU, h, hh, hh0, hbd⟩ := hty z hz
  set H := cHess n (fun v => (φ v : ℂ)) z with hH
  have hpsd : H.PosSemidef :=
    GlobalTheory.T.complexHessian_posSemidef_of_leviForm_nonneg n φ z (hφ.contDiffAt (hU.mem_nhds (hKU hz))) (hlevi z (hKU hz))
  have hT := hm H hpsd (hC z hz)
  set d := H.det.re / Real.pi ^ n with hd
  have hd0 : 0 ≤ d := by
    have h1 := hpsd.det_nonneg
    have h2 : 0 ≤ H.det.re := (Complex.le_def.1 h1).1
    positivity
  have hdD : d ≤ D := hD z hz

  set Wf : V n → ℝ := fun w => Real.exp (-(m * ((∑ j, ∑ l, H j l * w j *
    (starRingEnd ℂ) (w l)).re + η * ‖w‖ ^ 2))) with hWf
  set F : V n → ℂ := fun w => f (z + w) * Complex.exp (-((m : ℂ) * h w)) with hF
  set U' : Set (V n) := (fun w => z + w) ⁻¹' U with hU'
  have hU'o : IsOpen U' := hU.preimage (continuous_const.add continuous_id)
  have hballU : ∀ w ∈ closedBall (0 : V n) δ, z + w ∈ closedBall z δ := by
    intro w hw
    simpa [mem_closedBall, dist_eq_norm] using hw
  have hball' : closedBall (0 : V n) δ ⊆ U' := fun w hw =>
    (closedBall_subset_closedBall (min_le_left _ _)).trans hzU (hballU w hw)
  have hFd : DifferentiableOn ℂ F U' := by
    have h1 : DifferentiableOn ℂ (fun w => f (z + w)) U' :=
      hf.comp ((differentiable_const z).add differentiable_id).differentiableOn
        (fun w hw => hw)
    exact h1.mul ((hh.const_mul (m : ℂ)).neg.cexp.differentiableOn)
  have hWc : Continuous Wf := by
    simp only [hWf]; fun_prop
  have hW0 : ∀ w, 0 ≤ Wf w := fun w => (Real.exp_pos _).le
  have hWinv : ∀ (θ : ℂ) (w : V n), ‖θ‖ = 1 → Wf (θ • w) = Wf w := by
    intro θ w hθ
    have hθ' : θ * (starRingEnd ℂ) θ = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hθ]; simp
    have hsum : (∑ j, ∑ l, H j l * (θ • w) j * (starRingEnd ℂ) ((θ • w) l)) =
        ∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l) := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      have e1 : (θ • w) j = θ * w j := by simp
      have e2 : (θ • w) l = θ * w l := by simp
      rw [e1, e2, map_mul]
      calc H j l * (θ * w j) * ((starRingEnd ℂ) θ * (starRingEnd ℂ) (w l))
          = H j l * w j * (starRingEnd ℂ) (w l) * (θ * (starRingEnd ℂ) θ) := by ring
        _ = _ := by rw [hθ', mul_one]
    simp only [hWf, hsum, norm_smul, hθ, one_mul]
  have hcirc := GlobalTheory.T.norm_sq_mul_integral_ball_le_of_circle_invariant' n δ U' F Wf hδ0 hU'o hball' hFd hWc.continuousOn hW0 hWinv
  have hF0 : F 0 = f z := by simp [hF, hh0]
  rw [hF0] at hcirc

  have hmaps : Set.MapsTo (fun w => z + w) (closedBall (0 : V n) δ) U := fun w hw =>
    hball' hw
  have hfc : ContinuousOn (fun w => f (z + w)) (closedBall (0 : V n) δ) :=
    hf.continuousOn.comp (continuous_const.add continuous_id).continuousOn hmaps
  have hφc : ContinuousOn (fun w => φ (z + w)) (closedBall (0 : V n) δ) :=
    hφ.continuousOn.comp (continuous_const.add continuous_id).continuousOn hmaps
  have hgc : ContinuousOn (fun w => g (z + w)) (closedBall (0 : V n) δ) :=
    hg.comp (continuous_const.add continuous_id).continuousOn hmaps
  have hFc : ContinuousOn F (closedBall (0 : V n) δ) := hFd.continuousOn.mono hball'
  set G : V n → ℝ := fun w => ‖f w‖ ^ 2 * Real.exp (-(m * φ w)) * g w with hG
  have hGc : ContinuousOn (fun w => G (z + w)) (closedBall (0 : V n) δ) := by
    simp only [hG]
    exact ((hfc.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn
      ((continuousOn_const.mul hφc).neg))).mul hgc
  set k : ℝ := Real.exp (-(m * φ z)) * g z * (1 - τ) with hk
  have hk0 : 0 ≤ k := by
    have := hgpos z (hKU hz)
    have : 0 < 1 - τ := by linarith
    positivity
  have hpt : ∀ w ∈ ball (0 : V n) δ, k * (‖F w‖ ^ 2 * Wf w) ≤ G (z + w) := by
    intro w hw
    have hw' : ‖w‖ < δ := by simpa using hw
    have hw1 : w ∈ closedBall (0 : V n) δ₁ := by
      simp only [mem_closedBall, dist_zero_right]; linarith [min_le_left δ₁ δ₃]
    have hb := hbd w hw1
    have hq : (∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re =
        (leviV n (fun v => (φ v : ℂ)) z fun j => w j).re := by
      simp [hH, leviV, cHess]
    have hgzw := hgw z hz w (by linarith [min_le_right δ₁ δ₃])
    have hFn : ‖F w‖ ^ 2 = ‖f (z + w)‖ ^ 2 * Real.exp (-(m * (h w).re)) ^ 2 := by
      simp [hF, norm_mul, Complex.norm_exp, mul_pow]
    have hE : Real.exp (-(m * φ z)) * (Real.exp (-(m * (h w).re)) ^ 2 * Wf w) ≤
        Real.exp (-(m * φ (z + w))) := by
      simp only [hWf]
      rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have := mul_le_mul_of_nonneg_left hb hm0
      rw [hq]
      nlinarith
    have hP : 0 ≤ ‖f (z + w)‖ ^ 2 := by positivity
    have hgz : 0 ≤ (1 - τ) * g z := by
      have := hgpos z (hKU hz); have : 0 < 1 - τ := by linarith
      positivity
    calc k * (‖F w‖ ^ 2 * Wf w)
        = ((1 - τ) * g z) * (‖f (z + w)‖ ^ 2 *
            (Real.exp (-(m * φ z)) * (Real.exp (-(m * (h w).re)) ^ 2 * Wf w))) := by
          rw [hFn, hk]; ring
      _ ≤ g (z + w) * (‖f (z + w)‖ ^ 2 * Real.exp (-(m * φ (z + w)))) := by
          apply mul_le_mul hgzw (mul_le_mul_of_nonneg_left hE hP)
          · have := hW0 w; positivity
          · exact (hgpos _ (hmaps (ball_subset_closedBall hw))).le
      _ = G (z + w) := by simp only [hG]; ring
  have hint1 : IntegrableOn (fun w => k * (‖F w‖ ^ 2 * Wf w)) (ball (0 : V n) δ) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 δ)
      (continuousOn_const.mul ((hFc.norm.pow 2).mul hWc.continuousOn))).mono_set
      ball_subset_closedBall
  have hint2 : IntegrableOn (fun w => G (z + w)) (ball (0 : V n) δ) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 δ) hGc).mono_set
      ball_subset_closedBall
  have hmono := setIntegral_mono_on hint1 hint2 measurableSet_ball hpt
  rw [integral_const_mul, integral_ball_translate z δ G] at hmono

  set J := ∫ w in ball (0 : V n) δ, Wf w with hJ
  set I := ∫ w in ball z δ, G w with hI
  have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_ball fun w _ => hW0 w
  set A := ‖f z‖ ^ 2 * Real.exp (-(m * φ z)) * g z with hA
  have hA0 : 0 ≤ A := by have := hgpos z (hKU hz); positivity
  have hAJ : (1 - τ) * (A * J) ≤ I := by
    have h1 := mul_le_mul_of_nonneg_left hcirc hk0
    calc (1 - τ) * (A * J) = k * (‖f z‖ ^ 2 * J) := by rw [hA, hk]; ring
      _ ≤ _ := h1
      _ ≤ I := hmono
  have hmn : 0 ≤ (m : ℝ) ^ n := by positivity
  have hkey := hτd d hd0 hdD
  change A ≤ (d + ε) * (m : ℝ) ^ n * I
  calc A = A * 1 := (mul_one A).symm
    _ ≤ A * ((d + ε / 2) * (m : ℝ) ^ n * J) := mul_le_mul_of_nonneg_left hT hA0
    _ ≤ A * ((1 - τ) * (d + ε) * (m : ℝ) ^ n * J) := by
        apply mul_le_mul_of_nonneg_left _ hA0
        have := mul_nonneg hmn hJ0
        nlinarith
    _ = (d + ε) * (m : ℝ) ^ n * ((1 - τ) * (A * J)) := by ring
    _ ≤ (d + ε) * (m : ℝ) ^ n * I := by
        apply mul_le_mul_of_nonneg_left hAJ
        have : 0 ≤ d + ε := by linarith
        positivity

end GlobalTheory
