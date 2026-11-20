import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IterDifferentiableOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticGroupLawBoundedCommutatorStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticDoublingMapLocalInverseStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DoublingLimitLocalLogarithmStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalLogarithmHomomorphismStatement
open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Introduce `n g b₀ μ hμ hunit hcomm hassoc`. Establish `hμ0 : μ (b₀, 0, 0) = 0` using `hunit.self_of_nhds.1`. Use `set G : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ) := fun p => μ p - p.2.1 - p.2.2 with hG`. Establish `hGan : AnalyticAt ℂ G (b₀, 0, 0)` using `(hμ.sub (analyticAt_fst.comp_of_eq analyticAt_snd rfl)).sub (analyticAt_snd.comp_of_eq analyticAt_snd rfl)`. Establish `hG0 : G (b₀, 0, 0) = 0` using `by simp [hG, hμ0]`.

Establish `hGsmall : ∀ᶠ p in 𝓝 ((b₀, 0, 0) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)), ‖G p‖ < 1` using `by filter_upwards [hGan.continuousAt (ball_mem_nhds (G (b₀, 0, 0)) one_pos)] with p hp`. Simplify `hp` using `[hG0]`. Take `⟨R₁, hR₁, hball₁⟩` from `Metric.eventually_nhds_iff_ball.1 (hGsmall.and hGan.eventually_analyticAt)`. Take `⟨R₂, hR₂, hball₂⟩` from `Metric.eventually_nhds_iff_ball.1 hunit`. Use `set R := min R₁ R₂ with hRdef`.

Establish `hR : 0 < R` using `lt_min hR₁ hR₂`. Establish `hRG : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : Fin g → ℂ) R, ∀ t ∈ ball (0 : Fin g → ℂ) R, ‖G (b, s, t)‖ < 1 ∧ AnalyticAt ℂ G (b, s, t)`. Introduce `b hb s hs t ht`. Use `hball₁ (b, s, t) ?_` and prove the remaining obligations. Rewrite using `[← ball_prod_same, ← ball_prod_same]`.

Conclude with `⟨ball_subset_ball (min_le_left _ _) hb, ball_subset_ball (min_le_left _ _) hs, ball_subset_ball (min_le_left _ _) ht⟩`. Establish `hRu : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : Fin g → ℂ) R, μ (b, s, 0) = s ∧ μ (b, 0, s) = s`. Introduce `b hb s hs`. Use `hball₂ (b, s) ?_` and prove the remaining obligations. Rewrite using `[← ball_prod_same]`.

Conclude with `⟨ball_subset_ball (min_le_right _ _) hb, ball_subset_ball (min_le_right _ _) hs⟩`. Establish `hGbound : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : Fin g → ℂ) R, ∀ t ∈ ball (0 : Fin g → ℂ) R, ‖μ (b, s, t) - s - t‖ ≤ ‖s‖ * ‖t‖ / R ^ 2`. Use `GlobalTheory.T.analytic_group_law_bounded_commutator b₀ G R hR ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨b, s, t⟩ ⟨hb, hs, ht⟩`. Conclude with `(hRG b hb s hs t ht).2.differentiableAt.differentiableWithinAt`.

Introduce and unpack `⟨b, s, t⟩ ⟨hb, hs, ht⟩`. Conclude with `(hRG b hb s hs t ht).1.le`. Introduce `b hb s hs`. Use `hRu b hb s hs` as an intermediate fact. Simplify using `[hG, this.1, this.2]`.

Use `set C : ℝ := 1 / R ^ 2 with hCdef`. Establish `hCpos : 0 < C` using `by positivity`. Establish `hbound : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : Fin g → ℂ) R, ∀ t ∈ ball (0 : Fin g → ℂ) R, ‖μ (b, s, t) - s - t‖ ≤ C * ‖s‖ * ‖t‖`. Introduce `b hb s hs t ht`. Use `(hGbound b hb s hs t ht).trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[hCdef]`. Expand and normalize the polynomial expressions, which then agree. Use `set d : (Fin n → ℂ) × (Fin g → ℂ) → (Fin g → ℂ) := fun p => μ (p.1, p.2, p.2) with hd`. Establish `hdan : AnalyticAt ℂ d (b₀, 0)`. Establish `h1 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × (Fin g → ℂ) => (p.1, p.2, p.2)) (b₀, 0)` using `analyticAt_fst.prod (analyticAt_snd.prod analyticAt_snd)`.

Conclude with `AnalyticAt.comp_of_eq hμ h1 rfl`. Establish `hd0 : d (b₀, 0) = 0` using `hμ0`. Establish `hdderiv : HasFDerivAt d ((2 : ℂ) • ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin g → ℂ)) (b₀, 0)`. Use `HasFDerivAt.of_isLittleO ?_` and prove the remaining obligations. Rewrite using `[Asymptotics.isLittleO_iff]`.

Introduce `c hc`. Establish `hmem : ball ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)) (min R (c / C)) ∈ 𝓝 ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ))` using `ball_mem_nhds _ (lt_min hR (by positivity))`. Use `filter_upwards [hmem] with p hp`. Take `⟨b, s⟩` from `p`. Rewrite `hp` using `[← ball_prod_same]`.

Take `⟨hb, hs⟩` from `hp`. Establish `hb' : b ∈ ball b₀ R` using `ball_subset_ball (min_le_left _ _) hb`. Establish `hs' : s ∈ ball (0 : Fin g → ℂ) R` using `ball_subset_ball (min_le_left _ _) hs`. Establish `h1` using `hbound b hb' s hs' s hs'`. Establish `hsn : ‖s‖ < c / C` using `by simpa using (ball_subset_ball (min_le_right _ _) hs)`.

Establish `heq : d (b, s) - d (b₀, 0) - ((2 : ℂ) • ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin g → ℂ)) ((b, s) - (b₀, 0)) = μ (b, s, s) - s - s`. Rewrite using `[hd0]`. Simplify using `[hd, two_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[heq]`.

Establish `hle : ‖s‖ ≤ ‖((b, s) : (Fin n → ℂ) × (Fin g → ℂ)) - (b₀, 0)‖`. Simplify using `[Prod.norm_def]`. Establish `hCs : C * ‖s‖ ≤ c` using `((lt_div_iff₀' hCpos).1 hsn).le`. Combine the equalities or inequalities in the displayed calculation. Take `⟨h, hhan, hh0, H1, H2⟩` from `GlobalTheory.T.analytic_doubling_map_local_inverse b₀ d hdan hd0 hdderiv`.

Establish `hmed` using `LocalLog.medial_eventually b₀ μ hμ.continuousAt hμ0 hcomm hassoc`. Establish `hhc : ContinuousAt h (b₀, 0)` using `hhan.continuousAt`. Establish `t0 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => p.1) (𝓝 (b₀, 0, 0)) (𝓝 b₀)` using `continuous_fst.tendsto _`. Establish `t1 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (p.1, p.2.1)) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0))` using `t0.prodMk_nhds ((continuous_fst.comp continuous_snd).tendsto _)`. Establish `t2 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (p.1, p.2.2)) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0))` using `t0.prodMk_nhds ((continuous_snd.comp continuous_snd).tendsto _)`.

Establish `ts : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => h (p.1, p.2.1)) (𝓝 (b₀, 0, 0)) (𝓝 0)`. Simplify `hhc.tendsto.comp t1` using `[Function.comp_def, hh0]`. Establish `tt : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => h (p.1, p.2.2)) (𝓝 (b₀, 0, 0)) (𝓝 0)`. Simplify `hhc.tendsto.comp t2` using `[Function.comp_def, hh0]`. Establish `t3 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (p.1, h (p.1, p.2.1), h (p.1, p.2.2))) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0, 0))` using `t0.prodMk_nhds (ts.prodMk_nhds tt)`.

Establish `t4 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (p.1, μ (p.1, h (p.1, p.2.1), h (p.1, p.2.2)))) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0))` using `t0.prodMk_nhds (by simpa [Function.comp_def, hμ0] using hμ.continuousAt.tendsto.comp t3)`. Establish `hhom : ∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0), h (p.1, μ p) = μ (p.1, h (p.1, p.2.1), h (p.1, p.2.2))` using `by filter_upwards [t1.eventually H1, t2.eventually H1, t3.eventually hmed, t4.eventually H2] with p e1 e2 e3 e4`. Take `⟨b, s, t⟩` from `p`. Establish `e1' : μ (b, h (b, s), h (b, s)) = s` using `e1`. Establish `e2' : μ (b, h (b, t), h (b, t)) = t` using `e2`.

Establish `e3' : μ (b, μ (b, h (b, s), h (b, s)), μ (b, h (b, t), h (b, t))) = μ (b, μ (b, h (b, s), h (b, t)), μ (b, h (b, s), h (b, t)))` using `e3`. Establish `e4' : h (b, μ (b, μ (b, h (b, s), h (b, t)), μ (b, h (b, s), h (b, t)))) = μ (b, h (b, s), h (b, t))` using `e4`. Rewrite `e3'` using `[e1', e2']`. Use `show h (b, μ (b, s, t)) = μ (b, h (b, s), h (b, t))`. Rewrite using `[e3', e4']`.

Establish `hsmall : ∀ᶠ q in 𝓝 ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)), ‖h q‖ < min R (1 / (3 * C))`. Establish `hpos : 0 < min R (1 / (3 * C))` using `lt_min hR (by positivity)`. Use `filter_upwards [hhc (ball_mem_nhds (h (b₀, 0)) hpos)] with p hp`. Simplify `hp` using `[hh0]`. Take `⟨ρ₁, hρ₁, hb₁⟩` from `Metric.eventually_nhds_iff_ball.1 (H1.and (hhan.eventually_analyticAt.and hsmall))`.

Take `⟨ρ₂, hρ₂, hb₂⟩` from `Metric.eventually_nhds_iff_ball.1 hhom`. Use `set ρ := min R (min ρ₁ ρ₂) with hρdef`. Establish `hρ : 0 < ρ` using `lt_min hR (lt_min hρ₁ hρ₂)`. Establish `hρR : ρ ≤ R` using `min_le_left _ _`. Establish `hρ1 : ρ ≤ ρ₁` using `(min_le_right _ _).trans (min_le_left _ _)`.

Establish `hρ2 : ρ ≤ ρ₂` using `(min_le_right _ _).trans (min_le_right _ _)`. Establish `hq : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, μ (b, h (b, s), h (b, s)) = s ∧ AnalyticAt ℂ h (b, s) ∧ ‖h (b, s)‖ < min R (1 / (3 * C))`. Introduce `b hb s hs`. Use `hb₁ (b, s) ?_` and prove the remaining obligations. Rewrite using `[← ball_prod_same]`.

Conclude with `⟨ball_subset_ball hρ1 hb, ball_subset_ball hρ1 hs⟩`. Establish `hhomρ : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ∀ t ∈ ball (0 : Fin g → ℂ) ρ, h (b, μ (b, s, t)) = μ (b, h (b, s), h (b, t))`. Introduce `b hb s hs t ht`. Use `hb₂ (b, s, t) ?_` and prove the remaining obligations. Rewrite using `[← ball_prod_same, ← ball_prod_same]`.

Conclude with `⟨ball_subset_ball hρ2 hb, ball_subset_ball hρ2 hs, ball_subset_ball hρ2 ht⟩`. Establish `hboundρ : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ∀ t ∈ ball (0 : Fin g → ℂ) ρ, ‖μ (b, s, t) - s - t‖ ≤ C * ‖s‖ * ‖t‖` using `fun b hb s hs t ht => hbound b (ball_subset_ball hρR hb) s (ball_subset_ball hρR hs) t (ball_subset_ball hρR ht)`. Establish `key : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖h (b, s)‖ ^ 2`. Introduce `b hb s hs`. Take `⟨e1, -, e3⟩` from `hq b hb s hs`.

Establish `hs' : h (b, s) ∈ ball (0 : Fin g → ℂ) R`. Rewrite using `[mem_ball_zero_iff]`. Conclude with `e3.trans_le (min_le_left _ _)`. Establish `h1` using `hbound b (ball_subset_ball hρR hb) _ hs' _ hs'`. Rewrite `h1` using `[e1]`.

Establish `h2 : (2 : ℂ) • h (b, s) - s = -(s - h (b, s) - h (b, s))`. Rewrite using `[two_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[h2, norm_neg]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hcontr : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖`. Introduce `b hb s hs`. Establish `h1` using `key b hb s hs`. Take `⟨-, -, e3⟩` from `hq b hb s hs`. Establish `h3 : ‖h (b, s)‖ < 1 / (3 * C)` using `e3.trans_le (min_le_right _ _)`.

Establish `h4 : C * ‖h (b, s)‖ ≤ 1 / 3`. Rewrite `h3` using `[lt_div_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h5 : ‖(2 : ℂ) • h (b, s)‖ = 2 * ‖h (b, s)‖` using `by simp [norm_smul]`. Establish `h6 : ‖(2 : ℂ) • h (b, s)‖ ≤ ‖(2 : ℂ) • h (b, s) - s‖ + ‖s‖` using `norm_le_norm_sub_add _ _`.

Establish `h7` using `norm_nonneg (h (b, s))`. Use the polynomial consequences of the given equalities and inequalities. Establish `hquad : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖s‖ ^ 2`. Introduce `b hb s hs`. Use `(key b hb s hs).trans ?_` and prove the remaining obligations.

Establish `h1` using `hcontr b hb s hs`. Establish `h2 : ‖h (b, s)‖ ≤ ‖s‖` using `by linarith [norm_nonneg s]`. Use `gcongr`. Take `⟨L, hLu, hLb⟩` from `GlobalTheory.T.doubling_limit_local_logarithm b₀ h ρ C hρ hCpos.le hcontr hquad`. Establish `hdiffh : DifferentiableOn ℂ h (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) ρ)`.

Introduce and unpack `⟨b, s⟩ ⟨hb, hs⟩`. Conclude with `(hq b hb s hs).2.1.differentiableAt.differentiableWithinAt`. Establish `hit` using `fun k => LocalLog.iter_differentiableOn b₀ h ρ hdiffh hcontr k`. Establish `hDopen : IsOpen (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) ρ)` using `isOpen_ball.prod isOpen_ball`. Establish `hLd : DifferentiableOn ℂ L (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) ρ)` using `GlobalTheory.SCV.differentiableOn_of_tendstoLocallyUniformlyOn hDopen hLu.tendstoLocallyUniformlyOn (Eventually.of_forall fun k => by show DifferentiableOn ℂ ((2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k) _`.

Conclude with `(hit k).const_smul _)`. Establish `hLan : AnalyticAt ℂ L (b₀, 0)` using `GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hDopen hLd _ ⟨mem_ball_self hρ, mem_ball_self hρ⟩`. Use `⟨L, hLan, ?_, ?_⟩` and prove the remaining obligations. Use `filter_upwards [ball_mem_nhds b₀ hρ] with b hb`. Establish `hL0 : L (b, 0) = 0`.

Use `hLb b hb 0 (mem_ball_self hρ)` as an intermediate fact. Simplify using `using this`. Use `⟨hL0, ?_⟩` and prove the remaining obligations. Use `HasFDerivAt.of_isLittleO ?_` and prove the remaining obligations. Rewrite using `[Asymptotics.isLittleO_iff]`.

Introduce `c hc`. Establish `hc' : 0 < c / (4 * C)` using `by positivity`. Use `filter_upwards [ball_mem_nhds (0 : Fin g → ℂ) (lt_min hρ hc')] with s hs`. Establish `hs1 : s ∈ ball (0 : Fin g → ℂ) ρ` using `ball_subset_ball (min_le_left _ _) hs`. Establish `hs2 : ‖s‖ < c / (4 * C)` using `by simpa using (ball_subset_ball (min_le_right _ _) hs)`.

Establish `h1` using `hLb b hb s hs1`. Establish `h2 : 4 * C * ‖s‖ ≤ c` using `((lt_div_iff₀' (by positivity)).1 hs2).le`. Simplify using `only [hL0, sub_zero, ContinuousLinearMap.id_apply]`. Combine the equalities or inequalities in the displayed calculation. Establish `hpt : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, Tendsto (fun k : ℕ => (2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k (b, s)) atTop (𝓝 (L (b, s)))` using `fun b hb s hs => hLu.tendsto_at ⟨hb, hs⟩`.

Establish `hadd` using `GlobalTheory.T.local_logarithm_homomorphism b₀ h μ L ρ C hρ hCpos.le hcontr hboundρ hhomρ hpt`. Establish `hμs : ∀ᶠ p in 𝓝 ((b₀, 0, 0) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)), μ p ∈ ball (0 : Fin g → ℂ) ρ` using `by filter_upwards [hμ.continuousAt (ball_mem_nhds (μ (b₀, 0, 0)) hρ)] with p hp`. Simplify `hp` using `[hμ0]`. Use `filter_upwards [ball_mem_nhds ((b₀, 0, 0) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)) hρ, hμs] with p hp hq'`. Take `⟨b, s, t⟩` from `p`.

Rewrite `hp` using `[← ball_prod_same, ← ball_prod_same]`. Conclude with `hadd b hp.1 s hp.2.1 t hp.2.2 hq'`.
-/
theorem exists_local_log_of_commutative_law : ∀ (n g : ℕ) (b₀ : Fin n → ℂ) (μ : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)), AnalyticAt ℂ μ (b₀, 0, 0) → (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), μ (p.1, p.2, 0) = p.2 ∧ μ (p.1, 0, p.2) = p.2) → (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0), μ (p.1, p.2.1, p.2.2) = μ (p.1, p.2.2, p.2.1)) → (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0, 0), μ (p.1, μ (p.1, p.2.1, p.2.2.1), p.2.2.2) = μ (p.1, p.2.1, μ (p.1, p.2.2.1, p.2.2.2))) → ∃ L : (Fin n → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ L (b₀, 0) ∧ (∀ᶠ b in 𝓝 b₀, L (b, 0) = 0 ∧ HasFDerivAt (fun s => L (b, s)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧ ∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0), L (p.1, μ p) = L (p.1, p.2.1) + L (p.1, p.2.2) := by
  intro n g b₀ μ hμ hunit hcomm hassoc
  have hμ0 : μ (b₀, 0, 0) = 0 := hunit.self_of_nhds.1

  set G : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ) := fun p => μ p - p.2.1 - p.2.2 with hG
  have hGan : AnalyticAt ℂ G (b₀, 0, 0) :=
    (hμ.sub (analyticAt_fst.comp_of_eq analyticAt_snd rfl)).sub (analyticAt_snd.comp_of_eq analyticAt_snd rfl)
  have hG0 : G (b₀, 0, 0) = 0 := by simp [hG, hμ0]
  have hGsmall : ∀ᶠ p in 𝓝 ((b₀, 0, 0) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)), ‖G p‖ < 1 := by
    filter_upwards [hGan.continuousAt (ball_mem_nhds (G (b₀, 0, 0)) one_pos)] with p hp
    simpa [hG0] using hp
  obtain ⟨R₁, hR₁, hball₁⟩ := Metric.eventually_nhds_iff_ball.1 (hGsmall.and hGan.eventually_analyticAt)
  obtain ⟨R₂, hR₂, hball₂⟩ := Metric.eventually_nhds_iff_ball.1 hunit
  set R := min R₁ R₂ with hRdef
  have hR : 0 < R := lt_min hR₁ hR₂
  have hRG : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : Fin g → ℂ) R, ∀ t ∈ ball (0 : Fin g → ℂ) R, ‖G (b, s, t)‖ < 1 ∧ AnalyticAt ℂ G (b, s, t) := by
    intro b hb s hs t ht
    refine hball₁ (b, s, t) ?_
    rw [← ball_prod_same, ← ball_prod_same]
    exact ⟨ball_subset_ball (min_le_left _ _) hb, ball_subset_ball (min_le_left _ _) hs, ball_subset_ball (min_le_left _ _) ht⟩
  have hRu : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : Fin g → ℂ) R, μ (b, s, 0) = s ∧ μ (b, 0, s) = s := by
    intro b hb s hs
    refine hball₂ (b, s) ?_
    rw [← ball_prod_same]
    exact ⟨ball_subset_ball (min_le_right _ _) hb, ball_subset_ball (min_le_right _ _) hs⟩
  have hGbound : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : Fin g → ℂ) R, ∀ t ∈ ball (0 : Fin g → ℂ) R, ‖μ (b, s, t) - s - t‖ ≤ ‖s‖ * ‖t‖ / R ^ 2 := by
    refine GlobalTheory.T.analytic_group_law_bounded_commutator b₀ G R hR ?_ ?_ ?_
    · rintro ⟨b, s, t⟩ ⟨hb, hs, ht⟩
      exact (hRG b hb s hs t ht).2.differentiableAt.differentiableWithinAt
    · rintro ⟨b, s, t⟩ ⟨hb, hs, ht⟩
      exact (hRG b hb s hs t ht).1.le
    · intro b hb s hs
      have := hRu b hb s hs
      simp [hG, this.1, this.2]
  set C : ℝ := 1 / R ^ 2 with hCdef
  have hCpos : 0 < C := by positivity
  have hbound : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : Fin g → ℂ) R, ∀ t ∈ ball (0 : Fin g → ℂ) R, ‖μ (b, s, t) - s - t‖ ≤ C * ‖s‖ * ‖t‖ := by
    intro b hb s hs t ht
    refine (hGbound b hb s hs t ht).trans (le_of_eq ?_)
    rw [hCdef]; ring
  set d : (Fin n → ℂ) × (Fin g → ℂ) → (Fin g → ℂ) := fun p => μ (p.1, p.2, p.2) with hd
  have hdan : AnalyticAt ℂ d (b₀, 0) := by
    have h1 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × (Fin g → ℂ) => (p.1, p.2, p.2)) (b₀, 0) :=
      analyticAt_fst.prod (analyticAt_snd.prod analyticAt_snd)
    exact AnalyticAt.comp_of_eq hμ h1 rfl
  have hd0 : d (b₀, 0) = 0 := hμ0
  have hdderiv : HasFDerivAt d ((2 : ℂ) • ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin g → ℂ)) (b₀, 0) := by
    refine HasFDerivAt.of_isLittleO ?_
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hmem : ball ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)) (min R (c / C)) ∈ 𝓝 ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)) :=
      ball_mem_nhds _ (lt_min hR (by positivity))
    filter_upwards [hmem] with p hp
    obtain ⟨b, s⟩ := p
    rw [← ball_prod_same] at hp
    obtain ⟨hb, hs⟩ := hp
    have hb' : b ∈ ball b₀ R := ball_subset_ball (min_le_left _ _) hb
    have hs' : s ∈ ball (0 : Fin g → ℂ) R := ball_subset_ball (min_le_left _ _) hs
    have h1 := hbound b hb' s hs' s hs'
    have hsn : ‖s‖ < c / C := by simpa using (ball_subset_ball (min_le_right _ _) hs)
    have heq : d (b, s) - d (b₀, 0) - ((2 : ℂ) • ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin g → ℂ)) ((b, s) - (b₀, 0)) = μ (b, s, s) - s - s := by
      rw [hd0]
      simp [hd, two_smul]
      abel
    rw [heq]
    have hle : ‖s‖ ≤ ‖((b, s) : (Fin n → ℂ) × (Fin g → ℂ)) - (b₀, 0)‖ := by
      simp [Prod.norm_def]
    have hCs : C * ‖s‖ ≤ c := ((lt_div_iff₀' hCpos).1 hsn).le
    calc ‖μ (b, s, s) - s - s‖ ≤ C * ‖s‖ * ‖s‖ := h1
      _ ≤ c * ‖s‖ := by gcongr
      _ ≤ c * ‖((b, s) : (Fin n → ℂ) × (Fin g → ℂ)) - (b₀, 0)‖ := by gcongr
  obtain ⟨h, hhan, hh0, H1, H2⟩ := GlobalTheory.T.analytic_doubling_map_local_inverse b₀ d hdan hd0 hdderiv
  have hmed := LocalLog.medial_eventually b₀ μ hμ.continuousAt hμ0 hcomm hassoc
  have hhc : ContinuousAt h (b₀, 0) := hhan.continuousAt
  have t0 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => p.1) (𝓝 (b₀, 0, 0)) (𝓝 b₀) :=
    continuous_fst.tendsto _
  have t1 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (p.1, p.2.1)) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0)) :=
    t0.prodMk_nhds ((continuous_fst.comp continuous_snd).tendsto _)
  have t2 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (p.1, p.2.2)) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0)) :=
    t0.prodMk_nhds ((continuous_snd.comp continuous_snd).tendsto _)
  have ts : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => h (p.1, p.2.1)) (𝓝 (b₀, 0, 0)) (𝓝 0) := by
    simpa [Function.comp_def, hh0] using hhc.tendsto.comp t1
  have tt : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => h (p.1, p.2.2)) (𝓝 (b₀, 0, 0)) (𝓝 0) := by
    simpa [Function.comp_def, hh0] using hhc.tendsto.comp t2
  have t3 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (p.1, h (p.1, p.2.1), h (p.1, p.2.2))) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0, 0)) :=
    t0.prodMk_nhds (ts.prodMk_nhds tt)
  have t4 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (p.1, μ (p.1, h (p.1, p.2.1), h (p.1, p.2.2)))) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0)) :=
    t0.prodMk_nhds (by simpa [Function.comp_def, hμ0] using hμ.continuousAt.tendsto.comp t3)
  have hhom : ∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0), h (p.1, μ p) = μ (p.1, h (p.1, p.2.1), h (p.1, p.2.2)) := by
    filter_upwards [t1.eventually H1, t2.eventually H1, t3.eventually hmed, t4.eventually H2] with p e1 e2 e3 e4
    obtain ⟨b, s, t⟩ := p
    have e1' : μ (b, h (b, s), h (b, s)) = s := e1
    have e2' : μ (b, h (b, t), h (b, t)) = t := e2
    have e3' : μ (b, μ (b, h (b, s), h (b, s)), μ (b, h (b, t), h (b, t))) = μ (b, μ (b, h (b, s), h (b, t)), μ (b, h (b, s), h (b, t))) := e3
    have e4' : h (b, μ (b, μ (b, h (b, s), h (b, t)), μ (b, h (b, s), h (b, t)))) = μ (b, h (b, s), h (b, t)) := e4
    rw [e1', e2'] at e3'
    show h (b, μ (b, s, t)) = μ (b, h (b, s), h (b, t))
    rw [e3', e4']
  have hsmall : ∀ᶠ q in 𝓝 ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)), ‖h q‖ < min R (1 / (3 * C)) := by
    have hpos : 0 < min R (1 / (3 * C)) := lt_min hR (by positivity)
    filter_upwards [hhc (ball_mem_nhds (h (b₀, 0)) hpos)] with p hp
    simpa [hh0] using hp
  obtain ⟨ρ₁, hρ₁, hb₁⟩ := Metric.eventually_nhds_iff_ball.1 (H1.and (hhan.eventually_analyticAt.and hsmall))
  obtain ⟨ρ₂, hρ₂, hb₂⟩ := Metric.eventually_nhds_iff_ball.1 hhom
  set ρ := min R (min ρ₁ ρ₂) with hρdef
  have hρ : 0 < ρ := lt_min hR (lt_min hρ₁ hρ₂)
  have hρR : ρ ≤ R := min_le_left _ _
  have hρ1 : ρ ≤ ρ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hρ2 : ρ ≤ ρ₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hq : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, μ (b, h (b, s), h (b, s)) = s ∧ AnalyticAt ℂ h (b, s) ∧ ‖h (b, s)‖ < min R (1 / (3 * C)) := by
    intro b hb s hs
    refine hb₁ (b, s) ?_
    rw [← ball_prod_same]
    exact ⟨ball_subset_ball hρ1 hb, ball_subset_ball hρ1 hs⟩
  have hhomρ : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ∀ t ∈ ball (0 : Fin g → ℂ) ρ, h (b, μ (b, s, t)) = μ (b, h (b, s), h (b, t)) := by
    intro b hb s hs t ht
    refine hb₂ (b, s, t) ?_
    rw [← ball_prod_same, ← ball_prod_same]
    exact ⟨ball_subset_ball hρ2 hb, ball_subset_ball hρ2 hs, ball_subset_ball hρ2 ht⟩
  have hboundρ : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ∀ t ∈ ball (0 : Fin g → ℂ) ρ, ‖μ (b, s, t) - s - t‖ ≤ C * ‖s‖ * ‖t‖ :=
    fun b hb s hs t ht => hbound b (ball_subset_ball hρR hb) s (ball_subset_ball hρR hs) t (ball_subset_ball hρR ht)
  have key : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖h (b, s)‖ ^ 2 := by
    intro b hb s hs
    obtain ⟨e1, -, e3⟩ := hq b hb s hs
    have hs' : h (b, s) ∈ ball (0 : Fin g → ℂ) R := by
      rw [mem_ball_zero_iff]; exact e3.trans_le (min_le_left _ _)
    have h1 := hbound b (ball_subset_ball hρR hb) _ hs' _ hs'
    rw [e1] at h1
    have h2 : (2 : ℂ) • h (b, s) - s = -(s - h (b, s) - h (b, s)) := by
      rw [two_smul]; abel
    rw [h2, norm_neg]
    calc _ ≤ _ := h1
      _ = _ := by ring
  have hcontr : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖ := by
    intro b hb s hs
    have h1 := key b hb s hs
    obtain ⟨-, -, e3⟩ := hq b hb s hs
    have h3 : ‖h (b, s)‖ < 1 / (3 * C) := e3.trans_le (min_le_right _ _)
    have h4 : C * ‖h (b, s)‖ ≤ 1 / 3 := by
      rw [lt_div_iff₀ (by positivity)] at h3
      nlinarith
    have h5 : ‖(2 : ℂ) • h (b, s)‖ = 2 * ‖h (b, s)‖ := by simp [norm_smul]
    have h6 : ‖(2 : ℂ) • h (b, s)‖ ≤ ‖(2 : ℂ) • h (b, s) - s‖ + ‖s‖ := norm_le_norm_sub_add _ _
    have h7 := norm_nonneg (h (b, s))
    nlinarith
  have hquad : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖s‖ ^ 2 := by
    intro b hb s hs
    refine (key b hb s hs).trans ?_
    have h1 := hcontr b hb s hs
    have h2 : ‖h (b, s)‖ ≤ ‖s‖ := by linarith [norm_nonneg s]
    gcongr
  obtain ⟨L, hLu, hLb⟩ := GlobalTheory.T.doubling_limit_local_logarithm b₀ h ρ C hρ hCpos.le hcontr hquad
  have hdiffh : DifferentiableOn ℂ h (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) ρ) := by
    rintro ⟨b, s⟩ ⟨hb, hs⟩
    exact (hq b hb s hs).2.1.differentiableAt.differentiableWithinAt
  have hit := fun k => LocalLog.iter_differentiableOn b₀ h ρ hdiffh hcontr k
  have hDopen : IsOpen (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) ρ) := isOpen_ball.prod isOpen_ball
  have hLd : DifferentiableOn ℂ L (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) ρ) :=
    GlobalTheory.SCV.differentiableOn_of_tendstoLocallyUniformlyOn hDopen hLu.tendstoLocallyUniformlyOn
      (Eventually.of_forall fun k => by
        show DifferentiableOn ℂ ((2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k) _
        exact (hit k).const_smul _)
  have hLan : AnalyticAt ℂ L (b₀, 0) :=
    GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hDopen hLd _ ⟨mem_ball_self hρ, mem_ball_self hρ⟩
  refine ⟨L, hLan, ?_, ?_⟩
  · filter_upwards [ball_mem_nhds b₀ hρ] with b hb
    have hL0 : L (b, 0) = 0 := by
      have := hLb b hb 0 (mem_ball_self hρ)
      simpa using this
    refine ⟨hL0, ?_⟩
    refine HasFDerivAt.of_isLittleO ?_
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hc' : 0 < c / (4 * C) := by positivity
    filter_upwards [ball_mem_nhds (0 : Fin g → ℂ) (lt_min hρ hc')] with s hs
    have hs1 : s ∈ ball (0 : Fin g → ℂ) ρ := ball_subset_ball (min_le_left _ _) hs
    have hs2 : ‖s‖ < c / (4 * C) := by simpa using (ball_subset_ball (min_le_right _ _) hs)
    have h1 := hLb b hb s hs1
    have h2 : 4 * C * ‖s‖ ≤ c := ((lt_div_iff₀' (by positivity)).1 hs2).le
    simp only [hL0, sub_zero, ContinuousLinearMap.id_apply]
    calc ‖L (b, s) - s‖ ≤ 4 * C * ‖s‖ ^ 2 := h1
      _ = 4 * C * ‖s‖ * ‖s‖ := by ring
      _ ≤ c * ‖s‖ := by gcongr
  · have hpt : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, Tendsto (fun k : ℕ => (2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k (b, s)) atTop (𝓝 (L (b, s))) :=
      fun b hb s hs => hLu.tendsto_at ⟨hb, hs⟩
    have hadd := GlobalTheory.T.local_logarithm_homomorphism b₀ h μ L ρ C hρ hCpos.le hcontr hboundρ hhomρ hpt
    have hμs : ∀ᶠ p in 𝓝 ((b₀, 0, 0) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)), μ p ∈ ball (0 : Fin g → ℂ) ρ := by
      filter_upwards [hμ.continuousAt (ball_mem_nhds (μ (b₀, 0, 0)) hρ)] with p hp
      simpa [hμ0] using hp
    filter_upwards [ball_mem_nhds ((b₀, 0, 0) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)) hρ, hμs] with p hp hq'
    obtain ⟨b, s, t⟩ := p
    rw [← ball_prod_same, ← ball_prod_same] at hp
    exact hadd b hp.1 s hp.2.1 t hp.2.2 hq'

end GlobalTheory.CompanionTheory.Ar.Flat
