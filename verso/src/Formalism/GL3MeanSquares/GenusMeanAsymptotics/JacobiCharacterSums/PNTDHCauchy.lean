import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHSt
import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower

open Finset Complex Classical Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

/- English proof (translation)
Proceed by induction on `Z using Finset.induction_on with`. Consider the case `empty`. Introduce `U G C _ hd hb`. Conclude with `⟨G, by simpa using hd, fun _ _ => rfl, by simpa using hb⟩`. Consider the case `insert a Z ha ih`.

Introduce `U G C hU hd hb`. Establish `hset : U \ ((insert a Z : Finset ℂ) : Set ℂ) = (U \ {a}) \ (Z : Set ℂ)`. Use extensionality with `z`. Simplify using `[not_or, and_assoc]`. Rewrite `hd`, `hb` using `[hset]`.

Take `⟨H₁, hH₁d, hH₁e, hH₁b⟩` from `ih (U \ {a}) G C (hU.sdiff isClosed_singleton) hd hb`. Rewrite using `[hset]`. Distinguish the cases in `haU : a ∈ U`. Establish `hUa : U ∈ 𝓝 a` using `hU.mem_nhds haU`. Establish `hbd : BddAbove (norm ∘ H₁ '' (U \ {a}))` using `⟨C, by rintro _ ⟨z, hz, rfl⟩; exact hH₁b z hz⟩`.

Establish `hD` using `differentiableOn_update_limUnder_of_bddAbove hUa hH₁d hbd`. Establish `hne : ∀ z, z ≠ a → Function.update H₁ a (limUnder (𝓝[≠] a) H₁) z = H₁ z` using `fun z hz => Function.update_of_ne hz _ _`. Use `⟨_, hD, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Rewrite using `[hne z hz.1.2]`.

Conclude with `hH₁e z hz`. Introduce `z hz`. Distinguish the cases in `hza : z = a`. Rewrite using `[hza]`. Establish `hc` using `(hD.differentiableAt hUa).continuousAt`.

Establish `ht` using `(hc.norm).tendsto.mono_left (nhdsWithin_le_nhds (s := {a}ᶜ))`. Use `le_of_tendsto ht ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hUa] with w hw hwU`. Rewrite using `[hne w hw]`. Conclude with `hH₁b w ⟨hwU, hw⟩`.

Rewrite using `[hne z hza]`. Conclude with `hH₁b z ⟨hz, hza⟩`. Establish `hUe : U \ {a} = U` using `Set.sdiff_singleton_eq_self haU`. Rewrite `hH₁d`, `hH₁b`, `hH₁e`, the goal using `[hUe]`. Conclude with `⟨H₁, hH₁d, hH₁e, hH₁b⟩`.
-/
lemma dhc_removable (Z : Finset ℂ) : ∀ (U : Set ℂ) (G : ℂ → ℂ) (C : ℝ), IsOpen U →
    DifferentiableOn ℂ G (U \ (Z : Set ℂ)) → (∀ z ∈ U \ (Z : Set ℂ), ‖G z‖ ≤ C) →
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H U ∧ (∀ z ∈ U \ (Z : Set ℂ), H z = G z) ∧
      ∀ z ∈ U, ‖H z‖ ≤ C := by
  induction Z using Finset.induction_on with
  | empty =>
    intro U G C _ hd hb
    exact ⟨G, by simpa using hd, fun _ _ => rfl, by simpa using hb⟩
  | insert a Z ha ih =>
    intro U G C hU hd hb
    have hset : U \ ((insert a Z : Finset ℂ) : Set ℂ) = (U \ {a}) \ (Z : Set ℂ) := by
      ext z
      simp [not_or, and_assoc]
    rw [hset] at hd hb
    obtain ⟨H₁, hH₁d, hH₁e, hH₁b⟩ := ih (U \ {a}) G C (hU.sdiff isClosed_singleton) hd hb
    rw [hset]
    by_cases haU : a ∈ U
    · have hUa : U ∈ 𝓝 a := hU.mem_nhds haU
      have hbd : BddAbove (norm ∘ H₁ '' (U \ {a})) :=
        ⟨C, by rintro _ ⟨z, hz, rfl⟩; exact hH₁b z hz⟩
      have hD := differentiableOn_update_limUnder_of_bddAbove hUa hH₁d hbd
      have hne : ∀ z, z ≠ a → Function.update H₁ a (limUnder (𝓝[≠] a) H₁) z = H₁ z :=
        fun z hz => Function.update_of_ne hz _ _
      refine ⟨_, hD, ?_, ?_⟩
      · intro z hz
        rw [hne z hz.1.2]
        exact hH₁e z hz
      · intro z hz
        by_cases hza : z = a
        · rw [hza]
          have hc := (hD.differentiableAt hUa).continuousAt
          have ht := (hc.norm).tendsto.mono_left (nhdsWithin_le_nhds (s := {a}ᶜ))
          refine le_of_tendsto ht ?_
          filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hUa] with w hw hwU
          rw [hne w hw]
          exact hH₁b w ⟨hwU, hw⟩
        · rw [hne z hza]
          exact hH₁b z ⟨hz, hza⟩
    · have hUe : U \ {a} = U := Set.sdiff_singleton_eq_self haU
      rw [hUe] at hH₁d hH₁b hH₁e ⊢
      exact ⟨H₁, hH₁d, hH₁e, hH₁b⟩

/- English proof (translation)
Establish `h : (fun z : ℂ => c / (z - ρ)) = fun z => c * (fun z : ℂ => (1 * z - ρ)⁻¹) z`. Use extensionality with `z`. Simplify using `[div_eq_mul_inv]`. Establish `hk : (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ)` using `by push_cast; ring`. Rewrite using `[h, iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_inv_linear_sub]`.

Simplify using `only [one_pow, mul_one, one_mul]`. Rewrite using `[hk, zpow_neg, zpow_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma dhc_iter (c ρ : ℂ) (k : ℕ) (s : ℂ) :
    iteratedDeriv k (fun z => c / (z - ρ)) s =
      c * ((-1) ^ k * (k.factorial : ℂ)) * ((s - ρ) ^ (k + 1))⁻¹ := by
  have h : (fun z : ℂ => c / (z - ρ)) = fun z => c * (fun z : ℂ => (1 * z - ρ)⁻¹) z := by
    ext z
    simp [div_eq_mul_inv]
  have hk : (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_inv_linear_sub]
  simp only [one_pow, mul_one, one_mul]
  rw [hk, zpow_neg, zpow_natCast]
  ring

/- English proof (translation)
Establish `hcont : ContinuousAt (fun R : ℝ => (k.factorial : ℝ) * C / R ^ k) ϱ` using `continuousAt_const.div (continuousAt_id.pow k) (pow_pos hϱ k).ne'`. Establish `ht` using `hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio ϱ))`. Use `ge_of_tendsto ht ?_` and prove the remaining obligations. Use `filter_upwards [Ioo_mem_nhdsLT hϱ] with R hR`. Establish `hsub : Metric.closedBall s R ⊆ Metric.ball z₀ (2 * ϱ)`.

Introduce `z hz`. Rewrite `hz`, `hs` using `[Metric.mem_closedBall]`. Rewrite using `[Metric.mem_ball]`. Use `dist_triangle z s z₀` as an intermediate fact. Combine the linear relations using `[hR.2]`.

Conclude with `norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR.1 (hHd.diffContOnCl_ball hsub) (fun z hz => hHb z (hsub (Metric.sphere_subset_closedBall hz)))`.
-/
lemma dhc_cauchy (H : ℂ → ℂ) (z₀ s : ℂ) (ϱ C : ℝ) (hϱ : 0 < ϱ)
    (hHd : DifferentiableOn ℂ H (Metric.ball z₀ (2 * ϱ))) (hHb : ∀ z ∈ Metric.ball z₀ (2 * ϱ), ‖H z‖ ≤ C)
    (hs : s ∈ Metric.closedBall z₀ ϱ) (k : ℕ) :
    ‖iteratedDeriv k H s‖ ≤ k.factorial * C / ϱ ^ k := by
  have hcont : ContinuousAt (fun R : ℝ => (k.factorial : ℝ) * C / R ^ k) ϱ :=
    continuousAt_const.div (continuousAt_id.pow k) (pow_pos hϱ k).ne'
  have ht := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio ϱ))
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT hϱ] with R hR
  have hsub : Metric.closedBall s R ⊆ Metric.ball z₀ (2 * ϱ) := by
    intro z hz
    rw [Metric.mem_closedBall] at hz hs
    rw [Metric.mem_ball]
    have := dist_triangle z s z₀
    linarith [hR.2]
  exact norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR.1 (hHd.diffContOnCl_ball hsub)
    (fun z hz => hHb z (hsub (Metric.sphere_subset_closedBall hz)))

/- English proof (translation)
Introduce `f z₀ r B hr hB hfd hf0 hfb`. Take `⟨Z, m, hZ, hm1, -, -, hsum, hbd⟩` from `landau_local3 f z₀ r B hr hB hfd hf0 hfb`. Use `⟨Z, m, hZ, hm1, hsum, ?_⟩` and prove the remaining obligations. Establish `hfan : ∀ z ∈ Metric.ball z₀ (r / 6), AnalyticAt ℂ f z` using `fun z hz => (hfd.mono Metric.ball_subset_closedBall).analyticAt (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball (by linarith) hz))`. Establish `hnz : ∀ z ∈ Metric.ball z₀ (r / 6) \ (Z : Set ℂ), f z ≠ 0` using `fun z hz h0 => hz.2 (Finset.mem_coe.2 ((hZ z).2 ⟨Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hz.1), h0⟩))`.

Establish `hGd : DifferentiableOn ℂ (fun z => deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)) (Metric.ball z₀ (r / 6) \ (Z : Set ℂ))`. Introduce `z hz`. Establish `h1` using `hfan z hz.1`. Use `DifferentiableAt.differentiableWithinAt ?_` and prove the remaining obligations. Use `(h1.deriv.differentiableAt.div h1.differentiableAt (hnz z hz)).sub ?_` and prove the remaining obligations.

Use `DifferentiableAt.fun_sum (fun ρ hρ => ?_)` and prove the remaining obligations. Conclude with `(differentiableAt_const _).div (differentiableAt_id.sub_const ρ) (sub_ne_zero.2 (fun h => hz.2 (h ▸ Finset.mem_coe.2 hρ)))`. Take `⟨H, hHd, hHe, hHb⟩` from `dhc_removable Z _ _ (72 * Real.log B / r) Metric.isOpen_ball hGd (fun z hz => hbd z (Metric.ball_subset_closedBall hz.1) (hnz z hz))`. Introduce `k s hs hfs`. Establish `hsZ : s ∉ (Z : Set ℂ)` using `fun h => hfs ((hZ s).1 (Finset.mem_coe.1 h)).2`.

Establish `hsU : s ∈ Metric.ball z₀ (r / 6)`. Rewrite `hs` using `[Metric.mem_closedBall]`. Rewrite using `[Metric.mem_ball]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hev : (fun z => -(deriv f z / f z)) =ᶠ[𝓝 s] fun z => -(∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)) - H z`.

Establish `hn : Metric.ball z₀ (r / 6) \ (Z : Set ℂ) ∈ 𝓝 s` using `(Metric.isOpen_ball.sdiff Z.finite_toSet.isClosed).mem_nhds ⟨hsU, hsZ⟩`. Use `filter_upwards [hn] with z hz`. Rewrite using `[hHe z hz]`. Expand and normalize the polynomial expressions, which then agree. Establish `hHan : AnalyticAt ℂ H s` using `hHd.analyticAt (Metric.isOpen_ball.mem_nhds hsU)`.

Establish `hcd : ∀ ρ ∈ Z, ContDiffAt ℂ k (fun z => (m ρ : ℂ) / (z - ρ)) s` using `fun ρ hρ => contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) (sub_ne_zero.2 (fun h => hsZ (h ▸ Finset.mem_coe.2 hρ)))`. Establish `hkey : ‖iteratedDeriv k H s‖ ≤ k.factorial * (72 * Real.log B / r) / (r / 12) ^ k`. Establish `h2 : 2 * (r / 12) = r / 6` using `by ring`. Conclude with `dhc_cauchy H z₀ s (r / 12) _ (by positivity) (h2 ▸ hHd) (h2 ▸ hHb) hs k`. Establish `hfac : (k.factorial : ℂ) ≠ 0` using `by exact_mod_cast k.factorial_ne_zero`.

Establish `hpm : ((-1 : ℂ) ^ k * (-1) ^ k) = 1` using `by rw [← mul_pow]; simp`. Rewrite using `[hev.iteratedDeriv_eq k, iteratedDeriv_fun_sub (ContDiffAt.neg (ContDiffAt.sum hcd)) hHan.contDiffAt, iteratedDeriv_fun_neg, iteratedDeriv_fun_sum hcd]`. Repeatedly rewrite using `[dhc_iter]`. Establish `he : (-1 : ℂ) ^ k / (k.factorial : ℂ) * (-∑ ρ ∈ Z, (m ρ : ℂ) * ((-1) ^ k * (k.factorial : ℂ)) * ((s - ρ) ^ (k + 1))⁻¹ - iteratedDeriv k H s) + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) = -((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k H s)`. Establish `: ∑ ρ ∈ Z, (m ρ : ℂ) * ((-1) ^ k * (k.factorial : ℂ)) * ((s - ρ) ^ (k + 1))⁻¹ = ((-1) ^ k * (k.factorial : ℂ)) * ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun ρ _ => ?_)` and prove the remaining obligations. Rewrite using `[div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Generalize the expression as in `(∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)) = S`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(-(k.factorial : ℂ) * S) * hpm`. Rewrite using `[he, norm_neg, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]`. Establish `hfr : (0 : ℝ) < k.factorial` using `by exact_mod_cast k.factorial_pos`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_pow, div_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem deuring_heilbronn_cauchy : DHCauchy := by
  intro f z₀ r B hr hB hfd hf0 hfb
  obtain ⟨Z, m, hZ, hm1, -, -, hsum, hbd⟩ := landau_local3 f z₀ r B hr hB hfd hf0 hfb
  refine ⟨Z, m, hZ, hm1, hsum, ?_⟩
  have hfan : ∀ z ∈ Metric.ball z₀ (r / 6), AnalyticAt ℂ f z := fun z hz =>
    (hfd.mono Metric.ball_subset_closedBall).analyticAt
      (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball (by linarith) hz))
  have hnz : ∀ z ∈ Metric.ball z₀ (r / 6) \ (Z : Set ℂ), f z ≠ 0 := fun z hz h0 =>
    hz.2 (Finset.mem_coe.2 ((hZ z).2
      ⟨Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hz.1), h0⟩))
  have hGd : DifferentiableOn ℂ (fun z => deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ))
      (Metric.ball z₀ (r / 6) \ (Z : Set ℂ)) := by
    intro z hz
    have h1 := hfan z hz.1
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (h1.deriv.differentiableAt.div h1.differentiableAt (hnz z hz)).sub ?_
    refine DifferentiableAt.fun_sum (fun ρ hρ => ?_)
    exact (differentiableAt_const _).div (differentiableAt_id.sub_const ρ)
      (sub_ne_zero.2 (fun h => hz.2 (h ▸ Finset.mem_coe.2 hρ)))
  obtain ⟨H, hHd, hHe, hHb⟩ := dhc_removable Z _ _ (72 * Real.log B / r) Metric.isOpen_ball hGd
    (fun z hz => hbd z (Metric.ball_subset_closedBall hz.1) (hnz z hz))
  intro k s hs hfs
  have hsZ : s ∉ (Z : Set ℂ) := fun h => hfs ((hZ s).1 (Finset.mem_coe.1 h)).2
  have hsU : s ∈ Metric.ball z₀ (r / 6) := by
    rw [Metric.mem_closedBall] at hs
    rw [Metric.mem_ball]
    linarith
  have hev : (fun z => -(deriv f z / f z)) =ᶠ[𝓝 s]
      fun z => -(∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)) - H z := by
    have hn : Metric.ball z₀ (r / 6) \ (Z : Set ℂ) ∈ 𝓝 s :=
      (Metric.isOpen_ball.sdiff Z.finite_toSet.isClosed).mem_nhds ⟨hsU, hsZ⟩
    filter_upwards [hn] with z hz
    rw [hHe z hz]
    ring
  have hHan : AnalyticAt ℂ H s := hHd.analyticAt (Metric.isOpen_ball.mem_nhds hsU)
  have hcd : ∀ ρ ∈ Z, ContDiffAt ℂ k (fun z => (m ρ : ℂ) / (z - ρ)) s := fun ρ hρ =>
    contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const)
      (sub_ne_zero.2 (fun h => hsZ (h ▸ Finset.mem_coe.2 hρ)))
  have hkey : ‖iteratedDeriv k H s‖ ≤ k.factorial * (72 * Real.log B / r) / (r / 12) ^ k := by
    have h2 : 2 * (r / 12) = r / 6 := by ring
    exact dhc_cauchy H z₀ s (r / 12) _ (by positivity) (h2 ▸ hHd) (h2 ▸ hHb) hs k
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hpm : ((-1 : ℂ) ^ k * (-1) ^ k) = 1 := by rw [← mul_pow]; simp
  rw [hev.iteratedDeriv_eq k, iteratedDeriv_fun_sub (ContDiffAt.neg (ContDiffAt.sum hcd)) hHan.contDiffAt,
    iteratedDeriv_fun_neg, iteratedDeriv_fun_sum hcd]
  simp_rw [dhc_iter]
  have he : (-1 : ℂ) ^ k / (k.factorial : ℂ) *
        (-∑ ρ ∈ Z, (m ρ : ℂ) * ((-1) ^ k * (k.factorial : ℂ)) * ((s - ρ) ^ (k + 1))⁻¹ -
          iteratedDeriv k H s) + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) =
      -((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k H s) := by
    have : ∑ ρ ∈ Z, (m ρ : ℂ) * ((-1) ^ k * (k.factorial : ℂ)) * ((s - ρ) ^ (k + 1))⁻¹ =
        ((-1) ^ k * (k.factorial : ℂ)) * ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      rw [div_eq_mul_inv]
      ring
    rw [this]
    generalize (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)) = S
    field_simp
    linear_combination (-(k.factorial : ℂ) * S) * hpm
  rw [he, norm_neg, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
  have hfr : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  calc 1 / (k.factorial : ℝ) * ‖iteratedDeriv k H s‖
      ≤ 1 / (k.factorial : ℝ) * (k.factorial * (72 * Real.log B / r) / (r / 12) ^ k) := by gcongr
    _ = 72 * Real.log B / r * (12 / r) ^ k := by
      rw [div_pow, div_pow]
      field_simp

end Formalism.HermitianLattices.Ext.PrimesInProgressions
