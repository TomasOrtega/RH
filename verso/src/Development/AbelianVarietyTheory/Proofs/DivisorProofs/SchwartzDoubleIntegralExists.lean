import Mathlib
open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[integral_smul, norm_smul, Real.norm_of_nonneg hc]`. Use `_ ≤ ∫ k, B k ∂μ := norm_integral_le_of_norm_le hB (Filter.Eventually.of_forall fun k => by rw [norm_smul, Real.norm_of_nonneg hc]; exact h k)`.
-/
theorem mul_norm_integral_le_of_mul_norm_le {α E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α) (f : α → E) (B : α → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (hB : Integrable B μ) (h : ∀ k, c * ‖f k‖ ≤ B k) :
    c * ‖∫ k, f k ∂μ‖ ≤ ∫ k, B k ∂μ := by
  calc c * ‖∫ k, f k ∂μ‖ = ‖∫ k, c • f k ∂μ‖ := by
        rw [integral_smul, norm_smul, Real.norm_of_nonneg hc]
    _ ≤ ∫ k, B k ∂μ := norm_integral_le_of_norm_le hB
        (Filter.Eventually.of_forall fun k => by rw [norm_smul, Real.norm_of_nonneg hc]; exact h k)

/- English proof (translation)
Establish `hint : ∀ m t, Integrable (fun k => iteratedFDeriv ℝ m (F k) t) μ`. Introduce `m t`. Take `⟨B, hBi, hB⟩` from `hbd 0 m`. Use `hBi.mono' (hmeas m t) (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Simplify using `using hB k t`.

Establish `hdiff : ∀ m k, Differentiable ℝ (iteratedFDeriv ℝ m (F k))` using `fun m k => (F k).smooth'.differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top m)`. Establish `hder : ∀ m t, HasFDerivAt (fun t => ∫ k, iteratedFDeriv ℝ m (F k) t ∂μ) (∫ k, fderiv ℝ (iteratedFDeriv ℝ m (F k)) t ∂μ) t`. Introduce `m t`. Take `⟨B, hBi, hB⟩` from `hbd 0 (m + 1)`. Use `hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Set.univ) (F' := fun x k => fderiv ℝ (iteratedFDeriv ℝ m (F k)) x) (bound := B) Filter.univ_mem (Filter.Eventually.of_forall fun x => hmeas m x) (hint m t) ?_ ?_ hBi ?_` and prove the remaining obligations.

Establish `: (fun k => fderiv ℝ (iteratedFDeriv ℝ m (F k)) t) = fun k => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => V) ℂ) (iteratedFDeriv ℝ (m + 1) (F k) t)`. Use function extensionality and compare the values at `k`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `(LinearIsometryEquiv.continuous _).comp_aestronglyMeasurable (hmeas (m + 1) t)`.

Conclude with `Filter.Eventually.of_forall fun k x _ => by`. Rewrite using `[norm_fderiv_iteratedFDeriv (𝕜 := ℝ)]`. Simplify using `using hB k x`. Conclude with `Filter.Eventually.of_forall fun k x _ => (hdiff m k x).hasFDerivAt`. Use `set g0 : V → ℂ := fun t => ∫ k, F k t ∂μ with hg0`.

Establish `hiter : ∀ m : ℕ, iteratedFDeriv ℝ m g0 = fun t => ∫ k, iteratedFDeriv ℝ m (F k) t ∂μ`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Use function extensionality and compare the values at `t`.

Conclude with `((continuousMultilinearCurryFin0 ℝ V ℂ).symm.toContinuousLinearEquiv.integral_comp_comm (fun k => F k t)).symm`. Consider the case `succ m ih`. Use function extensionality and compare the values at `t`. Rewrite using `[iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih, (hder m t).fderiv]`. Conclude with `((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => V) ℂ).symm.toContinuousLinearEquiv.integral_comp_comm (fun k => fderiv ℝ (iteratedFDeriv ℝ m (F k)) t)).symm`.

Establish `hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g0` using `contDiff_of_differentiable_iteratedFDeriv fun m _ => by`. Rewrite using `[hiter m]`. Conclude with `fun t => (hder m t).differentiableAt`. Establish `hdecay : ∀ n m : ℕ, ∃ C, ∀ x, ‖x‖ ^ n * ‖iteratedFDeriv ℝ m g0 x‖ ≤ C`. Introduce `n m`.

Take `⟨B, hBi, hB⟩` from `hbd n m`. Use `⟨∫ k, B k ∂μ, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hiter m]`. Conclude with `mul_norm_integral_le_of_mul_norm_le μ _ B _ (by positivity) hBi fun k => hB k x`. Conclude with `⟨⟨g0, hsmooth, hdecay⟩, fun t => rfl, fun m t => congrFun (hiter m) t⟩`.
-/
theorem schwartz_integral_of_dominated {V α : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace α] (μ : Measure α) (F : α → SchwartzMap V ℂ)
    (hmeas : ∀ (m : ℕ) (t : V), AEStronglyMeasurable (fun k => iteratedFDeriv ℝ m (F k) t) μ)
    (hbd : ∀ n m : ℕ, ∃ Bd : α → ℝ, Integrable Bd μ ∧
      ∀ k t, ‖t‖ ^ n * ‖iteratedFDeriv ℝ m (F k) t‖ ≤ Bd k) :
    ∃ g : SchwartzMap V ℂ, (∀ t, g t = ∫ k, F k t ∂μ) ∧
      ∀ m t, iteratedFDeriv ℝ m g t = ∫ k, iteratedFDeriv ℝ m (F k) t ∂μ := by
  have hint : ∀ m t, Integrable (fun k => iteratedFDeriv ℝ m (F k) t) μ := by
    intro m t
    obtain ⟨B, hBi, hB⟩ := hbd 0 m
    refine hBi.mono' (hmeas m t) (Filter.Eventually.of_forall fun k => ?_)
    simpa using hB k t
  have hdiff : ∀ m k, Differentiable ℝ (iteratedFDeriv ℝ m (F k)) := fun m k =>
    (F k).smooth'.differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top m)
  have hder : ∀ m t, HasFDerivAt (fun t => ∫ k, iteratedFDeriv ℝ m (F k) t ∂μ)
      (∫ k, fderiv ℝ (iteratedFDeriv ℝ m (F k)) t ∂μ) t := by
    intro m t
    obtain ⟨B, hBi, hB⟩ := hbd 0 (m + 1)
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Set.univ)
      (F' := fun x k => fderiv ℝ (iteratedFDeriv ℝ m (F k)) x) (bound := B)
      Filter.univ_mem (Filter.Eventually.of_forall fun x => hmeas m x) (hint m t) ?_ ?_ hBi ?_
    · have : (fun k => fderiv ℝ (iteratedFDeriv ℝ m (F k)) t) = fun k =>
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => V) ℂ)
            (iteratedFDeriv ℝ (m + 1) (F k) t) := by
        funext k; rfl
      rw [this]
      exact (LinearIsometryEquiv.continuous _).comp_aestronglyMeasurable (hmeas (m + 1) t)
    · exact Filter.Eventually.of_forall fun k x _ => by
        rw [norm_fderiv_iteratedFDeriv (𝕜 := ℝ)]; simpa using hB k x
    · exact Filter.Eventually.of_forall fun k x _ => (hdiff m k x).hasFDerivAt
  set g0 : V → ℂ := fun t => ∫ k, F k t ∂μ with hg0
  have hiter : ∀ m : ℕ, iteratedFDeriv ℝ m g0 = fun t => ∫ k, iteratedFDeriv ℝ m (F k) t ∂μ := by
    intro m
    induction m with
    | zero =>
      funext t
      exact ((continuousMultilinearCurryFin0 ℝ V ℂ).symm.toContinuousLinearEquiv.integral_comp_comm
        (fun k => F k t)).symm
    | succ m ih =>
      funext t
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih, (hder m t).fderiv]
      exact ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => V) ℂ).symm.toContinuousLinearEquiv.integral_comp_comm
        (fun k => fderiv ℝ (iteratedFDeriv ℝ m (F k)) t)).symm
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g0 :=
    contDiff_of_differentiable_iteratedFDeriv fun m _ => by
      rw [hiter m]; exact fun t => (hder m t).differentiableAt
  have hdecay : ∀ n m : ℕ, ∃ C, ∀ x, ‖x‖ ^ n * ‖iteratedFDeriv ℝ m g0 x‖ ≤ C := by
    intro n m
    obtain ⟨B, hBi, hB⟩ := hbd n m
    refine ⟨∫ k, B k ∂μ, fun x => ?_⟩
    rw [hiter m]
    exact mul_norm_integral_le_of_mul_norm_le μ _ B _ (by positivity) hBi fun k => hB k x
  exact ⟨⟨g0, hsmooth, hdecay⟩, fun t => rfl, fun m t => congrFun (hiter m) t⟩

/- English proof (translation)
Introduce `V _ _ α β _ _ μα μβ Fm h1 h2 hb`. Establish `hin : ∀ k, ∃ g : SchwartzMap V ℂ, (∀ t, g t = ∫ l, Fm k l t ∂μβ) ∧ ∀ m t, iteratedFDeriv ℝ m g t = ∫ l, iteratedFDeriv ℝ m (Fm k l) t ∂μβ`. Introduce `k`. Use `schwartz_integral_of_dominated μβ (Fm k) (fun m t => h1 m t k) fun n m => ?_` and prove the remaining obligations. Take `⟨Bd, hBi, -, hB⟩` from `hb n m`.

Conclude with `⟨Bd k, hBi k, fun l t => hB k l t⟩`. Use `choose g hg0 hg using hin`. Take `⟨h, hh0, -⟩` from `schwartz_integral_of_dominated μα g (fun m t => by`. Establish `: (fun k => iteratedFDeriv ℝ m (g k) t) = fun k => ∫ l, iteratedFDeriv ℝ m (Fm k l) t ∂μβ`. Use function extensionality and compare the values at `k`.

Conclude with `hg k m t`. Rewrite using `[this]`. Conclude with `h2 m t)`. Use the proof step `(fun n m => by`. Take `⟨Bd, hBi, hBi2, hB⟩` from `hb n m`.

Use `⟨fun k => ∫ l, Bd k l ∂μβ, hBi2, fun k t => ?_⟩` and prove the remaining obligations. Rewrite using `[hg k m t]`. Conclude with `mul_norm_integral_le_of_mul_norm_le μβ _ (Bd k) _ (by positivity) (hBi k) fun l => hB k l t)`. Conclude with `⟨h, fun t => by rw [hh0]; simp only [hg0]⟩`.
-/
theorem schwartz_iterated_integral_of_dominated :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {α β : Type} [MeasurableSpace α]
    [MeasurableSpace β] (μα : Measure α) (μβ : Measure β) (Fm : α → β → SchwartzMap V ℂ),
    (∀ (m : ℕ) (t : V) (k : α), AEStronglyMeasurable (fun l => iteratedFDeriv ℝ m (Fm k l) t) μβ) →
    (∀ (m : ℕ) (t : V), AEStronglyMeasurable (fun k => ∫ l, iteratedFDeriv ℝ m (Fm k l) t ∂μβ) μα) →
    (∀ n m : ℕ, ∃ Bd : α → β → ℝ, (∀ k, Integrable (Bd k) μβ) ∧
      Integrable (fun k => ∫ l, Bd k l ∂μβ) μα ∧
      ∀ k l t, ‖t‖ ^ n * ‖iteratedFDeriv ℝ m (Fm k l) t‖ ≤ Bd k l) →
    ∃ g : SchwartzMap V ℂ, ∀ t, g t = ∫ k, ∫ l, Fm k l t ∂μβ ∂μα := by
  intro V _ _ α β _ _ μα μβ Fm h1 h2 hb
  have hin : ∀ k, ∃ g : SchwartzMap V ℂ, (∀ t, g t = ∫ l, Fm k l t ∂μβ) ∧
      ∀ m t, iteratedFDeriv ℝ m g t = ∫ l, iteratedFDeriv ℝ m (Fm k l) t ∂μβ := by
    intro k
    refine schwartz_integral_of_dominated μβ (Fm k) (fun m t => h1 m t k) fun n m => ?_
    obtain ⟨Bd, hBi, -, hB⟩ := hb n m
    exact ⟨Bd k, hBi k, fun l t => hB k l t⟩
  choose g hg0 hg using hin
  obtain ⟨h, hh0, -⟩ := schwartz_integral_of_dominated μα g
    (fun m t => by
      have : (fun k => iteratedFDeriv ℝ m (g k) t) =
          fun k => ∫ l, iteratedFDeriv ℝ m (Fm k l) t ∂μβ := by
        funext k; exact hg k m t
      rw [this]; exact h2 m t)
    (fun n m => by
      obtain ⟨Bd, hBi, hBi2, hB⟩ := hb n m
      refine ⟨fun k => ∫ l, Bd k l ∂μβ, hBi2, fun k t => ?_⟩
      rw [hg k m t]
      exact mul_norm_integral_le_of_mul_norm_le μβ _ (Bd k) _ (by positivity) (hBi k)
        fun l => hB k l t)
  exact ⟨h, fun t => by rw [hh0]; simp only [hg0]⟩

end GlobalTheory
