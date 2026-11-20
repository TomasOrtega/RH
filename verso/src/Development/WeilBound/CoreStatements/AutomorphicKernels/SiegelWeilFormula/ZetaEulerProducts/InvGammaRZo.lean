import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.MeromorphicAtProd

open Filter Topology Complex
open scoped Real

namespace PositivityTheory.Lord

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Use `⟨fun z => (Complex.Gamma (z + 1))⁻¹, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hd : Differentiable ℂ fun z : ℂ => (Complex.Gamma (z + 1))⁻¹`. Introduce `z`.

Establish `h` using `(Complex.differentiable_one_div_Gamma (z + 1)).comp z (differentiableAt_id.add_const (1 : ℂ))`. Conclude with `h.congr_of_eventuallyEq (Eventually.of_forall fun w => by simp)`. Conclude with `hd.analyticAt _`. Simplify using the standard rewrite rules. Use `filter_upwards [self_mem_nhdsWithin] with z hz`.

Establish `hz0 : z ≠ 0` using `by simpa using hz`. Rewrite using `[Complex.Gamma_add_one z hz0, mul_inv, ← mul_assoc]`. Simplify using `[hz0]`. Consider the case `succ n ih`. Take `⟨u, hu, hu0, he⟩` from `ih`.

Establish `hx : (-((n + 1 : ℕ) : ℂ)) + 1 = -(n : ℂ)` using `by push_cast; ring`. Use `⟨fun z => z * u (z + 1), ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : AnalyticAt ℂ (fun z : ℂ => z + 1) (-((n + 1 : ℕ) : ℂ))` using `analyticAt_id.add analyticAt_const`. Conclude with `analyticAt_id.mul (hu.comp_of_eq h1 hx)`. Simplify using `only [hx]`.

Use `mul_ne_zero ?_ hu0` and prove the remaining obligations. Rewrite using `[neg_ne_zero]`. Conclude with `Nat.succ_ne_zero n` after adjusting the coercions. Establish `ht : Tendsto (fun z : ℂ => z + 1) (𝓝[≠] (-((n + 1 : ℕ) : ℂ))) (𝓝[≠] (-(n : ℂ)))`. Apply `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within` to reduce the goal to its premises.

Establish `hc : Continuous fun z : ℂ => z + 1` using `continuous_id.add continuous_const`. Use `(hc.tendsto (-((n + 1 : ℕ) : ℂ))).mono_left (nhdsWithin_le_nhds (s := {(-((n + 1 : ℕ) : ℂ))}ᶜ))` as an intermediate fact. Simplify `this` using `only [hx]`. Use `filter_upwards [self_mem_nhdsWithin] with z hz`. Introduce `h`.

Apply `hz` to reduce the goal to its premises. Establish `: z = -(n : ℂ) - 1` using `by rw [← h]; ring`. Rewrite using `[Set.mem_singleton_iff, this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `h0 : ∀ᶠ z in 𝓝[≠] (-((n + 1 : ℕ) : ℂ)), z ≠ 0`. Use `eventually_nhdsWithin_of_eventually_nhds (isOpen_compl_singleton.mem_nhds ?_)` and prove the remaining obligations. Rewrite using `[Set.mem_compl_singleton_iff, neg_ne_zero]`. Conclude with `Nat.succ_ne_zero n` after adjusting the coercions. Use `filter_upwards [ht.eventually he, h0] with z h1 h2`.

Establish `hg : (Complex.Gamma z)⁻¹ = z * (Complex.Gamma (z + 1))⁻¹`. Rewrite using `[Complex.Gamma_add_one z h2, mul_inv, ← mul_assoc, mul_inv_cancel₀ h2, one_mul]`. Rewrite using `[hg, h1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem invGamma_zo (n : ℕ) : ZO (fun z => (Complex.Gamma z)⁻¹) (-(n : ℂ)) 1 := by
  induction n with
  | zero =>
    refine ⟨fun z => (Complex.Gamma (z + 1))⁻¹, ?_, ?_, ?_⟩
    · have hd : Differentiable ℂ fun z : ℂ => (Complex.Gamma (z + 1))⁻¹ := by
        intro z
        have h := (Complex.differentiable_one_div_Gamma (z + 1)).comp z (differentiableAt_id.add_const (1 : ℂ))
        exact h.congr_of_eventuallyEq (Eventually.of_forall fun w => by simp)
      exact hd.analyticAt _
    · simp
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hz0 : z ≠ 0 := by simpa using hz
      rw [Complex.Gamma_add_one z hz0, mul_inv, ← mul_assoc]
      simp [hz0]
  | succ n ih =>
    obtain ⟨u, hu, hu0, he⟩ := ih
    have hx : (-((n + 1 : ℕ) : ℂ)) + 1 = -(n : ℂ) := by push_cast; ring
    refine ⟨fun z => z * u (z + 1), ?_, ?_, ?_⟩
    · have h1 : AnalyticAt ℂ (fun z : ℂ => z + 1) (-((n + 1 : ℕ) : ℂ)) :=
        analyticAt_id.add analyticAt_const
      exact analyticAt_id.mul (hu.comp_of_eq h1 hx)
    · simp only [hx]
      refine mul_ne_zero ?_ hu0
      rw [neg_ne_zero]
      exact_mod_cast Nat.succ_ne_zero n
    · have ht : Tendsto (fun z : ℂ => z + 1) (𝓝[≠] (-((n + 1 : ℕ) : ℂ))) (𝓝[≠] (-(n : ℂ))) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have hc : Continuous fun z : ℂ => z + 1 := continuous_id.add continuous_const
          have := (hc.tendsto (-((n + 1 : ℕ) : ℂ))).mono_left (nhdsWithin_le_nhds (s := {(-((n + 1 : ℕ) : ℂ))}ᶜ))
          simpa only [hx] using this
        · filter_upwards [self_mem_nhdsWithin] with z hz
          intro h
          apply hz
          have : z = -(n : ℂ) - 1 := by rw [← h]; ring
          rw [Set.mem_singleton_iff, this]; push_cast; ring
      have h0 : ∀ᶠ z in 𝓝[≠] (-((n + 1 : ℕ) : ℂ)), z ≠ 0 := by
        refine eventually_nhdsWithin_of_eventually_nhds (isOpen_compl_singleton.mem_nhds ?_)
        rw [Set.mem_compl_singleton_iff, neg_ne_zero]
        exact_mod_cast Nat.succ_ne_zero n
      filter_upwards [ht.eventually he, h0] with z h1 h2
      have hg : (Complex.Gamma z)⁻¹ = z * (Complex.Gamma (z + 1))⁻¹ := by
        rw [Complex.Gamma_add_one z h2, mul_inv, ← mul_assoc, mul_inv_cancel₀ h2, one_mul]
      rw [hg, h1]
      push_cast
      ring

/- English proof (translation)
Use `split_ifs with he`. Take `⟨m, hm⟩` from `he`. Take `⟨n, hn⟩ : ∃ n : ℕ, m = -(n : ℤ)` from `⟨m.natAbs, by omega⟩`. Take `⟨u, hu, hu0, hue⟩` from `invGamma_zo n`. Establish `hjn : (j : ℂ) = -(2 * (n : ℂ))` using `by rw [hm, hn]; push_cast; ring`.

Establish `hpi : (π : ℂ) ≠ 0` using `ofReal_ne_zero.2 Real.pi_ne_zero`. Use `⟨fun s => ((π : ℂ) ^ (-s / 2))⁻¹ * u (s / 2) / 2, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : AnalyticAt ℂ (fun s : ℂ => ((π : ℂ) ^ (-s / 2))⁻¹) (j : ℂ)`. Establish `hd : Differentiable ℂ fun s : ℂ => (π : ℂ) ^ (-s / 2)` using `fun s => ((differentiableAt_id.neg).div_const 2).const_cpow (Or.inl hpi)`. Conclude with `(hd.analyticAt _).inv (by rw [Ne, cpow_eq_zero_iff]; tauto)`.

Establish `h2 : AnalyticAt ℂ (fun s : ℂ => u (s / 2)) (j : ℂ)`. Establish `hc : AnalyticAt ℂ (fun s : ℂ => s / 2) (j : ℂ)` using `analyticAt_id.div_const`. Conclude with `hu.comp_of_eq hc (by rw [hjn]; ring)`. Conclude with `(h1.mul h2).div_const`. Simplify using `only`.

Establish `: (j : ℂ) / 2 = -(n : ℂ)` using `by rw [hjn]; ring`. Rewrite using `[this]`. Use `div_ne_zero (mul_ne_zero (inv_ne_zero ?_) hu0) two_ne_zero` and prove the remaining obligations. Rewrite using `[Ne, cpow_eq_zero_iff]`. The claim follows by propositional logic.

Establish `ht : Tendsto (fun s : ℂ => s / 2) (𝓝[≠] (j : ℂ)) (𝓝[≠] (-(n : ℂ)))`. Apply `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within` to reduce the goal to its premises. Establish `hc : Continuous fun s : ℂ => s / 2` using `continuous_id.div_const 2`. Use `(hc.tendsto (j : ℂ)).mono_left (nhdsWithin_le_nhds (s := {(j : ℂ)}ᶜ))` as an intermediate fact. Establish `e : (j : ℂ) / 2 = -(n : ℂ)` using `by rw [hjn]; ring`.

Simplify `this` using `only [e]`. Use `filter_upwards [self_mem_nhdsWithin] with s hs`. Introduce `h`. Apply `hs` to reduce the goal to its premises. Establish `: s = 2 * (-(n : ℂ))` using `by rw [← h]; ring`.

Rewrite using `[Set.mem_singleton_iff, this, hjn]`. Expand and normalize the polynomial expressions, which then agree. Use `filter_upwards [ht.eventually hue] with s h1`. Rewrite using `[Gammaℝ_def, mul_inv, h1, hjn]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hd : Differentiable ℂ fun s => (Gammaℝ s)⁻¹` using `differentiable_Gammaℝ_inv`. Use `⟨fun s => (Gammaℝ s)⁻¹, hd.analyticAt _, inv_ne_zero fun h => he ?_, Eventually.of_forall fun s => by simp⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `Gammaℝ_eq_zero_iff.1 h`. Use `⟨-(n : ℤ), ?_⟩` and prove the remaining obligations. Establish `: ((j : ℤ) : ℂ) = ((-(n : ℤ) + -(n : ℤ) : ℤ) : ℂ)` using `by rw [hn]; push_cast; ring`.

Conclude with `this` after adjusting the coercions.
-/
theorem invGammaR_zo (j : ℤ) (hj : j ≤ 0) :
    ZO (fun s => (Gammaℝ s)⁻¹) (j : ℂ) (if Even j then 1 else 0) := by
  split_ifs with he
  · obtain ⟨m, hm⟩ := he
    obtain ⟨n, hn⟩ : ∃ n : ℕ, m = -(n : ℤ) := ⟨m.natAbs, by omega⟩
    obtain ⟨u, hu, hu0, hue⟩ := invGamma_zo n
    have hjn : (j : ℂ) = -(2 * (n : ℂ)) := by rw [hm, hn]; push_cast; ring
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    refine ⟨fun s => ((π : ℂ) ^ (-s / 2))⁻¹ * u (s / 2) / 2, ?_, ?_, ?_⟩
    · have h1 : AnalyticAt ℂ (fun s : ℂ => ((π : ℂ) ^ (-s / 2))⁻¹) (j : ℂ) := by
        have hd : Differentiable ℂ fun s : ℂ => (π : ℂ) ^ (-s / 2) :=
          fun s => ((differentiableAt_id.neg).div_const 2).const_cpow (Or.inl hpi)
        exact (hd.analyticAt _).inv (by rw [Ne, cpow_eq_zero_iff]; tauto)
      have h2 : AnalyticAt ℂ (fun s : ℂ => u (s / 2)) (j : ℂ) := by
        have hc : AnalyticAt ℂ (fun s : ℂ => s / 2) (j : ℂ) := analyticAt_id.div_const
        exact hu.comp_of_eq hc (by rw [hjn]; ring)
      exact (h1.mul h2).div_const
    · simp only
      have : (j : ℂ) / 2 = -(n : ℂ) := by rw [hjn]; ring
      rw [this]
      refine div_ne_zero (mul_ne_zero (inv_ne_zero ?_) hu0) two_ne_zero
      rw [Ne, cpow_eq_zero_iff]; tauto
    · have ht : Tendsto (fun s : ℂ => s / 2) (𝓝[≠] (j : ℂ)) (𝓝[≠] (-(n : ℂ))) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have hc : Continuous fun s : ℂ => s / 2 := continuous_id.div_const 2
          have := (hc.tendsto (j : ℂ)).mono_left (nhdsWithin_le_nhds (s := {(j : ℂ)}ᶜ))
          have e : (j : ℂ) / 2 = -(n : ℂ) := by rw [hjn]; ring
          simpa only [e] using this
        · filter_upwards [self_mem_nhdsWithin] with s hs
          intro h
          apply hs
          have : s = 2 * (-(n : ℂ)) := by rw [← h]; ring
          rw [Set.mem_singleton_iff, this, hjn]; ring
      filter_upwards [ht.eventually hue] with s h1
      rw [Gammaℝ_def, mul_inv, h1, hjn]
      ring
  · have hd : Differentiable ℂ fun s => (Gammaℝ s)⁻¹ := differentiable_Gammaℝ_inv
    refine ⟨fun s => (Gammaℝ s)⁻¹, hd.analyticAt _, inv_ne_zero fun h => he ?_,
      Eventually.of_forall fun s => by simp⟩
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.1 h
    refine ⟨-(n : ℤ), ?_⟩
    have : ((j : ℤ) : ℂ) = ((-(n : ℤ) + -(n : ℤ) : ℤ) : ℂ) := by rw [hn]; push_cast; ring
    exact_mod_cast this

/- English proof (translation)
Take `⟨n, hn⟩ : ∃ n : ℕ, j = -(n : ℤ)` from `⟨j.natAbs, by omega⟩`. Take `⟨u, hu, hu0, hue⟩` from `invGamma_zo n`. Establish `hjn : (j : ℂ) = -(n : ℂ)` using `by rw [hn]; push_cast; ring`. Establish `h2pi : (2 * (π : ℂ)) ≠ 0` using `mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)`. Use `⟨fun s => (2 * (2 * (π : ℂ)) ^ (-s))⁻¹ * u s, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `hd : Differentiable ℂ fun s : ℂ => 2 * (2 * (π : ℂ)) ^ (-s)` using `fun s => (differentiableAt_id.neg.const_cpow (Or.inl h2pi)).const_mul 2`. Use `((hd.analyticAt _).inv ?_).mul (by rw [hjn]; exact hu)` and prove the remaining obligations. Conclude with `mul_ne_zero two_ne_zero (by rw [Ne, cpow_eq_zero_iff]; tauto)`. Simplify using `only`. Rewrite using `[hjn]`.

Use `mul_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero ?_)) hu0` and prove the remaining obligations. Rewrite using `[Ne, cpow_eq_zero_iff]`. The claim follows by propositional logic. Rewrite using `[hjn] filter_upwards [hue] with s h1`. Rewrite using `[Gammaℂ_def, mul_inv, h1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem invGammaC_zo (j : ℤ) (hj : j ≤ 0) : ZO (fun s => (Gammaℂ s)⁻¹) (j : ℂ) 1 := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨j.natAbs, by omega⟩
  obtain ⟨u, hu, hu0, hue⟩ := invGamma_zo n
  have hjn : (j : ℂ) = -(n : ℂ) := by rw [hn]; push_cast; ring
  have h2pi : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)
  refine ⟨fun s => (2 * (2 * (π : ℂ)) ^ (-s))⁻¹ * u s, ?_, ?_, ?_⟩
  · have hd : Differentiable ℂ fun s : ℂ => 2 * (2 * (π : ℂ)) ^ (-s) :=
      fun s => (differentiableAt_id.neg.const_cpow (Or.inl h2pi)).const_mul 2
    refine ((hd.analyticAt _).inv ?_).mul (by rw [hjn]; exact hu)
    exact mul_ne_zero two_ne_zero (by rw [Ne, cpow_eq_zero_iff]; tauto)
  · simp only
    rw [hjn]
    refine mul_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero ?_)) hu0
    rw [Ne, cpow_eq_zero_iff]; tauto
  · rw [hjn]
    filter_upwards [hue] with s h1
    rw [Gammaℂ_def, mul_inv, h1]
    ring

end PositivityTheory.Lord
