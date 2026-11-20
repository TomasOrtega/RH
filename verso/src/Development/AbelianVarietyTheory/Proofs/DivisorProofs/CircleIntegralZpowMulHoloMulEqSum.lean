import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
namespace GlobalTheory

/- English proof (translation)
Establish `hs₀V : V ∈ 𝓝 s₀` using `hV.mem_nhds (hball (Metric.mem_closedBall_self hr.le))`. Establish `hsph : ∀ z ∈ Metric.sphere s₀ r, z - s₀ ≠ 0`. Introduce `z hz h`. Rewrite `hz` using `[Metric.mem_sphere, dist_eq_norm, h, norm_zero]`. Conclude with `hr.ne hz`.

Establish `hzpow : ∀ k : ℤ, ContinuousOn (fun z : ℂ => (z - s₀) ^ k) (Metric.sphere s₀ r)`. Introduce `k`. Conclude with `((continuousOn_id.sub continuousOn_const)).zpow₀ k (fun z hz => Or.inl (hsph z hz))`. Establish `hsphV : Metric.sphere s₀ r ⊆ V` using `Metric.sphere_subset_closedBall.trans hball`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero`. Introduce `χ j hχ hn`. Use `⟨0, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[hn, Finset.sum_range_zero]`.

Establish `hj : 0 ≤ j` using `by omega`. Take `⟨m, rfl⟩` from `Int.eq_ofNat_of_zero_le hj`. Simplify using `only [zpow_natCast]`. Apply `DiffContOnCl.circleIntegral_eq_zero hr.le` to reduce the goal to its premises. Establish `hd : DifferentiableOn ℂ (fun z => (z - s₀) ^ m * (χ z * Φ z g)) V` using `(((differentiableOn_id.sub_const s₀).pow m)).mul (hχ.mul (hΦ g))`.

Conclude with `(hd.mono (Metric.closure_ball_subset_closedBall.trans hball)).diffContOnCl`. Consider the case `succ n ih`. Introduce `χ j hχ hn`. Establish `hχ' : DifferentiableOn ℂ (dslope χ s₀) V` using `(Complex.differentiableOn_dslope hs₀V).2 hχ`. Establish `hn' : (-(j + 1)).toNat = n` using `by omega`.

Take `⟨c', hc'⟩` from `ih (dslope χ s₀) (j + 1) hχ' hn'`. Use `⟨fun i => Nat.casesOn i (χ s₀) c', fun g => ?_⟩` and prove the remaining obligations. Establish `hcont : ContinuousOn (Φ · g) (Metric.sphere s₀ r)` using `(hΦ g).continuousOn.mono hsphV`. Establish `hcontχ' : ContinuousOn (dslope χ s₀) (Metric.sphere s₀ r)` using `hχ'.continuousOn.mono hsphV`. Establish `hsplit : circleIntegral (fun z => (z - s₀) ^ j * (χ z * Φ z g)) s₀ r = circleIntegral (fun z => χ s₀ * ((z - s₀) ^ j * Φ z g) + (z - s₀) ^ (j + 1) * (dslope χ s₀ z * Φ z g)) s₀ r`.

Apply `circleIntegral.integral_congr hr.le` to reduce the goal to its premises. Introduce `z hz`. Establish `h0` using `hsph z hz`. Establish `hχz : χ z = χ s₀ + (z - s₀) * dslope χ s₀ z`. Use `sub_smul_dslope χ s₀ z` as an intermediate fact.

Rewrite `this` using `[smul_eq_mul]`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only`. Rewrite using `[hχz, zpow_add_one₀ h0]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit, circleIntegral.integral_add, circleIntegral.integral_const_mul, hc' g, hn, hn', Finset.sum_range_succ']`. Rewrite using `[add_comm]`. Use `congr 1`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `i _`. Simplify using `only [Nat.cast_succ]`. Use `congr 2`. Use function extensionality and compare the values at `z`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Conclude with `ContinuousOn.circleIntegrable hr.le (continuousOn_const.mul ((hzpow j).mul hcont))`. Conclude with `ContinuousOn.circleIntegrable hr.le ((hzpow (j + 1)).mul (hcontχ'.mul hcont))`.
-/
theorem circleIntegral_zpow_mul_holo_sum {X : Type} (s₀ : ℂ) (r : ℝ) (V : Set ℂ)
    (Φ : ℂ → X → ℂ) (hr : 0 < r) (hV : IsOpen V) (hball : Metric.closedBall s₀ r ⊆ V)
    (hΦ : ∀ g, DifferentiableOn ℂ (Φ · g) V) :
    ∀ n : ℕ, ∀ (χ : ℂ → ℂ) (j : ℤ), DifferentiableOn ℂ χ V → (-j).toNat = n →
    ∃ c : ℕ → ℂ, ∀ g, circleIntegral (fun z => (z - s₀) ^ j * (χ z * Φ z g)) s₀ r =
      ∑ i ∈ Finset.range (-j).toNat, c i * circleIntegral (fun z => (z - s₀) ^ (j + i) * Φ z g) s₀ r := by
  have hs₀V : V ∈ 𝓝 s₀ := hV.mem_nhds (hball (Metric.mem_closedBall_self hr.le))
  have hsph : ∀ z ∈ Metric.sphere s₀ r, z - s₀ ≠ 0 := by
    intro z hz h
    rw [Metric.mem_sphere, dist_eq_norm, h, norm_zero] at hz
    exact hr.ne hz
  have hzpow : ∀ k : ℤ, ContinuousOn (fun z : ℂ => (z - s₀) ^ k) (Metric.sphere s₀ r) := by
    intro k
    exact ((continuousOn_id.sub continuousOn_const)).zpow₀ k (fun z hz => Or.inl (hsph z hz))
  have hsphV : Metric.sphere s₀ r ⊆ V := Metric.sphere_subset_closedBall.trans hball
  intro n
  induction n with
  | zero =>
    intro χ j hχ hn
    refine ⟨0, fun g => ?_⟩
    rw [hn, Finset.sum_range_zero]
    have hj : 0 ≤ j := by omega
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    simp only [zpow_natCast]
    apply DiffContOnCl.circleIntegral_eq_zero hr.le
    have hd : DifferentiableOn ℂ (fun z => (z - s₀) ^ m * (χ z * Φ z g)) V :=
      (((differentiableOn_id.sub_const s₀).pow m)).mul (hχ.mul (hΦ g))
    exact (hd.mono (Metric.closure_ball_subset_closedBall.trans hball)).diffContOnCl
  | succ n ih =>
    intro χ j hχ hn
    have hχ' : DifferentiableOn ℂ (dslope χ s₀) V := (Complex.differentiableOn_dslope hs₀V).2 hχ
    have hn' : (-(j + 1)).toNat = n := by omega
    obtain ⟨c', hc'⟩ := ih (dslope χ s₀) (j + 1) hχ' hn'
    refine ⟨fun i => Nat.casesOn i (χ s₀) c', fun g => ?_⟩
    have hcont : ContinuousOn (Φ · g) (Metric.sphere s₀ r) := (hΦ g).continuousOn.mono hsphV
    have hcontχ' : ContinuousOn (dslope χ s₀) (Metric.sphere s₀ r) := hχ'.continuousOn.mono hsphV
    have hsplit : circleIntegral (fun z => (z - s₀) ^ j * (χ z * Φ z g)) s₀ r =
        circleIntegral (fun z => χ s₀ * ((z - s₀) ^ j * Φ z g) +
          (z - s₀) ^ (j + 1) * (dslope χ s₀ z * Φ z g)) s₀ r := by
      apply circleIntegral.integral_congr hr.le
      intro z hz
      have h0 := hsph z hz
      have hχz : χ z = χ s₀ + (z - s₀) * dslope χ s₀ z := by
        have := sub_smul_dslope χ s₀ z
        rw [smul_eq_mul] at this
        rw [this]; ring
      simp only
      rw [hχz, zpow_add_one₀ h0]
      ring
    rw [hsplit, circleIntegral.integral_add, circleIntegral.integral_const_mul, hc' g, hn, hn',
      Finset.sum_range_succ']
    · rw [add_comm]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        simp only [Nat.cast_succ]
        congr 2
        funext z
        congr 2
        ring
      · simp
    · exact ContinuousOn.circleIntegrable hr.le
        (continuousOn_const.mul ((hzpow j).mul hcont))
    · exact ContinuousOn.circleIntegrable hr.le
        ((hzpow (j + 1)).mul (hcontχ'.mul hcont))

/- English proof (translation)
Introduce `hr hV hball hχ hΦ j` and use `circleIntegral_zpow_mul_holo_sum s₀ r V Φ hr hV hball hΦ _ χ j hχ rfl`.
-/
theorem circleIntegral_zpow_mul_holo_mul_eq_sum {X : Type} (s₀ : ℂ) (r : ℝ) (V : Set ℂ)
    (χ : ℂ → ℂ) (Φ : ℂ → X → ℂ) : 0 < r → IsOpen V →
    Metric.closedBall s₀ r ⊆ V → DifferentiableOn ℂ χ V → (∀ g, DifferentiableOn ℂ (Φ · g) V) →
    ∀ j : ℤ, ∃ c : ℕ → ℂ, ∀ g, circleIntegral (fun z => (z - s₀) ^ j * (χ z * Φ z g)) s₀ r =
      ∑ i ∈ Finset.range (-j).toNat, c i * circleIntegral (fun z => (z - s₀) ^ (j + i) * Φ z g) s₀ r :=
  fun hr hV hball hχ hΦ j =>
    circleIntegral_zpow_mul_holo_sum s₀ r V Φ hr hV hball hΦ _ χ j hχ rfl

end GlobalTheory
