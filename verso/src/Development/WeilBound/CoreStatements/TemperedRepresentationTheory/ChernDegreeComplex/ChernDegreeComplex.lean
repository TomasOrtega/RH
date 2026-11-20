import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPresentationIndepStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPolynomialGrowthStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntersectionNumberPolynomialStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperplaneTwistGloballyGeneratedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralEqIntersectionStatement

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel

namespace PositivityTheory.Tls2.Chern2

/- English proof (translation)
Introduce `Y Δ L r hr φ hφ`. Use `⟨GlobalTheory.Published.ChernDegreeComplexModel.integrable Y φ hφ, ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `ProjSpace.exists_mem_chart ℂ Y.N (Y.ι (genericPoint ↥Y.X))`. Take `⟨M₀, hM₀⟩` from `Filter.eventually_atTop.mp (GlobalTheory.T.hyperplane_twist_globally_generated Y i hi 0)`. Take `⟨L₀, r₀, n₀, b₀, hL₀, hp₀, hb₀⟩` from `hM₀ (M₀ + 1) (by omega)`.

Establish `hφ₀` using `Weight.isCInf_fsBasis (p := Y.str) (σ := RingHom.id ℂ) hL₀ b₀ hb₀ 1 (by simp)`. Take `⟨P, -, hP⟩` from `GlobalTheory.T.chern_integral_polynomial_growth Y Δ _ L L₀ r r₀ hr hp₀ φ _ hφ hφ₀`. Take `⟨Q, hQ⟩` from `GlobalTheory.T.intersection_number_polynomial Y Δ (0 + (M₀ + 1) • Y.hyp hi)`. Take `⟨M, hM⟩` from `Filter.eventually_atTop.mp (GlobalTheory.T.hyperplane_twist_globally_generated Y i hi Δ)`. Establish `key : ∀ m : ℕ, M ≤ m → P.eval (m : ℝ) = Q.eval (m : ℝ)`.

Introduce `m hm`. Take `⟨L', r', ψ, hp', hψ, hψeq⟩` from `hP m`. Establish `hmm : M ≤ m * (M₀ + 1)` using `le_trans hm (Nat.le_mul_of_pos_right m (Nat.succ_pos M₀))`. Take `⟨L₁, r₁, n₁, b₁, hL₁, hp₁, hb₁⟩` from `hM (m * (M₀ + 1)) hmm`. Establish `hΔ : Δ + (m * (M₀ + 1)) • Y.hyp hi = Δ + m • (0 + (M₀ + 1) • Y.hyp hi)`.

Rewrite using `[zero_add, mul_smul]`. Rewrite `hp₁` using `[hΔ]`. Rewrite using `[← hψeq, ← hQ m, ← GlobalTheory.T.chern_integral_eq_intersection Y _ L₁ r₁ hL₁ n₁ b₁ hb₁ hp₁]`. Conclude with `GlobalTheory.T.chern_integral_presentation_indep Y _ L' L₁ r' r₁ hp' hp₁ ψ _ hψ (Weight.isCInf_fsBasis _ _ _ _ _)`. Establish `hPQ : P = Q`.

Apply `Polynomial.eq_of_infinite_eval_eq` to reduce the goal to its premises. Use `Set.Infinite.mono ?_ ((Set.Ici_infinite M).image Nat.cast_injective.injOn)` and prove the remaining obligations. Introduce and unpack `x ⟨m, hm, rfl⟩`. Conclude with `key m hm`. Take `⟨L', r', ψ, hp', hψ, hψeq⟩` from `hP 0`.

Establish `h0 : Δ + (0 : ℕ) • (0 + (M₀ + 1) • Y.hyp hi) = Δ` using `by simp`. Rewrite `hp'` using `[h0]`. Establish `hQ0` using `hQ 0`. Rewrite `hQ0` using `[h0]`. Rewrite using `[hQ0, ← hPQ, ← hψeq]`.

Conclude with `GlobalTheory.T.chern_integral_presentation_indep Y Δ L L' r r' hr hp' φ ψ hφ hψ`.
-/
theorem chernDegreeComplex : GlobalTheory.Published.ChernDegreeComplex := by
  intro Y Δ L r hr φ hφ
  refine ⟨GlobalTheory.Published.ChernDegreeComplexModel.integrable Y φ hφ, ?_⟩
  obtain ⟨i, hi⟩ := ProjSpace.exists_mem_chart ℂ Y.N (Y.ι (genericPoint ↥Y.X))
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp (GlobalTheory.T.hyperplane_twist_globally_generated Y i hi 0)
  obtain ⟨L₀, r₀, n₀, b₀, hL₀, hp₀, hb₀⟩ := hM₀ (M₀ + 1) (by omega)
  have hφ₀ := Weight.isCInf_fsBasis (p := Y.str) (σ := RingHom.id ℂ) hL₀ b₀ hb₀ 1 (by simp)
  obtain ⟨P, -, hP⟩ := GlobalTheory.T.chern_integral_polynomial_growth Y Δ _ L L₀ r r₀ hr hp₀ φ _ hφ hφ₀
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.intersection_number_polynomial Y Δ (0 + (M₀ + 1) • Y.hyp hi)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (GlobalTheory.T.hyperplane_twist_globally_generated Y i hi Δ)
  have key : ∀ m : ℕ, M ≤ m → P.eval (m : ℝ) = Q.eval (m : ℝ) := by
    intro m hm
    obtain ⟨L', r', ψ, hp', hψ, hψeq⟩ := hP m
    have hmm : M ≤ m * (M₀ + 1) := le_trans hm (Nat.le_mul_of_pos_right m (Nat.succ_pos M₀))
    obtain ⟨L₁, r₁, n₁, b₁, hL₁, hp₁, hb₁⟩ := hM (m * (M₀ + 1)) hmm
    have hΔ : Δ + (m * (M₀ + 1)) • Y.hyp hi = Δ + m • (0 + (M₀ + 1) • Y.hyp hi) := by
      rw [zero_add, mul_smul]
    rw [hΔ] at hp₁
    rw [← hψeq, ← hQ m, ← GlobalTheory.T.chern_integral_eq_intersection Y _ L₁ r₁ hL₁ n₁ b₁ hb₁ hp₁]
    exact GlobalTheory.T.chern_integral_presentation_indep Y _ L' L₁ r' r₁ hp' hp₁ ψ _ hψ
      (Weight.isCInf_fsBasis _ _ _ _ _)
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono ?_ ((Set.Ici_infinite M).image Nat.cast_injective.injOn)
    rintro x ⟨m, hm, rfl⟩
    exact key m hm
  obtain ⟨L', r', ψ, hp', hψ, hψeq⟩ := hP 0
  have h0 : Δ + (0 : ℕ) • (0 + (M₀ + 1) • Y.hyp hi) = Δ := by simp
  rw [h0] at hp'
  have hQ0 := hQ 0
  rw [h0] at hQ0
  rw [hQ0, ← hPQ, ← hψeq]
  exact GlobalTheory.T.chern_integral_presentation_indep Y Δ L L' r r' hr hp' φ ψ hφ hψ

end PositivityTheory.Tls2.Chern2
