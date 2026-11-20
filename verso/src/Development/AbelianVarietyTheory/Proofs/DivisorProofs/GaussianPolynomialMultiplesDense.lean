import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveQuadraticLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialMultipleInSubmoduleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianPolynomialDensityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseCompactSupportSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseAnalyticGrowthSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseSchwartzMultipleNonvanishingStatement

open SchwartzMap

namespace GlobalTheory.GaussDense

/- English proof (translation)
Introduce `V _ _ _ Q hQ g hg N hgN hmul`. Take `⟨c, hc, hcQ⟩` from `GlobalTheory.T.positive_quadratic_lower_bound V Q hQ`. Establish `hpoly` using `GlobalTheory.T.polynomial_multiple_in_submodule V N g hgN hmul`. Establish `hgt : (⇑g).HasTemperateGrowth` using `g.hasTemperateGrowth`. Set `L : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ` to `SchwartzMap.smulLeftCLM ℂ (⇑g)`.

Establish `hL : ∀ ψ x, L ψ x = g x * ψ x` using `fun ψ x => by`. Simplify using `only [L, SchwartzMap.smulLeftCLM_apply_apply hgt, smul_eq_mul]`. Establish `hclosed : IsClosed (L ⁻¹' (N.topologicalClosure : Set (SchwartzMap V ℂ)))` using `N.isClosed_topologicalClosure.preimage L.continuous`. Establish `hsub : {ψ : SchwartzMap V ℂ | ∃ A ρ : ℝ, ∀ (j : ℕ) (y : V), ‖iteratedFDeriv ℝ j ψ y‖ ≤ A * ρ ^ j} ⊆ L ⁻¹' (N.topologicalClosure : Set (SchwartzMap V ℂ))`. Introduce and unpack `ψ ⟨A, ρ, hb⟩`.

Conclude with `GlobalTheory.T.gaussian_polynomial_density V Q c hc hcQ g hg N hpoly ψ A ρ hb (L ψ) (fun x => by rw [hL, mul_comm])`. Establish `hall : ∀ ψ, L ψ ∈ N.topologicalClosure`. Introduce `ψ`. Establish `h1` using `closure_minimal hsub hclosed`. Rewrite `h1` using `[(GlobalTheory.T.dense_analytic_growth_schwartz GlobalTheory.T.dense_compact_support_schwartz V).closure_eq]`.

Conclude with `h1 (Set.mem_univ ψ)`. Establish `hE : {F : SchwartzMap V ℂ | ∃ ψ : SchwartzMap V ℂ, ∀ x, F x = ψ x * g x} ⊆ (N.topologicalClosure : Set (SchwartzMap V ℂ))`. Introduce and unpack `F ⟨ψ, hψ⟩`. Establish `: F = L ψ` using `by ext x; rw [hψ, hL, mul_comm]`. Rewrite using `[this]`.

Conclude with `hall ψ`. Establish `hD` using `(GlobalTheory.T.dense_schwartz_multiple_nonvanishing V g (fun x => by rw [hg]; exact Complex.exp_ne_zero _) (GlobalTheory.T.dense_compact_support_schwartz V)).mono hE`. Rewrite `hD` using `[Submodule.topologicalClosure_coe]`. Conclude with `hD.of_closure`.
-/
theorem gauss_dense : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℂ), (∀ x, x ≠ 0 → 0 < (Q x x).re) →
    ∀ g : SchwartzMap V ℂ, (∀ x, g x = Complex.exp (-(Q x x))) →
    ∀ N : Submodule ℂ (SchwartzMap V ℂ), g ∈ N →
    (∀ f ∈ N, ∀ ℓ : V →ₗ[ℝ] ℝ, ∃ f₁ ∈ N, ∀ x, f₁ x = (ℓ x : ℂ) * f x) →
    Dense (N : Set (SchwartzMap V ℂ)) := by
  intro V _ _ _ Q hQ g hg N hgN hmul
  obtain ⟨c, hc, hcQ⟩ := GlobalTheory.T.positive_quadratic_lower_bound V Q hQ
  have hpoly := GlobalTheory.T.polynomial_multiple_in_submodule V N g hgN hmul
  have hgt : (⇑g).HasTemperateGrowth := g.hasTemperateGrowth
  let L : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ := SchwartzMap.smulLeftCLM ℂ (⇑g)
  have hL : ∀ ψ x, L ψ x = g x * ψ x := fun ψ x => by
    simp only [L, SchwartzMap.smulLeftCLM_apply_apply hgt, smul_eq_mul]
  have hclosed : IsClosed (L ⁻¹' (N.topologicalClosure : Set (SchwartzMap V ℂ))) :=
    N.isClosed_topologicalClosure.preimage L.continuous
  have hsub : {ψ : SchwartzMap V ℂ | ∃ A ρ : ℝ, ∀ (j : ℕ) (y : V), ‖iteratedFDeriv ℝ j ψ y‖ ≤ A * ρ ^ j} ⊆
      L ⁻¹' (N.topologicalClosure : Set (SchwartzMap V ℂ)) := by
    rintro ψ ⟨A, ρ, hb⟩
    exact GlobalTheory.T.gaussian_polynomial_density V Q c hc hcQ g hg N hpoly ψ A ρ hb (L ψ) (fun x => by rw [hL, mul_comm])
  have hall : ∀ ψ, L ψ ∈ N.topologicalClosure := by
    intro ψ
    have h1 := closure_minimal hsub hclosed
    rw [(GlobalTheory.T.dense_analytic_growth_schwartz GlobalTheory.T.dense_compact_support_schwartz V).closure_eq] at h1
    exact h1 (Set.mem_univ ψ)
  have hE : {F : SchwartzMap V ℂ | ∃ ψ : SchwartzMap V ℂ, ∀ x, F x = ψ x * g x} ⊆
      (N.topologicalClosure : Set (SchwartzMap V ℂ)) := by
    rintro F ⟨ψ, hψ⟩
    have : F = L ψ := by ext x; rw [hψ, hL, mul_comm]
    rw [this]; exact hall ψ
  have hD := (GlobalTheory.T.dense_schwartz_multiple_nonvanishing V g (fun x => by rw [hg]; exact Complex.exp_ne_zero _) (GlobalTheory.T.dense_compact_support_schwartz V)).mono hE
  rw [Submodule.topologicalClosure_coe] at hD
  exact hD.of_closure

end GlobalTheory.GaussDense
