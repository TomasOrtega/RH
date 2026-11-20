import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.QuotientLatticeByIsotropicSubmoduleStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.RealFormIndep

/- English proof (translation)
Rewrite using `[star_sum, mulVec_sum, sum_dotProduct]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[dotProduct_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[star_smul, star_trivial, mulVec_smul, smul_dotProduct, dotProduct_smul, Complex.real_smul, Complex.real_smul, Complex.ofReal_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pairing_real_combination {g k : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (u : Fin k → Fin g → ℂ) (a b : Fin k → ℝ) :
    (∑ i, a i • u i) ⬝ᵥ Hm *ᵥ star (∑ j, b j • u j) =
      ∑ i, ∑ j, ((a i * b j : ℝ) : ℂ) * (u i ⬝ᵥ Hm *ᵥ star (u j)) := by
  rw [star_sum, mulVec_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_smul, star_trivial, mulVec_smul, smul_dotProduct, dotProduct_smul, Complex.real_smul,
    Complex.real_smul, Complex.ofReal_mul]
  ring

/- English proof (translation)
Introduce `g k Hm hpos u hu hreal`. Rewrite `hu`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `c hc`. Establish `hR : ∀ a b : Fin k → ℝ, ((∑ i, a i • u i) ⬝ᵥ Hm *ᵥ star (∑ j, b j • u j)).im = 0`. Introduce `a b`.

Rewrite using `[pairing_real_combination]`. Simplify using `[Complex.im_sum, hreal]`. Establish `hxy : (∑ i, (c i).re • u i) + Complex.I • (∑ i, (c i).im • u i) = 0`. Rewrite using `[← hc]`. Use extensionality with `t`.

Simplify using `only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [← Complex.re_add_im (c i)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hx : (∑ i, (c i).re • u i) = -(Complex.I • ∑ i, (c i).im • u i)` using `eq_neg_of_add_eq_zero_left hxy`.

Establish `hyy : ((∑ i, (c i).im • u i) ⬝ᵥ Hm *ᵥ star (∑ j, (c j).im • u j)).re = 0`. Establish `h` using `hR (fun i => (c i).re) (fun j => (c j).im)`. Rewrite `h` using `[hx, neg_dotProduct, smul_dotProduct, smul_eq_mul]`. Simplify using `using h`. Establish `hy0 : (∑ i, (c i).im • u i) = 0`.

Assume the negation of the conclusion as `hne`. Use `hpos _ hne` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hx0 : (∑ i, (c i).re • u i) = 0`. Rewrite using `[hx, hy0, smul_zero, neg_zero]`.

Introduce `i`. Establish `h1` using `hu (fun i => (c i).re) hx0 i`. Establish `h2` using `hu (fun i => (c i).im) hy0 i`. Conclude with `Complex.ext (by simpa using h1) (by simpa using h2)`.
-/
theorem linearIndependent_complex_of_real_form :
    ∀ (g k : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ),
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) →
      ∀ u : Fin k → Fin g → ℂ, LinearIndependent ℝ u →
        (∀ i j, (u i ⬝ᵥ Hm *ᵥ star (u j)).im = 0) → LinearIndependent ℂ u := by
  intro g k Hm hpos u hu hreal
  rw [Fintype.linearIndependent_iff] at hu ⊢
  intro c hc
  have hR : ∀ a b : Fin k → ℝ, ((∑ i, a i • u i) ⬝ᵥ Hm *ᵥ star (∑ j, b j • u j)).im = 0 := by
    intro a b
    rw [pairing_real_combination]
    simp [Complex.im_sum, hreal]
  have hxy : (∑ i, (c i).re • u i) + Complex.I • (∑ i, (c i).im • u i) = 0 := by
    rw [← hc]
    ext t
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [← Complex.re_add_im (c i)]
    ring
  have hx : (∑ i, (c i).re • u i) = -(Complex.I • ∑ i, (c i).im • u i) := eq_neg_of_add_eq_zero_left hxy
  have hyy : ((∑ i, (c i).im • u i) ⬝ᵥ Hm *ᵥ star (∑ j, (c j).im • u j)).re = 0 := by
    have h := hR (fun i => (c i).re) (fun j => (c j).im)
    rw [hx, neg_dotProduct, smul_dotProduct, smul_eq_mul] at h
    simpa using h
  have hy0 : (∑ i, (c i).im • u i) = 0 := by
    by_contra hne
    have := hpos _ hne
    linarith
  have hx0 : (∑ i, (c i).re • u i) = 0 := by
    rw [hx, hy0, smul_zero, neg_zero]
  intro i
  have h1 := hu (fun i => (c i).re) hx0 i
  have h2 := hu (fun i => (c i).im) hy0 i
  exact Complex.ext (by simpa using h1) (by simpa using h2)

end GlobalTheory.CompanionTheory.Ar.RealFormIndep
