import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicTemperedDistPoisson
import Mathlib
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IntComb.dirac_comb_unique` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPeriodicTemperedDistPoisson.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.periodic_tempered_dist_poisson : ∀ (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ),
    (∀ k : Fin n → ℤ, ∀ f f' : SchwartzMap (Fin n → ℝ) ℂ, (∀ x, f' x = f (x + fun i => (k i : ℝ))) → T f' = T f) →
    (∀ m : Fin n → ℤ, ∀ f f' : SchwartzMap (Fin n → ℝ) ℂ,
      (∀ x, f' x = Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (m i : ℝ) * x i : ℝ) : ℂ)) * f x) → T f' = T f) →
    ∃ c : ℂ, ∀ f : SchwartzMap (Fin n → ℝ) ℂ, T f = c * ∑' k : Fin n → ℤ, f (fun i => (k i : ℝ)) := by
  first | exact @GlobalTheory.IntComb.dirac_comb_unique | exact GlobalTheory.IntComb.dirac_comb_unique | (intros; apply GlobalTheory.IntComb.dirac_comb_unique <;> assumption)
