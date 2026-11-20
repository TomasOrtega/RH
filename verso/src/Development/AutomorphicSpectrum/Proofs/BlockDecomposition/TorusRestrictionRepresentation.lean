import Mathlib
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

noncomputable section

open Finset Matrix

namespace GlobalTheory.CompanionTheory.RgTorus

open PositivityTheory.RgDs.K

variable {n : ℕ}

/- English proof (translation)
Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Simplify using `only [tor, Matrix.diagonal_mul_diagonal, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]`. Conclude with `Matrix.diagonal_one`.
-/
theorem tor_inv (θ : Fin n → ℝ) :
    (tor θ)⁻¹ = Matrix.diagonal fun a => Complex.exp (-((θ a : ℂ) * Complex.I)) := by
  apply Matrix.inv_eq_left_inv
  simp only [tor, Matrix.diagonal_mul_diagonal, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  exact Matrix.diagonal_one

/- English proof (translation)
Unfold `adC`. Rewrite using `[tor_inv]`. Distinguish the cases in `h1 : q.1 = p.1`. Establish `h2 : p.2 ≠ q.2` using `fun h2 => h (Prod.ext h1.symm h2)`. Rewrite using `[Matrix.diagonal_apply_ne _ h2, mul_zero]`.

Unfold `tor`. Rewrite using `[Matrix.diagonal_apply_ne _ h1, zero_mul]`.
-/
theorem adC_tor_ne (θ : Fin n → ℝ) {p q : Fin n × Fin n} (h : p ≠ q) : adC (tor θ) p q = 0 := by
  unfold adC
  rw [tor_inv]
  by_cases h1 : q.1 = p.1
  · have h2 : p.2 ≠ q.2 := fun h2 => h (Prod.ext h1.symm h2)
    rw [Matrix.diagonal_apply_ne _ h2, mul_zero]
  · unfold tor
    rw [Matrix.diagonal_apply_ne _ h1, zero_mul]

/- English proof (translation)
Unfold `adC`. Rewrite using `[tor_inv]`. Unfold `tor`. Rewrite using `[Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, ← Complex.exp_add]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem adC_tor_self (θ : Fin n → ℝ) (p : Fin n × Fin n) :
    adC (tor θ) p p = Complex.exp (((θ p.1 - θ p.2 : ℝ) : ℂ) * Complex.I) := by
  unfold adC
  rw [tor_inv]
  unfold tor
  rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/- English proof (translation)
Introduce `n ε Λ T m θ k hk a x`. Unfold `rhoA`. Rewrite using `[hk, Finset.sum_eq_single x.2]`. Use `congr 1`. Simplify using `only [adC_tor_self]`.

Rewrite using `[← Complex.exp_sum]`. Use `congr 1`. Use `push_cast`. Rewrite using `[Finset.sum_mul]`. Introduce `w _ hw`.

Take `⟨i, hi⟩` from `Function.ne_iff.mp hw`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ i) (adC_tor_ne θ hi), zero_smul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem rhoTorus : RhoTorus := by
  intro n ε Λ T m θ k hk a x
  unfold rhoA
  rw [hk, Finset.sum_eq_single x.2]
  · congr 1
    simp only [adC_tor_self]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
  · intro w _ hw
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (adC_tor_ne θ hi), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end GlobalTheory.CompanionTheory.RgTorus
