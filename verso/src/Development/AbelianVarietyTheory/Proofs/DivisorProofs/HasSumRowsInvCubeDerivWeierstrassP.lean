import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

/- English proof (translation)
Establish `h` using `((tauPair τ).hasSum_derivWeierstrassP z).mul_left (-(1 / 2))`. Set `e : ℤ × ℤ ≃ (tauPair τ).lattice` to `(Equiv.neg (ℤ × ℤ)).trans (tauPair τ).latticeEquivProd.symm.toEquiv`. Rewrite `h` using `[← e.hasSum_iff]`. Establish `key : (fun p : ℤ × ℤ => 1 / (z + p.1 * (τ : ℂ) + p.2) ^ 3) = (fun i : (tauPair τ).lattice => -(1 / 2) * (-2 / (z - (i : ℂ)) ^ 3)) ∘ e` using `?_`. Rewrite using `[key]`.

Conclude with `h`. Use function extensionality and compare the values at `p`. Establish `he : ((e p : (tauPair τ).lattice) : ℂ) = -(p.1 * (τ : ℂ) + p.2)`. Express the relevant statement in the definitionally equal form `((tauPair τ).latticeEquivProd.symm (-p)).1 = _`. Rewrite using `[PeriodPair.latticeEquiv_symm_apply]`.

Simplify using `[tauPair]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Function.comp, he]`. Rewrite using `[show z - -(p.1 * (τ : ℂ) + p.2) = z + p.1 * (τ : ℂ) + p.2 by ring]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasSum_prod_derivWeierstrassP (τ : ℍ) (z : ℂ) :
    HasSum (fun p : ℤ × ℤ => 1 / (z + p.1 * (τ : ℂ) + p.2) ^ 3)
      (-(1 / 2) * (tauPair τ).derivWeierstrassP z) := by
  have h := ((tauPair τ).hasSum_derivWeierstrassP z).mul_left (-(1 / 2))
  let e : ℤ × ℤ ≃ (tauPair τ).lattice :=
    (Equiv.neg (ℤ × ℤ)).trans (tauPair τ).latticeEquivProd.symm.toEquiv
  rw [← e.hasSum_iff] at h
  have key : (fun p : ℤ × ℤ => 1 / (z + p.1 * (τ : ℂ) + p.2) ^ 3) =
      (fun i : (tauPair τ).lattice => -(1 / 2) * (-2 / (z - (i : ℂ)) ^ 3)) ∘ e := ?_
  · rw [key]; exact h
  funext p
  have he : ((e p : (tauPair τ).lattice) : ℂ) = -(p.1 * (τ : ℂ) + p.2) := by
    change ((tauPair τ).latticeEquivProd.symm (-p)).1 = _
    rw [PeriodPair.latticeEquiv_symm_apply]
    simp [tauPair]
    ring
  simp only [Function.comp, he]
  rw [show z - -(p.1 * (τ : ℂ) + p.2) = z + p.1 * (τ : ℂ) + p.2 by ring]
  ring

/- English proof (translation)
Introduce `τ z`. Establish `h` using `hasSum_prod_derivWeierstrassP τ z`. Conclude with `h.prod_fiberwise fun n => (h.summable.prod_factor n).hasSum`.
-/
theorem hasSum_rows_derivWeierstrassP : ∀ (τ : ℍ) (z : ℂ), HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * (τ : ℂ) + m) ^ 3) (-(1 / 2) * (tauPair τ).derivWeierstrassP z) := by
  intro τ z
  have h := hasSum_prod_derivWeierstrassP τ z
  exact h.prod_fiberwise fun n => (h.summable.prod_factor n).hasSum

end GlobalTheory.WpFam
