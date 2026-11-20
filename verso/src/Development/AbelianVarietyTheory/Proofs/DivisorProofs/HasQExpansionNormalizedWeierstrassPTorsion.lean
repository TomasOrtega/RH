import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassDivisionValueQExpansionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassConstantQExpansionStatement

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.ExpP

/- English proof (translation)
Introduce `N _ x τ`. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Establish `h0 : wp N 0 τ = 0`. Simplify using `[wp, tors, PeriodPair.weierstrassP_zero]`.

Simplify using `only [cP, h0, if_true]`. Simplify using `using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)`. Establish `hB` using `GlobalTheory.T.weierstrass_division_value_q_expansion N x hx τ`. Establish `hG` using `GlobalTheory.T.weierstrass_constant_q_expansion N τ`. Establish `hd` using `hB.sub hG`.

Establish `hw : wp N x τ = wB N x τ - gN τ` using `by simp [wB]`. Establish `hf : (fun n : ℕ => cP N x n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) = fun n : ℕ => cB N x n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N) - cG N n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N)`. Use function extensionality and compare the values at `n`. Simplify using `[cP, hx, sub_mul]`. Rewrite using `[hw, hf]`.

Conclude with `hd`.
-/
theorem main : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), HasQ N (wp N x) (cP N x) := by
  intro N _ x τ
  by_cases hx : x = 0
  · subst hx
    have h0 : wp N 0 τ = 0 := by
      simp [wp, tors, PeriodPair.weierstrassP_zero]
    simp only [cP, h0, if_true]
    simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  · have hB := GlobalTheory.T.weierstrass_division_value_q_expansion N x hx τ
    have hG := GlobalTheory.T.weierstrass_constant_q_expansion N τ
    have hd := hB.sub hG
    have hw : wp N x τ = wB N x τ - gN τ := by simp [wB]
    have hf : (fun n : ℕ => cP N x n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) =
        fun n : ℕ => cB N x n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N) -
          cG N n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N) := by
      funext n
      simp [cP, hx, sub_mul]
    rw [hw, hf]
    exact hd

end GlobalTheory.WpFam.ExpP
