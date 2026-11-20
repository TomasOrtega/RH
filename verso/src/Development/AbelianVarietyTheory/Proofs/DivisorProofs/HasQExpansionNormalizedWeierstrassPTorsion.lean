import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassDivisionValueQExpansionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassConstantQExpansionStatement

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.ExpP

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
