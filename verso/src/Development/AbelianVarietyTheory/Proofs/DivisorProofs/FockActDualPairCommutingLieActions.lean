import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockQuadraticActionMapLieBracketStatement
open Formalism.BasicNotions.TH
open scoped Kronecker

namespace GlobalTheory.FockPair

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fockAct1_eq_kron (p q r s : ℕ) (Y : Mat p q) :
    fockAct1 p q r s Y = omAct p q r s (Y ⊗ₖ (1 : Mat r s)) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fockAct2_eq_kron (p q r s : ℕ) (Z : Mat r s) :
    fockAct2 p q r s Z = omAct p q r s ((1 : Mat p q) ⊗ₖ Z) := rfl

/- English proof (translation)
Introduce `p q r s`. Use `⟨fun X Y => ?_, fun X Y => ?_, fun Y Z => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub]`. Simplify using `only [fockAct1_eq_kron]`. Rewrite using `[← GlobalTheory.T.fockQuadraticAction_map_lie_bracket, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, map_sub]`.

Rewrite using `[map_sub]`. Simplify using `only [fockAct2_eq_kron]`. Rewrite using `[← GlobalTheory.T.fockQuadraticAction_map_lie_bracket, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, map_sub]`. Rewrite using `[← sub_eq_zero, fockAct1_eq_kron, fockAct2_eq_kron, ← GlobalTheory.T.fockQuadraticAction_map_lie_bracket, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]`. Simplify using the standard rewrite rules.
-/
theorem pair_lie_commute : ∀ (p q r s : ℕ), IsLieAct (fockAct1 p q r s) ∧
    IsLieAct (fockAct2 p q r s) ∧ ∀ (Y : Mat p q) (Z : Mat r s),
      fockAct1 p q r s Y * fockAct2 p q r s Z = fockAct2 p q r s Z * fockAct1 p q r s Y := by
  intro p q r s
  refine ⟨fun X Y => ?_, fun X Y => ?_, fun Y Z => ?_⟩
  · rw [map_sub]
    simp only [fockAct1_eq_kron]
    rw [← GlobalTheory.T.fockQuadraticAction_map_lie_bracket, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      map_sub]
  · rw [map_sub]
    simp only [fockAct2_eq_kron]
    rw [← GlobalTheory.T.fockQuadraticAction_map_lie_bracket, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      map_sub]
  · rw [← sub_eq_zero, fockAct1_eq_kron, fockAct2_eq_kron, ← GlobalTheory.T.fockQuadraticAction_map_lie_bracket,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp

end GlobalTheory.FockPair
