import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem exponent_regular_of_natDegree_minpoly_pow : ∀ (F : Type) [Field F] [Finite F] (d k : ℕ) (ζ : AlgebraicClosure F), 0 < d → orderOf ζ = Nat.card F ^ d - 1 → (minpoly F (ζ ^ k)).natDegree = d → ∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1] := by
  intro F _ _ d k ζ _ hord hdeg i hi hid hmod
  have h1 : ζ ^ (Nat.card F ^ d - 1) = 1 := by
    rw [← hord]; exact pow_orderOf_eq_one ζ
  have h2 : (ζ ^ k) ^ (Nat.card F ^ i) = ζ ^ k := by
    rw [← pow_mul]; exact pow_eq_pow_of_modEq hmod h1
  have hint : IsIntegral F (ζ ^ k) := Algebra.IsIntegral.isIntegral _
  have hdvd : minpoly F (ζ ^ k) ∣ (X ^ (Nat.card F ^ i) - X : F[X]) := by
    apply minpoly.dvd
    simp only [map_sub, map_pow, aeval_X, h2, sub_self]
  have h3 := (minpoly.irreducible hint).natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hdvd
  rw [hdeg] at h3
  exact absurd (Nat.le_of_dvd hi h3) (not_le.mpr hid)

end GlobalTheory.CuspGL
