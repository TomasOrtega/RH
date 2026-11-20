import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplex

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

namespace GlobalTheory.Cyc.Decomp

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation.

A detailed English derivation is pending.
-/
theorem le_pow_n0_mul (l : ℕ) [hl : Fact l.Prime] (H : ℕ) : H ≤ l ^ (n0 l H) * (l - 1) := by
  unfold n0
  apply Nat.sInf_mem (s := {n | H ≤ l ^ n * (l - 1)})
  have h2 : 2 ≤ l := hl.out.two_le
  refine ⟨H, ?_⟩
  show H ≤ l ^ H * (l - 1)
  calc H ≤ l ^ H := (Nat.lt_pow_self (by omega : 1 < l)).le
    _ ≤ l ^ H * (l - 1) := Nat.le_mul_of_pos_right _ (by omega)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.

Establish an intermediate fact. Establish an intermediate fact. Check the signs of the components of the expression. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_prime_eq_mul_primitiveRoot_sub_one_pow (l : ℕ) [hl : Fact l.Prime] (H : ℕ)
    (ζ : PadicComplex l) (hζ : IsPrimitiveRoot ζ (l ^ (1 + n0 l H))) :
    ∃ u : PadicComplex l, ‖u‖ ≤ 1 ∧ (l : PadicComplex l) = u * (ζ - 1) ^ H := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hH : (H : ℝ) ≤ (l : ℝ) ^ (n0 l H) * ((l : ℝ) - 1) := by
    have h := le_pow_n0_mul l H
    have h1 : 1 ≤ l := hl.out.one_lt.le
    calc (H : ℝ) ≤ ((l ^ n0 l H * (l - 1) : ℕ) : ℝ) := by exact_mod_cast h
      _ = (l : ℝ) ^ (n0 l H) * ((l : ℝ) - 1) := by push_cast [Nat.cast_sub h1]; ring
  have hDpos : 0 < (l : ℝ) ^ (n0 l H) * ((l : ℝ) - 1) := by
    have : (0 : ℝ) < (l : ℝ) - 1 := by linarith
    positivity
  have hnorm := norm_primitiveRoot_sub_one l (1 + n0 l H) (by omega) ζ hζ
  rw [Nat.add_sub_cancel_left] at hnorm
  have hpos : 0 < ‖ζ - 1‖ := by rw [hnorm]; positivity
  have hne : ζ - 1 ≠ 0 := norm_pos_iff.mp hpos
  refine ⟨(l : PadicComplex l) / (ζ - 1) ^ H, ?_, (div_mul_cancel₀ _ (pow_ne_zero H hne)).symm⟩
  rw [norm_div, norm_pow, norm_natCast_prime_padicComplex, div_le_one (pow_pos hpos H), hnorm,
    ← Real.rpow_mul_natCast (by positivity), ← Real.rpow_neg_one]
  apply Real.rpow_le_rpow_of_exponent_le hl1.le
  rw [neg_div, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, one_mul, div_le_one hDpos]
  exact hH

end GlobalTheory.Cyc.Decomp
