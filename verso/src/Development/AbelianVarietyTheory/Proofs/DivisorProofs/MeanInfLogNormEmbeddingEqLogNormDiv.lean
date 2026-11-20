import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Formalism.PairingDivisors.StatementH
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem meanInf_log_norm_embedding (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (a : K) (ha : a ≠ 0) :
    Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.log ‖v.embedding a‖) = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| / Module.finrank ℚ K := by
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  have hprod := InfinitePlace.prod_eq_abs_norm (K := K) a
  have hmult : ∀ v : InfinitePlace K, v.mult = 2 := fun v => by
    rw [InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v))]
  have hpos : ∀ v : InfinitePlace K, 0 < v a := fun v => by
    rw [InfinitePlace.pos_iff]; exact ha
  have hsum : Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∑ v : InfinitePlace K, 2 * Real.log (v a) := by
    rw [show |((Algebra.norm ℚ a : ℚ) : ℝ)| = ((|Algebra.norm ℚ a| : ℚ) : ℝ) by push_cast; rfl, ← hprod, Real.log_prod]
    · refine Finset.sum_congr rfl fun v _ => ?_
      rw [hmult, Real.log_pow]; push_cast; ring
    · intro v _; exact pow_ne_zero _ (hpos v).ne'
  have he : ∀ v : InfinitePlace K, ‖v.embedding a‖ = v a := fun v => InfinitePlace.norm_embedding_eq v a
  simp only [he]
  rw [hsum, ← Finset.mul_sum]
  ring

end GlobalTheory
